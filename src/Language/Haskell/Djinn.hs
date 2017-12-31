{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TemplateHaskell     #-}

-----------------------------------------------------------------------------
-- |
-- Module      :  Language.Haskell.Djinn
-- License     :  BSD-style (see the accompanying LICENSE file)
--
-- Maintainer  :  claudiusmaximus@goto10.org
-- Stability   :  experimental
-- Portability :  non-portable (template-haskell)
--
-- Djinn uses a theorem prover for intuitionistic propositional logic to
-- generate a Haskell expression when given a type. Djinn-TH uses Template
-- Haskell to turn this expression into executable code.
--
-- Based mostly on <http://hackage.haskell.org/package/djinn>.
--
-- Using Language.Haskell.Djinn generally requires:
--
-- @&#x7B;-&#x23; LANGUAGE TemplateHaskell, ScopedTypeVariables &#x23;-&#x7D;@
--
-----------------------------------------------------------------------------
--
-- Modified to use TemplateHaskell by Claude Heiland-Allen, 2010
--
-- Copyright (c) 2005 Lennart Augustsson
-- See LICENSE for licensing details.
--
module Language.Haskell.Djinn
  ( djinn -- :: Q Type -> Q Exp
  , djinns -- :: Q Type -> Q Exp
  , djinnD -- :: String -> Q Type -> Q [Dec]
  , djinnsD -- :: String -> Q Type -> Q [Dec]
  , djinnsLim
  ) where

import           Control.Monad
import           Data.List                     (nub, sortBy)
import           Data.Ord                      (comparing)
import           Data.Ratio                    ((%))
import           Data.Set                      (Set, empty, singleton, toList,
                                                union)
import           Language.Haskell.TH           hiding (cxt)

import           Language.Haskell.Djinn.HTypes
import           Language.Haskell.Djinn.LJT

getConTs :: Type -> Set Name
getConTs (ForallT _ _ t) = getConTs t
getConTs (ConT name    ) = singleton name
getConTs (AppT t1 t2   ) = getConTs t1 `union` getConTs t2
getConTs (TupleT n     ) = singleton (tupleTypeName n)
getConTs _               = empty

hType :: Type -> HType
hType (TupleT 0) = HTTuple []
hType (TupleT 1) = error $ "djinn: 1-tuple should not exist"
-- FIXME kludge for now to handle small tuples...
-- FIXME kludge to handle GHC's tuple stuff
hType (AppT (AppT ArrowT t1) t2) = HTArrow (hType t1) (hType t2)
hType (AppT (AppT (TupleT 2) t1) t2) = HTTuple (map hType [t1, t2])
hType (AppT (AppT (ConT c) t1) t2) | c == tupleTypeName 2 = HTTuple
  (map hType [t1, t2])
hType (AppT (AppT (AppT (TupleT 3) t1) t2) t3) =
  HTTuple (map hType [t1, t2, t3])
hType (AppT (AppT (AppT (ConT c) t1) t2) t3) | c == tupleTypeName 3 =
  HTTuple (map hType [t1, t2, t3])
hType (AppT (AppT (AppT (AppT (TupleT 4) t1) t2) t3) t4) =
  HTTuple (map hType [t1, t2, t3, t4])
hType (AppT (AppT (AppT (AppT (ConT c) t1) t2) t3) t4) | c == tupleTypeName 4 =
  HTTuple (map hType [t1, t2, t3, t4])
hType (AppT (AppT (AppT (AppT (AppT (TupleT 5) t1) t2) t3) t4) t5) =
  HTTuple (map hType [t1, t2, t3, t4, t5])
hType (AppT (AppT (AppT (AppT (AppT (ConT c) t1) t2) t3) t4) t5) | c
  == tupleTypeName 5 = HTTuple (map hType [t1, t2, t3, t4, t5])
hType (TupleT n) | n > 5 =
  error $ "djinn: " ++ show n ++ "-tuple not yet supported (max 5)"
hType (AppT t1 t2   ) = HTApp (hType t1) (hType t2)
hType (ForallT _ _ t) = hType t
hType (VarT v       ) = HTVar v
hType (ConT n       ) = HTCon n
hType t               = error $ "djinn: unimplemented in hType: " ++ pprint t

-- two mutually recursive functions chase down all data/type defs
environment :: Type -> Q HEnvironment
environment = fmap concat . mapM environment1 . toList . getConTs

environment1 :: Name -> Q HEnvironment
environment1 name = do
  info <- reify name
  case info of
    ClassI _dec _insts      -> fail "djinn: unexpected ClassI"
    ClassOpI   _n _t  _pn   -> fail "djinn: unexpected ClassOpI"
    PrimTyConI n  _ar _l    -> fail ("djinn: unexpected PrimTyConI " ++ show n)
    DataConI   _n _t  _pn   -> fail "djinn: unexpected DataConI"
    VarI       _n _t  _mdec -> fail "djinn: unexpected VarI"
    TyVarI _tvName _tvType  -> fail "djinn: unexpected TyVarI"
    TyConI dec              -> case dec of
      DataD _cxt dName dVars _kind dCtors _derivs -> do
        dTypes <- forM dCtors $ \(NormalC cName cFields) -> do
          let cTypes = map (hType . snd) cFields
          cEnv <- mapM (environment . snd) cFields
          pure ((cName, cTypes), cEnv)
        pure
          $ (dName, (map binderName dVars, HTUnion (map fst dTypes)))
          : (concat . concatMap snd $ dTypes)
      TySynD tName tVars tType -> do
        es <- environment tType
        pure $ (tName, (map binderName tVars, hType tType)) : es
      x -> fail $ "djinn: unexpected TyConI " ++ show x

binderName :: TyVarBndr -> Name
binderName (PlainTV n    ) = n
binderName (KindedTV n _k) = n

pat :: HPat -> Pat
pat (HPVar   s  ) = VarP s
pat (HPTuple ps ) = TupP (map pat ps)
pat (HPAt s p   ) = AsP s (pat p)
pat (HPCon c    ) = ConP c []
pat (HPApply p q) = let ConP c ps = pat p in ConP c (ps ++ [pat q])

expr :: HExpr -> Exp
expr (HELam   ps e) = LamE (map pat ps) (expr e)
expr (HEApply e  f) = AppE (expr e) (expr f)
expr (HECon   c   ) = ConE c
expr (HEVar   v   ) = VarE v
expr (HETuple es) = foldl AppE (ConE (tupleDataName (length es))) (map expr es)
expr (HECase e ms ) = CaseE (expr e) (map case1 ms)
  where case1 (p, f) = Match (pat p) (NormalB $ expr f) []

genDjinn' :: Bool -> Maybe String -> Type -> Q Exp
genDjinn' = genDjinn Nothing

genDjinn :: Maybe Int -> Bool -> Maybe String -> Type -> Q Exp
genDjinn lim multi mStr typ = do
  syns <- environment typ
  name <- case mStr of
    Nothing -> newName "djinn"
    Just s  -> pure $ mkName s
  let form = hTypeToFormula syns (hType typ)
  ps_ <-
    (map snd . sortBy (comparing fst) . map (f name)) `fmap` prove multi [] form
  let ps = case lim of
        Nothing -> nub ps_
        Just c  -> nub (take c ps_)
  if multi
    then pure $ ListE (map g ps)
    else case ps of
      ps'@(p:_:_) -> do
        reportDjWarning ps' name
        pure $ g p
      [p] -> pure $ g p
      []  -> do
        reportDjinnError name
        x <- newName "djinnError"
        pure $ LetE [ValD (VarP x) (NormalB (VarE x)) []] (VarE x)
 where
  reportDjWarning ps' n =
    reportWarning
      $  "djinn: "
      ++ show (length ps')
      ++ " options for: "
      ++ show n
      ++ " :: "
      ++ pprint typ
  reportDjinnError n =
    reportError $ "djinn: cannot realize: " ++ show n ++ " :: " ++ pprint typ
  f name p =
    let
      c   = termToHClause name p
      bvs = getBinderVars c
      r   = if null bvs
        then (0, 0)
        else (length (filter (== underscore) bvs) % length bvs, length bvs)
    in
      (r, c)
  g (HClause _ pats body) = let e = expr (HELam pats body) in wilderE e

underscore :: Name
underscore = mkName "_"

wilder :: Pat -> Pat
wilder l@(LitP _        )                   = l
wilder (  VarP n        ) | n == underscore = WildP
wilder (  TupP ps       )                   = TupP (map wilder ps)
wilder (  ConP n ps     )                   = ConP n (map wilder ps)
wilder (  InfixP p1 n p2)                   = InfixP (wilder p1) n (wilder p2)
wilder (  TildeP p      )                   = TildeP (wilder p)
wilder (AsP n p) | n == underscore = wilder p
                 | otherwise       = AsP n (wilder p)
--wilder (RecP n fs) = error $ "djinn: field patterns not yet implemented"
wilder (ListP ps) = ListP (map wilder ps)
wilder (SigP p t) = SigP (wilder p) t
wilder p          = p

wilderE :: Exp -> Exp
wilderE (AppE e f) = AppE (wilderE e) (wilderE f)
wilderE (InfixE me o mf) =
  InfixE (fmap wilderE me) (wilderE o) (fmap wilderE mf)
wilderE (LamE ps e  ) = LamE (map wilder ps) (wilderE e)
wilderE (TupE es    ) = TupE (map wilderE es)
wilderE (CondE e f g) = CondE (wilderE e) (wilderE f) (wilderE g)
wilderE (LetE  ds e ) = LetE (map wilderD ds) (wilderE e)
wilderE (CaseE e  ms) = CaseE (wilderE e) (map wilderM ms)
-- DoE [Stmt]                         -- { do { p <- e1; e2 }  }
-- CompE [Stmt]                       -- { [ (x,y) | x <- xs, y <- ys ] }
-- ArithSeqE Range                    -- { [ 1 ,2 .. 10 ] }
wilderE (ListE es   ) = ListE (map wilderE es)
wilderE (SigE e t   ) = SigE (wilderE e) t
-- RecConE Name [FieldExp]            -- { T { x = y, z = w } }
-- RecUpdE Exp [FieldExp]             -- { (f x) { z = w } }
wilderE e             = e

wilderM :: Match -> Match
wilderM (Match p b ds) = Match (wilder p) (wilderB b) (map wilderD ds)

wilderD :: Dec -> Dec
wilderD d = d -- error "djinn: no wilderD yet"

wilderB :: Body -> Body
wilderB b = b --error "djinn: no wilderD yet"

{- |
Generate an anonymous expression of the given type (if it is realizable).
-}
djinn
  :: Q Type -- ^ type
  -> Q Exp
djinn qtyp = do
  typ <- qtyp
  genDjinn' False Nothing typ

{- |
Generate a list of anonymous expressions of the given type (if it is realizable).
-}
djinnsLim
  :: Int
  -> Q Type -- ^ type
  -> Q Exp
djinnsLim c qtyp = do
  typ <- qtyp
  genDjinn (Just c) True Nothing typ

{- |
Generate a list of anonymous expressions of the given type (if it is realizable).
-}
djinns
  :: Q Type -- ^ type
  -> Q Exp
djinns qtyp = do
  typ <- qtyp
  genDjinn' True Nothing typ

{- |
Generate a named declaration with an accompanying type signature.  For example:

>   $(djinnD "maybeToEither" [t| forall a b . a ->  Maybe b ->  Either a b |])
>   main = print . map (maybeToEither "foo") $ [ Nothing, Just "bar" ]

might print @[Left \"foo\",Right \"bar\"]@.
-}
djinnD
  :: String -- ^ name
  -> Q Type -- ^ type
  -> Q [Dec]
djinnD str qtyp = do
  let name = mkName str
  typ  <- qtyp
  exp' <- genDjinn' False (Just str) typ
  pure [SigD name typ, FunD name [Clause [] (NormalB $ exp') []]]

{- |
Generate a named declaration with an accompanying type signature
for a list of possible realizations of a type.

>   $(djinnsD "picks" [t| forall a . (a, a) -> (a -> a) -> a |])
>   main = print [ p ("A","B") (++"C") | p <- picks ]

might print @[\"BC\",\"AC\",\"B\",\"A\"]@.

-}
djinnsD
  :: String -- ^ name
  -> Q Type -- ^ type
  -> Q [Dec]
djinnsD str qtyp = do
  let name = mkName str
  typ  <- qtyp
  exp' <- genDjinn' True (Just str) typ
  case typ of
    ForallT vs cxt t -> pure
      [ SigD name (ForallT vs cxt (AppT ListT t))
      , FunD name [Clause [] (NormalB $ exp') []]
      ]
    t ->
      pure [SigD name (AppT ListT t), FunD name [Clause [] (NormalB $ exp') []]]

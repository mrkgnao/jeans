module Language.Haskell.Djinn.HTypes
  ( HKind(..)
  , HType(..)
  , HSymbol
  , HEnvironment1
  , HEnvironment
  , hTypeToFormula
  , isHTUnion
  , getHTVars
  , substHT
  , HClause(..)
  , HPat(..)
  , HExpr(..)
  , termToHExpr
  , termToHClause
  , getBinderVars
  ) where

import           Language.Haskell.TH               (Name, mkName)

import           Data.Maybe
import           Control.Monad                     (zipWithM)
import           Data.List                         (union, (\\))
import           Language.Haskell.Djinn.LJTFormula (ConsDesc (..), Formula (..),
                                                    Symbol (..), Term (..))

type HSymbol = Name

data HKind
  = KStar
  | KArrow HKind
           HKind
  | KVar Int
  deriving (Eq, Show)

data HType
  = HTApp HType
          HType
  | HTVar HSymbol
  | HTCon HSymbol
  | HTTuple [HType]
  | HTArrow HType
            HType
  | HTUnion [(HSymbol, [HType])]
  deriving (Eq, Show)

type HEnvironment1 = (HSymbol, ([HSymbol], HType))

type HEnvironment = [HEnvironment1]

isHTUnion :: HType -> Bool
isHTUnion (HTUnion _) = True
isHTUnion _           = False

getHTVars :: HType -> [HSymbol]
getHTVars (HTApp f a  ) = getHTVars f `union` getHTVars a
getHTVars (HTVar   v  ) = [v]
getHTVars (HTCon   _  ) = []
getHTVars (HTTuple ts ) = foldr (union . getHTVars) [] ts
getHTVars (HTArrow f a) = getHTVars f `union` getHTVars a
getHTVars _             = error "getHTVars"

hTypeToFormula :: HEnvironment -> HType -> Formula
hTypeToFormula ss (HTTuple ts) = Conj (map (hTypeToFormula ss) ts)
hTypeToFormula ss (HTArrow t1 t2) =
  hTypeToFormula ss t1 :-> hTypeToFormula ss t2
hTypeToFormula ss (HTUnion ctss) = Disj
  [ (ConsDesc c (length ts), hTypeToFormula ss (HTTuple ts)) | (c, ts) <- ctss ]
hTypeToFormula ss t = case expandSyn ss t [] of
  Nothing -> PVar $ SymbolS $ show t
  Just t' -> hTypeToFormula ss t'

expandSyn :: HEnvironment -> HType -> [HType] -> Maybe HType
expandSyn ss (HTApp f a) as = expandSyn ss f (a : as)
expandSyn ss (HTCon c  ) as = case lookup c ss of
  Just (vs, t) | length vs == length as -> Just $ substHT (zip vs as) t
  _ -> Nothing
expandSyn _ _ _ = Nothing

substHT :: [(HSymbol, HType)] -> HType -> HType
substHT r (  HTApp f a) = HTApp (substHT r f) (substHT r a)
substHT r t@(HTVar v  ) = fromMaybe t (lookup v r)
substHT _ t@(HTCon   _  ) = t
substHT r (  HTTuple ts ) = HTTuple (map (substHT r) ts)
substHT r (  HTArrow f a) = HTArrow (substHT r f) (substHT r a)
substHT r (HTUnion (ctss)) =
  HTUnion [ (c, map (substHT r) ts) | (c, ts) <- ctss ]

-------------------------------
data HClause =
  HClause HSymbol
          [HPat]
          HExpr
  deriving (Show, Eq)

data HPat
  = HPVar HSymbol
  | HPCon HSymbol
  | HPTuple [HPat]
  | HPAt HSymbol
         HPat
  | HPApply HPat
            HPat
  deriving (Show, Eq)

data HExpr
  = HELam [HPat]
          HExpr
  | HEApply HExpr
            HExpr
  | HECon HSymbol
  | HEVar HSymbol
  | HETuple [HExpr]
  | HECase HExpr
           [(HPat, HExpr)]
  deriving (Show, Eq)

unSymbol :: Symbol -> HSymbol
unSymbol (Symbol  s) = s
unSymbol (SymbolS s) = mkName s

termToHExpr :: Term -> HExpr
termToHExpr term = niceNames $ etaReduce $ remUnusedVars $ fst $ conv [] term
 where
  conv _vs (Var s) = (HEVar $ unSymbol s, [])
  conv vs (Lam s te) =
    let hs        = unSymbol s
        (te', ss) = conv (hs : vs) te
    in  (hELam [convV hs ss] te', ss)
  conv vs (Apply (Cinj (ConsDesc s n) _) a) =
    (f $ foldl HEApply (HECon s) as, ss)
   where
    (f , as) = unTuple n ha
    (ha, ss) = conv vs a
  conv vs  (Apply te1 te2) = convAp vs te1 [te2]
  conv _vs (Ctuple 0     ) = (HETuple [], [])
  conv _vs e               = error $ "termToHExpr " ++ show e
  unTuple 0 _                             = (id, [])
  unTuple 1 a                             = (id, [a])
  unTuple n (HETuple as) | length as == n = (id, as)
  unTuple n e = error $ "unTuple: unimplemented " ++ show (n, e)
  unTupleP 0 _ = []
  unTupleP n (HPTuple ps) | length ps == n = ps
  unTupleP n p = error $ "unTupleP: unimplemented " ++ show (n, p)
  convAp vs (Apply te1 te2) as = convAp vs te1 (te2 : as)
  convAp vs (Ctuple n) as | length as == n =
    let (es, sss) = unzip $ map (conv vs) as in (hETuple es, concat sss)
  convAp vs (Ccases cds) (se:es) =
    let (alts, ass) = unzip $ zipWith cAlt es cds
        cAlt (Lam v e) (ConsDesc c n) =
          let hv       = unSymbol v
              (he, ss) = conv (hv : vs) e
              ps       = case lookup hv ss of
                Nothing -> replicate n underscore
                Just p  -> unTupleP n p
          in  ((foldl HPApply (HPCon c) ps, he), ss)
        cAlt e _ = error $ "cAlt " ++ show e
        (e', ess) = conv vs se
    in  (hECase e' alts, ess ++ concat ass)
  convAp vs (Csplit n) (b:a:as) =
    let
      (hb , sb ) = conv vs b
      (a' , sa ) = conv vs a
      (as', sss) = unzip $ map (conv vs) as
      (ps , b' ) = unLam n hb
      unLam 0 e = ([], e)
      unLam k (HELam ps0 e) | length ps0 >= n =
        let (ps1, ps2) = splitAt k ps0 in (ps1, hELam ps2 e)
      unLam k e = error $ "unLam: unimplemented" ++ show (k, e)
    in
      case a' of
        HEVar v | v `elem` vs && null as -> (b', [(v, HPTuple ps)] ++ sb ++ sa)
        _ ->
          ( foldr HEApply (hECase a' [(HPTuple ps, b')]) as'
          , sb ++ sa ++ concat sss
          )
  convAp vs f as =
    let (es, sss) = unzip $ map (conv vs) (f : as)
    in  (foldl1 HEApply es, concat sss)
  convV hs ss = case lookup hs ss of
    Nothing -> HPVar hs
    Just p  -> HPAt hs p
  hETuple [e] = e
  hETuple es  = HETuple es

--        conv _vs (Ctuple 0) = (HECon "()", [])
--      unTupleP 1 p = [p]
niceNames :: HExpr -> HExpr
niceNames e =
  let bvars    = filter (/= mkName "_") $ getBinderVarsHE e
      chars    = ['a' .. 'z']
      nvars    = map (: []) chars ++ [ cs ++ [c] | cs <- nvars, c <- chars ]
      freevars = getAllVars e \\ bvars
      vars     = map mkName nvars \\ freevars
      sub      = zip bvars vars
  in  hESubst sub e

hELam :: [HPat] -> HExpr -> HExpr
hELam [] e             = e
hELam ps (HELam ps' e) = HELam (ps ++ ps') e
hELam ps e             = HELam ps e

hECase :: HExpr -> [(HPat, HExpr)] -> HExpr
--hECase e [] = HEApply (HEVar "void") e
--hECase _ [(HPCon "()", e)] = e
hECase e  pes | all (uncurry eqPatExpr) pes = e
hECase e  [     (p, HELam ps b)   ]         = HELam ps $ hECase e [(p, b)]
hECase se alts@((_, HELam ops _):_) | m > 0 = HELam (take m ops)
  $ hECase se alts'
 where
  m = minimum (map (numBind . snd) alts)
  numBind (HELam ps _) = length (takeWhile isPVar ps)
  numBind _            = 0
  isPVar (HPVar _) = True
  isPVar _         = False
  alts' =
    [ let (ps1, ps2) = splitAt m ps
      in  (cps, hELam ps2 $ hESubst (zipWith (\(HPVar v) n -> (v, n)) ps1 ns) e)
    | (cps, HELam ps e) <- alts
    ]
  ns = [ n | HPVar n <- take m ops ]
-- if all arms are equal and there are at least two alternatives there can be no bound vars
-- from the patterns
hECase _ ((_, e):alts@(_:_)) | all (alphaEq e . snd) alts = e
hECase e alts = HECase e alts

eqPatExpr :: HPat -> HExpr -> Bool
eqPatExpr (HPVar   s    ) (HEVar   s'   ) = s == s'
eqPatExpr (HPCon   s    ) (HECon   s'   ) = s == s'
eqPatExpr (HPTuple ps   ) (HETuple es   ) = and (zipWith eqPatExpr ps es)
eqPatExpr (HPApply pf pa) (HEApply ef ea) = eqPatExpr pf ef && eqPatExpr pa ea
eqPatExpr _               _               = False

alphaEq :: HExpr -> HExpr -> Bool
alphaEq e1             e2 | e1 == e2  = True
alphaEq (HELam ps1 e1) (HELam ps2 e2) = Nothing /= do
  s <- matchPat (HPTuple ps1) (HPTuple ps2)
  if alphaEq (hESubst s e1) e2 then return () else Nothing
alphaEq (HEApply f1 a1) (HEApply f2 a2) = alphaEq f1 f2 && alphaEq a1 a2
alphaEq (HECon   s1   ) (HECon   s2   )                            = s1 == s2
alphaEq (HEVar   s1   ) (HEVar   s2   )                            = s1 == s2
alphaEq (HETuple es1  ) (HETuple es2  ) | length es1 == length es2 = and
  (zipWith alphaEq es1 es2)
alphaEq (HECase e1 alts1) (HECase e2 alts2) = alphaEq e1 e2 && and
  ( zipWith alphaEq
            [ HELam [p] e | (p, e) <- alts1 ]
            [ HELam [p] e | (p, e) <- alts2 ]
  )
alphaEq _ _ = False

matchPat :: HPat -> HPat -> Maybe [(HSymbol, HSymbol)]
matchPat (HPVar s1) (HPVar s2) = return [(s1, s2)]
matchPat (HPCon s1) (HPCon s2) | s1 == s2 = return []
matchPat (HPTuple ps1) (HPTuple ps2) | length ps1 == length ps2 = do
  ss <- zipWithM matchPat ps1 ps2
  return $ concat ss
matchPat (HPAt s1 p1) (HPAt s2 p2) = do
  s <- matchPat p1 p2
  return $ (s1, s2) : s
matchPat (HPApply f1 a1) (HPApply f2 a2) = do
  s1 <- matchPat f1 f2
  s2 <- matchPat a1 a2
  return $ s1 ++ s2
matchPat _ _ = Nothing

hESubst :: [(HSymbol, HSymbol)] -> HExpr -> HExpr
hESubst s (  HELam   ps e) = HELam (map (hPSubst s) ps) (hESubst s e)
hESubst s (  HEApply f  a) = HEApply (hESubst s f) (hESubst s a)
hESubst _ e@(HECon   _   ) = e
hESubst s (  HEVar   v   ) = HEVar $ maybe v id $ lookup v s
hESubst s (  HETuple es  ) = HETuple (map (hESubst s) es)
hESubst s (HECase e alts) =
  HECase (hESubst s e) [ (hPSubst s p, hESubst s b) | (p, b) <- alts ]

hPSubst :: [(HSymbol, HSymbol)] -> HPat -> HPat
hPSubst s (  HPVar   v  ) = HPVar $ maybe v id $ lookup v s
hPSubst _ p@(HPCon   _  ) = p
hPSubst s (  HPTuple ps ) = HPTuple (map (hPSubst s) ps)
hPSubst s (  HPAt    v p) = HPAt (maybe v id $ lookup v s) (hPSubst s p)
hPSubst s (  HPApply f a) = HPApply (hPSubst s f) (hPSubst s a)

termToHClause :: HSymbol -> Term -> HClause
termToHClause i term = case termToHExpr term of
  HELam ps e -> HClause i ps e
  e          -> HClause i [] e

remUnusedVars :: HExpr -> HExpr
remUnusedVars expr = fst $ remE expr
 where
  remE (HELam ps e) =
    let (e', vs) = remE e in (HELam (map (remP vs) ps) e', vs)
  remE (HEApply f a) =
    let (f', fs) = remE f
        (a', as) = remE a
    in  (HEApply f' a', fs ++ as)
  remE (HETuple es) =
    let (es', sss) = unzip (map remE es) in (HETuple es', concat sss)
  remE (HECase e alts) =
    let
      (e', es) = remE e
      (alts', sss) =
        unzip
          [ let (ee', ss) = remE ee in ((remP ss p, ee'), ss)
          | (p, ee) <- alts
          ]
    in
      case alts' of
        [(u, b)] | u == underscore -> (b, concat sss)
        _                          -> (hECase e' alts', es ++ concat sss)
  remE e@(HECon _) = (e, [])
  remE e@(HEVar v) = (e, [v])
  remP vs  p@(HPVar   v  ) = if v `elem` vs then p else underscore
  remP _vs p@(HPCon   _  ) = p
  remP vs  (  HPTuple ps ) = hPTuple (map (remP vs) ps)
  remP vs (HPAt v p) = if v `elem` vs then HPAt v (remP vs p) else remP vs p
  remP vs  (  HPApply f a) = HPApply (remP vs f) (remP vs a)
  hPTuple ps | all (== underscore) ps = underscore
  hPTuple ps                          = HPTuple ps

underscore :: HPat
underscore = HPVar (mkName "_")

getBinderVars :: HClause -> [HSymbol]
getBinderVars (HClause _ pats expr) =
  concatMap getBinderVarsHP pats ++ getBinderVarsHE expr

getBinderVarsHE :: HExpr -> [HSymbol]
getBinderVarsHE expr = gbExp expr
 where
  gbExp (HELam   ps e) = concatMap getBinderVarsHP ps ++ gbExp e
  gbExp (HEApply f  a) = gbExp f ++ gbExp a
  gbExp (HETuple es  ) = concatMap gbExp es
  gbExp (HECase se alts) =
    gbExp se ++ concatMap (\(p, e) -> getBinderVarsHP p ++ gbExp e) alts
  gbExp _ = []

getBinderVarsHP :: HPat -> [HSymbol]
getBinderVarsHP pat = gbPat pat
 where
  gbPat (HPVar   s  ) = [s]
  gbPat (HPCon   _  ) = []
  gbPat (HPTuple ps ) = concatMap gbPat ps
  gbPat (HPAt    s p) = s : gbPat p
  gbPat (HPApply f a) = gbPat f ++ gbPat a

getAllVars :: HExpr -> [HSymbol]
getAllVars expr = gaExp expr
 where
  gaExp (HELam   _ps e) = gaExp e
  gaExp (HEApply f   a) = gaExp f `union` gaExp a
  gaExp (HETuple es   ) = foldr union [] (map gaExp es)
  gaExp (HECase se alts) =
    foldr union (gaExp se) (map (\(_p, e) -> gaExp e) alts)
  gaExp (HEVar s) = [s]
  gaExp _         = []

etaReduce :: HExpr -> HExpr
etaReduce expr = fst $ eta expr
 where
  eta (HELam [HPVar v] (HEApply f (HEVar v'))) | v == v' && v `notElem` vs = ( f'
                                                                             , vs
                                                                             )
    where (f', vs) = eta f
  eta (HELam   ps e) = (HELam ps e', vs) where (e', vs) = eta e
  eta (HEApply f  a) = (HEApply f' a', fvs ++ avs)
   where
    (f', fvs) = eta f
    (a', avs) = eta a
  eta e@(HECon   _ ) = (e, [])
  eta e@(HEVar   s ) = (e, [s])
  eta (  HETuple es) = (HETuple es', concat vss)
    where (es', vss) = unzip $ map eta es
  eta (HECase e alts) = (HECase e' alts', vs ++ concat vss)
   where
    (e', vs) = eta e
    (alts', vss) =
      unzip $ [ let (a', ss) = eta a in ((p, a'), ss) | (p, a) <- alts ]

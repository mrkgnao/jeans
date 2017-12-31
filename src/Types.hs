{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE QuasiQuotes #-}
{-# LANGUAGE TemplateHaskellQuotes #-}
module Types where

import Language.Haskell.TH
import Language.Haskell.Djinn

data State s a = State (s -> (a, s))

type U = ()
type D1 = U
type D2 = Either U U
type D3 = Either D2 U
type D3_S = Either U D2
type D4 = Either D2 D2
type D5 = Either D2 D3
type D5_S = Either D3 D2

data Func a b = Func (a -> b)

type StateFmapT s a b = (a -> b) -> State s a -> State s b
type StatePureT s a = a -> State s a
type StateBindT s a b = State s a -> (a -> State s b) -> State s b

type StateFmapQ = forall s a b. StateFmapT s a b
type StatePureQ = forall s a. StatePureT s a
type StateBindQ = forall s a b. StateBindT s a b

data StateFmap = StateFmap StateFmapQ
data StatePure = StatePure StatePureQ
data StateBind = StateBind StateBindQ

cand_fmap = djinnsD "candidates_state_fmap_" [t| forall s a b. StateFmapT s a b |]
cand_pure = djinnsD "candidates_state_pure_" [t| forall s a. StatePureT s a |]
cand_bind = djinnsD "candidates_state_bind_" [t| forall s a b. StateBindT s a b |]

getExps :: Q [Dec] -> Q [Exp]
getExps exps = do
  decs <- exps
  case decs of
    [SigD{}, FunD _ [Clause [] (NormalB (ListE es)) []]] -> pure es


{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE QuasiQuotes #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TemplateHaskellQuotes #-}
{-# LANGUAGE ImpredicativeTypes #-}
module Test where

import Language.Haskell.Djinn
import Language.Haskell.TH
import Test.QuickCheck
import Control.Monad
import Data.Foldable
import Unsafe.Coerce
import Data.List

import Types

cfmaps_pp = $((listE . map (stringE . pprint)) =<< getExps cand_fmap)
cpures_pp = $((listE . map (stringE . pprint)) =<< getExps cand_pure)
cbinds_pp = $((listE . map (stringE . pprint)) =<< getExps cand_bind)

type S = D2
type A = (U,D2)
type B = D2
type C = D3

$cand_fmap
$cand_pure
$cand_bind

candidates_state_fmap :: [StateFmap]
candidates_state_fmap = map StateFmap (unsafeCoerce candidates_state_fmap_)

candidates_state_pure :: [StatePure]
candidates_state_pure = map StatePure (unsafeCoerce candidates_state_pure_)

candidates_state_bind :: [StateBind]
candidates_state_bind = map StateBind (unsafeCoerce candidates_state_bind_)

instance Arbitrary (State S A) where arbitrary = elements $(djinns [t| State S A |])
instance Arbitrary (State S B) where arbitrary = elements $(djinns [t| State S B |])
instance Arbitrary (State S C) where arbitrary = elements $(djinns [t| State S C |])
instance Arbitrary (Func A B) where arbitrary = elements $(djinns [t| Func A B |])

test_state_eq :: (Eq a, Eq s) => State s a -> State s a -> s -> Bool
test_state_eq (State m) (State m') s = m s == m' s

law_fmap_id
  :: StateFmapT S A A -- fmap
  -> State S A -- input
  -> S -- input to input
  -> Bool
law_fmap_id cfmap st@(State k) s = k s == k' s where State k' = cfmap id st

law_monad_left_identity
  :: StatePureT S A
  -> StateBindT S A B
  -> A
  -> (A -> State S B)
  -> State S A
  -> S
  -> Bool
law_monad_left_identity cpure cbind a k m =
  (cpure a `cbind` k) `test_state_eq` k a

law_monad_right_identity
  :: StatePureT S A -> StateBindT S A A -> State S A -> S -> Bool
law_monad_right_identity cpure cbind ma = (ma `cbind` cpure) `test_state_eq` ma

law_monad_assoc
  :: StateBindT S A B
  -> StateBindT S B C
  -> StateBindT S A C
  -> State S A
  -> (A -> State S B)
  -> (B -> State S C)
  -> S
  -> Bool
law_monad_assoc bind_ab bind_bc bind_ac ma amb bmc =
  (ma `bind_ac` (\a -> amb a `bind_bc` bmc))
    `test_state_eq` ((ma `bind_ab` amb) `bind_bc` bmc)

propBool :: Testable prop => prop -> IO Bool
propBool prop = do
  res <- quickCheckWithResult (stdArgs { chatty = False }) prop
  case res of
    Success{} -> pure True
    _         -> pure False

is_fmap :: StateFmapT S A A -> IO Bool
is_fmap f = propBool (law_fmap_id f)

is_monad :: StateFmapQ -> StatePureQ -> StateBindQ -> IO Bool
is_monad cfmap cpure cbind = do
  r <- liftAnd
    [ propBool (law_fmap_id cfmap)
    , propBool (law_monad_left_identity cpure cbind)
    , propBool (law_monad_right_identity cpure cbind)
    , propBool (law_monad_assoc cbind cbind cbind)
    ]
  pure r

liftAnd :: (Monad m) => [m Bool] -> m Bool
liftAnd []     = pure True
liftAnd (x:xs) = do
  x' <- x
  if x' then liftAnd xs else pure False

enumerate = zip [0 ..]

candidate_instances :: [((Int, Int, Int), (StateFmap, StatePure, StateBind))]
candidate_instances =
  [ ((fi, pi, bi), (f, p, b))
  | (fi, f) <- enumerate candidates_state_fmap
  , (pi, p) <- enumerate candidates_state_pure
  , (bi, b) <- enumerate candidates_state_bind
  ]

main :: IO ()
main = do
  putStrLn "Generating law-abiding Functor/Monad implementations for State."
  ixs <- map fst <$> filterM
    (\(_, (StateFmap f, StatePure p, StateBind b)) -> is_monad f p b)
    candidate_instances
  putStrLn ("Found " ++ show (length ixs) ++ " law-abiding implementations.\n")
  forM_ ixs $ \i@(fi, pi, bi) -> do
    putStrLn ("Instance #" ++ show i)
    putStrLn "\nfmap:"
    putStrLn (cfmaps_pp !! fi)
    putStrLn "\npure:"
    putStrLn (cpures_pp !! pi)
    putStrLn "\nbind:"
    putStrLn (cbinds_pp !! bi)
  pure ()

instance Show (State S A) where show _ = "<<state>>" -- unlines . map show $ [f (Left ()), f (Right ())]
instance Show (Func a b) where show _ = "<<fun>>"
instance Show (a -> b) where show _ = "<<fun>>"

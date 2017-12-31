module Language.Haskell.Djinn.LJTFormula
  ( Symbol(..)
  , Formula(..)
  , (<->)
  , (&)
  , fnot
  , false
  , true
  , ConsDesc(..)
  , Term(..)
  , applys
  , freeVars
  ) where

import           Data.List           (union, (\\))
import           Language.Haskell.TH (Name)

infixr 2 :->

infix 2 <->

--infixl 3 |:
infixl 4 &

data Symbol
  = Symbol Name
  | SymbolS String
  deriving (Eq, Ord, Show)

data ConsDesc =
  ConsDesc Name
           Int -- name and arity
  deriving (Eq, Ord, Show)

data Formula
  = Conj [Formula]
  | Disj [(ConsDesc, Formula)]
  | Formula :-> Formula
  | PVar Symbol
  deriving (Eq, Ord, Show)

(<->) :: Formula -> Formula -> Formula
x <-> y = (x :-> y) & (y :-> x)

(&) :: Formula -> Formula -> Formula
x & y = Conj [x, y]

{-
(|:) :: Formula -> Formula -> Formula
x |: y = Disj [((ConsDesc "Left" 1), x), ((ConsDesc "Right" 1), y)]
-}
fnot :: Formula -> Formula
fnot x = x :-> false

false :: Formula
false = Disj []

true :: Formula
true = Conj []

------------------------------
data Term
  = Var Symbol
  | Lam Symbol
        Term
  | Apply Term
          Term
  | Ctuple Int
  | Csplit Int
  | Cinj ConsDesc
         Int
  | Ccases [ConsDesc]
  | Xsel Int
         Int
         Term --- XXX just temporary by MJ
  deriving (Eq, Ord, Show)

applys :: Term -> [Term] -> Term
applys f as = foldl Apply f as

freeVars :: Term -> [Symbol]
freeVars (Var s     ) = [s]
freeVars (Lam   s e ) = freeVars e \\ [s]
freeVars (Apply f a ) = freeVars f `union` freeVars a
freeVars (Xsel _ _ e) = freeVars e
freeVars _            = []

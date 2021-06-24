module Models where

data Token = Ende | Implikation | Punkt | And | KlammerAuf | KlammerZu | Not | Variable String | Name String | Unbekannt String deriving (Show, Eq)

-- TODO: Consider rewriting this as Pointer a and implementing functor
data Pointer = Pointer Int | Nil

instance Show Pointer where
  show (Pointer x) = show x
  show Nil = show "nil"

instance Eq Pointer where
  (Pointer x) == (Pointer y) = x == y
  Nil == Nil = True
  _ == _ = False

{---------------------------------------------------------------------
   Functions for Pointers
 ---------------------------------------------------------------------}

addPi :: Pointer -> Int -> Pointer
addPi Nil y = Pointer y
addPi (Pointer x) y = Pointer $ x + y

pToInt :: Pointer -> Int
pToInt (Pointer x) = x
pToInt Nil = error "Naaaaaaaa"

module Models where

data Token = Ende | Implikation | Punkt | And | KlammerAuf | KlammerZu | Not | Variable String | Name String | Unbekannt String deriving (Show, Eq)

data Pointer = C Int | Nil

instance Show Pointer where 
  show (C x) = show x
  show  Nil  = show "nil"

instance Eq Pointer where
    (C x) == (C y) = x == y
    Nil   ==  Nil  = True
    _     ==  _    = False

{---------------------------------------------------------------------
   Functions for Pointers
 ---------------------------------------------------------------------}

addPI :: Pointer -> Integer -> Pointer
addPI (C x) y = C (x+(fromInteger y)) 
addPI   Nil y = C (fromInteger y)

pToInt:: Pointer -> Int
pToInt (C x) = x
pToInt   Nil = error "Naaaaaaaa"
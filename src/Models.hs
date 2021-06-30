module Models where

data Token = Ende | Implikation | Punkt | And | KlammerAuf | KlammerZu | Not | Variable String | Name String | Unbekannt String deriving (Show, Eq)

data Pointer = Pointer Int | Nil deriving (Show, Eq)

{---------------------------------------------------------------------
   Functions for Pointers
 ---------------------------------------------------------------------}

addPi :: Pointer -> Int -> Pointer
addPi Nil y = Pointer y
addPi (Pointer x) y = Pointer $ x + y

pToInt :: Pointer -> Int
pToInt (Pointer x) = x
pToInt Nil = error "Failed getting Int out of Pointer"

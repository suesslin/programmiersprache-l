module Tokenizer (tokenize) where

import Data.Char (isDigit, isLetter, isLower, isSpace, isUpper)
import Models (Token (..))

type Akkumulator = [Token]

tokenize :: String -> [Token]
tokenize str = tokenize' str []

tokenize' :: String -> Akkumulator -> [Token]
tokenize' [] akk = akk ++ [Ende]
tokenize' (':' : '-' : xs) akk = tokenize' xs (akk ++ [Implikation])
tokenize' ('.' : xs) akk = tokenize' xs (akk ++ [Punkt])
tokenize' (',' : xs) akk = tokenize' xs (akk ++ [And])
tokenize' ('(' : xs) akk = tokenize' xs (akk ++ [KlammerAuf])
tokenize' (')' : xs) akk = tokenize' xs (akk ++ [KlammerZu])
tokenize' ('n' : 'o' : 't' : x : xs) akk
  | not (isAllowed x) = tokenize' (x : xs) (akk ++ [Not])
  | otherwise = tokenize' (dropWhile isAllowed (x : xs)) (akk ++ [Name (takeWhile isAllowed ("not" ++ (x : xs)))])
tokenize' (x : xs) akk
  | isSpace x = tokenize' xs akk
  | isLower x = tokenize' (dropWhile isAllowed xs) (akk ++ [Name (takeWhile isAllowed (x : xs))])
  | isUpper x = tokenize' (dropWhile isAllowed xs) (akk ++ [Variable (takeWhile isAllowed (x : xs))])
  | otherwise = akk ++ [Unbekannt (x : xs)]

isAllowed :: Char -> Bool
isAllowed x = isUpper x || isLower x || isDigit x
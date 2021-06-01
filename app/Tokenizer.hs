module Tokenizer where
    import Data.Char ( isLetter, isDigit, isLower, isSpace, isUpper )
    import Models (Token, TokenizerResult)

    type Akkumulator = TokenizerResult

    tokenizer :: String -> Akkumulator -> TokenizerResult
    tokenizer []                        akk = akk++[Ende]
    tokenizer (':':'-':xs)              akk = tokenizer xs (akk++[Implikation])
    tokenizer ('.':xs)                  akk = tokenizer xs (akk++[Punkt])
    tokenizer (',':xs)                  akk = tokenizer xs (akk++[And])
    tokenizer ('(':xs)                  akk = tokenizer xs (akk++[KlammerAuf])
    tokenizer (')':xs)                  akk = tokenizer xs (akk++[KlammerZu])
    tokenizer ('n':'o':'t':x:xs)        akk
        | not (isLetter x || isDigit x) = tokenizer (x:xs) (akk++[Not])
        | otherwise                     = tokenizer (dropWhile isAllowed (x:xs)) (akk++[Name (takeWhile isAllowed ("not"++(x:xs)))])
    tokenizer (x:xs)                    akk
        | isSpace x = tokenizer xs akk
        | isLower x = tokenizer (dropWhile isAllowed xs) (akk++[Name (takeWhile isAllowed (x:xs)) ])
        | isUpper x = tokenizer (dropWhile isAllowed xs) (akk++[Variable (takeWhile isAllowed (x:xs)) ])
        | otherwise = akk ++ [Unbekannt (x:xs)]

    isAllowed:: Char -> Bool
    isAllowed x = isUpper  x || isLower x || isDigit x
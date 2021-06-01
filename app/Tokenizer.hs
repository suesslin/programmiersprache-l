module Tokenizer where
    import Data.Char

    data Symbol = Ende | Implikation | Punkt | And | KlammerAuf | KlammerZu | Not | Variable |  Name | Unbekannt  deriving (Show)
    type Akkumulator = [(Symbol, String)] 

    tokenizer ::String -> Akkumulator -> [(Symbol, String)]
    tokenizer []                        akk = akk++[(Ende, "")]
    tokenizer (':':'-':xs)              akk = tokenizer xs (akk++[(Implikation, ":-")])
    tokenizer ('.':xs)                  akk = tokenizer xs (akk++[(Punkt, ".")]) 
    tokenizer (',':xs)                  akk = tokenizer xs (akk++[(And, ",")]) 
    tokenizer ('(':xs)                  akk = tokenizer xs (akk++[(KlammerAuf,"(")]) 
    tokenizer (')':xs)                  akk = tokenizer xs (akk++[(KlammerZu, ")")]) 
    tokenizer ('n':'o':'t':x:xs)        akk 
        | not (isLetter x || isDigit x) = tokenizer (x:xs) (akk++[(Not, "not")])
        | otherwise                     = tokenizer (dropWhile isAllowed (x:xs)) (akk++[(Name, takeWhile isAllowed ("not"++(x:xs)))])  
    tokenizer (x:xs)                    akk 
        | isSpace x = tokenizer xs akk
        | isLower x = tokenizer (snd(span (isAllowed) xs)) (akk++[(Name, fst(span (isAllowed) (x:xs))) ]) 
        | isUpper x = tokenizer (snd(span (isAllowed) xs)) (akk++[(Variable, fst(span (isAllowed) (x:xs)))])
        | otherwise = (akk ++ [(Unbekannt,(x:xs))])


    isAllowed:: Char -> Bool
    isAllowed x = isUpper  x || isLower x || isDigit x 
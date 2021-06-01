module Models where

    type TokenizerResult = [Token String] -- Also serves as an accumulator
    data Token a = Ende | Implikation | Punkt | And | KlammerAuf | KlammerZu | Not | Variable a |  Name a | Unbekannt a  deriving (Show)
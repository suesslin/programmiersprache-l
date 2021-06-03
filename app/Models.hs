module Models where

    data Token = Ende | Implikation | Punkt | And | KlammerAuf | KlammerZu | Not | Variable String |  Name String | Unbekannt String  deriving (Show)
module Parser where

    import Models (TokenizerResult, Token)

    data Programm = P1 Ziel 
                  | P2 Programmklausel Programm
      deriving (Show)

    data Programmklausel = Pk1 NichtVariableLTerm Punkt 
                         | Pk2 NichtVariableLTerm Ziel
      deriving (Show)

    -- Für die Wiederholung des Syntaxgraphen vom "Ziel"
    data Teilziel = Tz1 Literal 
                  | Tz2 Literal Komma Teilziel 
      deriving (Show)

    data Ziel = Z1 ImpliziertDurch Literal Punkt
              | Z2 ImpliziertDurch Teilziel Punkt
      deriving (Show)

    data Literal = L1 LTerm | L2 Not LTerm deriving (Show)

    -- Für die Wiederholugn des Syntaxgraphen vom "NichtVariableLTerm"
    data TeilNichtVariableLTerm = TnvLT1 LTerm | TnvLT2 LTerm Komma TeilNichtVariableLTerm

    data NichtVariableLTerm = NvLT1 Name
                            | NvLT2 Name KlammerAuf TeilNichtVariableLTerm KlammerZu
      deriving (Show)

    data LTerm = LT1 Variable | LT2 NichtVariableLTerm deriving (Show)

    data Tree = Programm | Programmklausel | Teilziel | Ziel | Literal | TeilNichtVariableLTerm | NichtVariableLTerm | LTerm
    type Rule = [Token] -> (Tree, [Token])
 
    -- TODO: Better error handling
    
    -- TODO: Maybe implement functor and just use first function
    lookAhead :: [Token] -> Token
    lookAhead [] = error "List of symbols went empty whilst parsing"
    lookAhead (x:_) = x

    
    -- TODO: Redo tail
    tail' :: [Token] -> Token
    tail' [] = error "Jack, don't let go"
    tail' (_:xs) = xs

    -- nichtVariableLTerm :: Rule
    -- nichtVariableLTerm tokens@(token:_) = 
    --     let (tree, tokens') = name tokens
    --     in 
    --         case lookAhead tokens' of
    --             KlammerAuf -> let (tree'', tokens'') = lTerm . tail' $ tokens'
    --                           in 
    --             _          -> error "FIXME"


    -- parser :: [Token String] -> Tree
    -- parser (x:xs) 
module Parser where

    import Models (Token(..))

    type IsTrue = Bool

    -- Is using Lists fine here?
    data Programm = Programm [Programmklausel] Ziel
    data Programmklausel = Pk1 NVLTerm | Pk2 NVLTerm Ziel
    data Ziel = Z1 Literal | Z2 Literal [Literal]
    data Literal = Literal IsTrue LTerm 
    data NVLTerm = NVLTerm String [LTerm]
    data LTerm = LTVar String | LTNVar NVLTerm

    data Tree = TP Programm
              | TPk Programmklausel
              | TZ Ziel
              | TL Literal
              | TLL [Literal]
              | TName String
              | TNVLT NVLTerm
              | TLT LTerm
              | TLLT [LTerm]

    type Rule = [Token] -> (Tree, [Token])
 
    -- TODO: Better error handling
    -- TODO: Maybe implement functor and just use first function
    lookAhead :: [Token] -> Token
    lookAhead [] = error "List of symbols unexpectedly went empty whilst parsing"
    lookAhead (x:_) = x

    -- TODO: Redo tail
    tail' :: [Token] -> [Token]
    tail' [] = error "Jack, don't let go"
    tail' (_:xs) = xs
    
    lTerm :: Rule
    lTerm ((Variable str):toks) = (TLT $ LTVar str, toks)
    lterm = nichtVariableLTerm 

    name :: Rule 
    name ((Name str):toks) = (TName str, toks)
    name (tok:_) = error $ "Expected a name but got: " ++ show tok

    -- Helper function
    teilNichtVariableLTerm :: Rule
    teilNichtVariableLTerm toks =
        let (TLT ltvar, toks') = lterm toks
        in 
            case lookAhead toks' of
                And       -> let (TLLT ltvars, toks'') = teilNichtVariableLTerm (tail' toks')
                             in (TLLT $ ltvar : ltvars, toks'')
                KlammerZu -> (TLLT [ltvar], tail' toks')
                _         -> error $ "Expected AND or close parenthesis but got: " ++ show (lookAhead toks') 

    nichtVariableLTerm :: Rule
    nichtVariableLTerm toks = 
        let (TName str, toks') = name toks
        in
            case lookAhead toks' of
                KlammerAuf -> let (TLLT lterms, toks'') = teilNichtVariableLTerm (tail' toks')
                              in (TNVLT $ NVLTerm str lterms, toks'')
                _          -> error $ "Expected open parenthesis but got: " ++ show (lookAhead toks')

    literal :: Rule
    literal (Not:toks) =
        let (TLT lterm, toks') = lTerm toks
        in (TL $ Literal False lterm, toks')
    literal toks = lTerm toks

    -- Helper function
    reoccurringLiteral :: Rule
    reoccurringLiteral toks = 
        let (TL lit, toks') = literal toks
        in 
            case lookAhead toks' of
                And   -> let (TLL lits, toks'') = reoccurringLiteral (tail' toks')
                         in (TLL $ lit : lits, toks'')
                Punkt -> (TLL [lit], tail' toks')
                _     -> error $ "Expected And or Punkt but got " ++ show (lookAhead toks')

    ziel :: Rule
    ziel (Implikation:toks) = reoccurringLiteral toks 
    -- ziel (Implikation:toks) = 
    --     let ((TL lit), toks') = literal toks
    --     in 
    --         case lookAhead toks' of
    --             And   -> let ((TLL lits), toks'') = reoccurringLiteral (tail' toks')
    --                      in (TLL $ [lit] ++ lits, toks'')
    --             Punkt -> (TZ $ Z1 tree, (tail' toks'))
    ziel (tok:_) = error $ "Expected an Implication but got " ++ show tok


        -- TODO: Programmklausel, Programm

    -- -- parser :: [Token String] -> Tree
    -- -- parser (x:xs) 
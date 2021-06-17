{-# OPTIONS_GHC -Wno-incomplete-patterns #-}
module MiniL2 where

    import Parser
    import Tokenizer
    import Models
    import Data.List


    type B = Bool --backtrack flag
    type T = Integer  --Top of Stack
    type C = Integer  --next Klausel
    type R = Integer  --backtrack adress
    type P = Integer  --programmcounter for next command
    type Atom = String -- for MiniL, could be Variable or Name

    type I = (Adressreg, B, Stack) -> (Adressreg, B,  Stack) --Instructionregister, holds one Instruction
    type Zielcode = [String] --Goal after using ubersetzungen

    type Stack = [Maybe StackElement] --Stack
    data StackElement = A Atom | I Integer deriving (Show, Eq)--Elements, able to be in our Stack 

    type Adressreg = (T, C, R, P) --Pointers that look at different points in Stack

    --Übersetzung für MiniL Programme
    uebersetzungMiniL :: Tree -> Zielcode -> Zielcode
    uebersetzungMiniL (TP (Programm [] (Ziel []))) zielcode                                         = zielcode
    uebersetzungMiniL (TP (Programm [] (Ziel (y:ys)))) zielcode                                     = uebersetzungBody (y:ys) zielcode ++ ["prompt"]
    uebersetzungMiniL (TP (Programm ((Pk1 (NVLTerm str [])):xs) (Ziel (y:ys)))) zielcode            = uebersetzungMiniL (TP (Programm xs (Ziel (y:ys)))) (uebersetzungHead str zielcode ++ ["returnL"])
    uebersetzungMiniL (TP (Programm ((Pk2 (NVLTerm str [])(Ziel ziel)):xs) (Ziel (y:ys)))) zielcode = uebersetzungMiniL (TP (Programm xs (Ziel (y:ys)))) (uebersetzungBody ziel (uebersetzungHead str zielcode) ++ ["returnL"])
    uebersetzungMiniL  _  _                                                                         = error "Kein korrekter Tree, Tree muss anfangen mit TP (Programm ...)"

    --Übersetzung für Fakten
    uebersetzungHead :: Atom -> Zielcode -> Zielcode
    uebersetzungHead atom zielcode = zielcode ++ ["unify " ++ atom, "backtrackQ"]

    --Übersetzung für Literale
    uebersetzungBody :: [Literal] -> Zielcode -> Zielcode
    uebersetzungBody []                                            zielcode = zielcode
    uebersetzungBody ((Literal bool (LTNVar (NVLTerm str []))):ys) zielcode = uebersetzungBody ys (zielcode ++ ["push " ++ str, "call", "backtrackQ"])
    uebersetzungBody                                            _         _ = error "Wird noch nicht behandelt"

    --Zielcode wird weitergegeben, da manche Aufrufe, die folgen, den Zielcode benötigen(Bsp: push ruft cFirst auf und das braucht den Zielcode.)
    stringToCommand:: Zielcode -> Zielcode -> I
    stringToCommand ("prompt":xs)     zielcode = prompt zielcode
    stringToCommand ("returnL":xs)    zielcode = returnL zielcode
    stringToCommand ("backtrackQ":xs) zielcode = backtrackQ zielcode
    stringToCommand ("call":xs)       zielcode = call zielcode
    stringToCommand ((x:xs):rest)     zielcode
                        | x == 'u'             = unify (snd'(words xs)) zielcode
                        | x == 'p'             = push (snd'(words xs)) zielcode
                        | otherwise            = error "Nah fam"
    stringToCommand _                 _        = error "Was kam den da vor?"

    snd':: [a] -> a
    snd' = head . tail

    push:: Atom -> Zielcode -> I
    push atom zielcode ((c,r,t,p),b,stack) = ( (t+1, c+1, t+4, p+1),
                                               b,
                                               stack ++ [Just (I (cFirst zielcode)),Just (I c), Just (I (p+3)), Just (A atom)]
                                             )

    unify :: Atom -> Zielcode -> I
    unify atom zielcode ((c,r,t,p),b,stack) =( (c,r,t,p+1),
                                               isThere (c+3) (Just (A atom)) stack,
                                                stack
                                              )

    call :: Zielcode -> I
    call zielcode ((c,r,t,p),b,stack) = if isThere c Nothing stack
                                        then (
                                             (c,r,t,p+1),
                                             True,
                                             stack
                                             )
                                        else (
                                            (c,r,t, search c stack),
                                            b,
                                            replace c (Just (I (cNext c zielcode))) stack []
                                            )

    returnL :: Zielcode -> I
    returnL zielcode ((c,r,t,p),b,stack) = if not(isThere r Nothing stack)
                                           then (
                                                (c,search r stack+1, t, search (r+1) stack),
                                                b,
                                                stack
                                                )
                                           else (
                                                (c,r,t, search (r+1) stack),
                                                b,
                                                stack
                                                )

    backtrackQ :: Zielcode -> I
    backtrackQ zielcode ((c,r,t,p),b,stack) = if b
                                              then if isThere c Nothing stack && not(isThere r Nothing stack)
                                                   then backtrackQ zielcode ((search r stack, c+1, c+3, p),b, stack)
                                                   else if isThere c Nothing stack
                                                        then ((c,r,t,cLast zielcode), b, stack)
                                                        else ((c,r,t, search c stack), False, replace c (Just (I (cNext c zielcode))) stack [])
                                              else (
                                                   (c,r,t,p+1),
                                                   b,
                                                   stack
                                                   )

    prompt :: Zielcode -> I
    prompt zielcode ((c,r,t,p),b,stack)
          | b     = undefined
          | not b = undefined

    prompt':: IO()
    prompt' = undefined

    --Anmerkung: 0 = Nil, so the Stack starts at 1 not at 0. Index 0 doesnt exits and will be used for errors..
    cFirst :: Zielcode -> Integer
    cFirst     [] = error "Something went wrong whilst translating"
    cFirst (x:xs) = cFirst' (x:xs) [] 1

    --should return the index of the first command from the programms first Programmklausel
    cFirst':: Zielcode -> Zielcode -> Integer -> Integer
    cFirst'              [] akk index = undefined
    cFirst' ("returnL":xs) akk index = undefined
    cFirst'         (x:xs) akk index = undefined

    --returns the index of the first command of the c+1-(fst/snd/thrd/th) Programmklausel 
    cNext:: Integer -> Zielcode -> Integer
    cNext c     [] = error "Something went wrong whilst translating2"
    cNext c (x:xs) = cNext' c (x:xs) [] 1

    cNext' :: Integer -> Zielcode -> Zielcode -> Integer -> Integer
    cNext' c            []  akk zahl = 0 -- This means Nil
    cNext' c ("returnL":xs) akk zahl = cNext' c xs ("returnL":akk) (zahl+1)
    cNext' c         (x:xs) akk zahl = if c == toInteger(length akk) then zahl else cNext' c xs akk (zahl+1)

    --returns the index of the last command(always prompt)
    cLast:: Zielcode -> Integer
    cLast     [] = error "something went wrong whilst translating3"
    cLast (x:xs) = toInteger (length (x:xs))

    --Returns the index of the first command of the programms goal 
    cGoal :: Zielcode -> Integer
    cGoal     [] = error "something went wrong whilst translating4"
    cGoal (x:xs) = cGoal' (reverse(x:xs)) (toInteger (length (x:xs)))

    cGoal' :: Zielcode -> Integer -> Integer
    cGoal' []             index = error "No Goal found."
    cGoal' ("returnL":xs) index = index+1
    cGoal' (x:xs) index = cGoal' xs (index-1)

    --replaces StackElement at the Index Stelle of Stack with newElement. (stack[stelle] = newElement) 
    replace :: Integer -> Maybe StackElement -> Stack -> Stack -> Stack
    replace 0      newElement (x:xs)            akk = akk++[newElement]++ xs
    replace stelle newElement []                akk = error "Stack went empty whilst replaceing"
    replace stelle newElement (Nothing:xs)      akk = replace (stelle-1) newElement xs (akk++[Nothing])
    replace stelle newElement ((Just (A x)):xs) akk = replace (stelle-1) newElement xs (akk++[Just (A x)])
    replace stelle newElement ((Just (I x)):xs) akk = replace (stelle-1) newElement xs (akk++[Just (I x)])

    --returns the pointer of Stack at Index stelle. (stack[stelle])
    search :: Integer -> Stack -> Integer
    search 0      ((Just (A x)):xs) = error "Stack contained an Atom and not a Integer"
    search 0      ((Just (I x)):xs) = x
    search stelle []                = error "Stack went empty whilst searching"
    search stelle (Nothing:xs)      = search (stelle-1) xs
    search stelle ((Just (A x)):xs) = search (stelle-1) xs
    search stelle ((Just(I x)):xs)  = search (stelle-1) xs

    --returns True if StackElement is at Index stelle. (stack[stelle] == gesucht)
    isThere :: Integer -> Maybe StackElement -> Stack -> Bool
    isThere 0      gesucht (x:xs)            = gesucht == x
    isThere stelle gesucht []                = False
    isThere stelle gesucht (Nothing:xs)      = isThere (stelle-1) gesucht xs
    isThere stelle gesucht ((Just (A x)):xs) = isThere (stelle-1) gesucht xs
    isThere stelle gesucht ((Just(I x)):xs)  = isThere (stelle-1) gesucht xs



module MiniL2 where

    import Parser
    import Tokenizer
    import Models
    import Data.List
    import Control.Monad

    --Wichtig bei der Ausgabe eines (c,r,t,p),b,stack (Beispiel zur Verdeutlichung)
    --Zielprogramm: ["unify p","backtrackQ","push q","call","backtrackQ","returnL","unify q","backtrackQ","push r","call","backtrackQ","returnL","unify r","backtrackQ","returnL","push p","call","backtrackQ","push r","call","backtrackQ","prompt"]
    --C zeigt auf eine Klausel im Zielprogramm sprich (C 0) ist die erste Klausel im Zielprogramm.
    --R zeigt auf ein Element im Stack (C 5) heißt also das 6ste Element im Stack, dieses zeigt wieder auf einen Punkt im Stack (C 0) entspricht also das erste Element im Stack
    --T zeigt auf den Top des stacks. (C 7) heißt also der Stack hat 8 Elemente
    --P zeigt auf eine Klausel im Zielprogramm, und zwar die nächste die ausgeführt wird
    -- ((C 4, C 5, C 7, C 3), False, [Just (I (C 6)),Just (I Nil),Just (I (C 18)),Just (A "p"),Just (I (C 0)),Just (I (C 0)),Just (I (C 5)),Just (A "q")]), entspricht also:
    -- C = C 4 = 5tes Element des Stacks = Just (I (C 0)) = Zeigt auf die erste Klausel
    -- R = C 5 = 6stes Element des Stacks = Just (I (C 0)) = Zeigt auf das erste Element im Stack
    -- T = C 7 = Zeigt auf das Achte Element des Stacks also = Just (A "q")
    -- P = C 3 = Zeigt auf die vierte Anweisung. sprich "call" 


    --TODO Pointer entspricht momentan den Pointern auf den Stack und worauf der Stack zeigt, im Stack ist jedes (4x + 2)te Elememt ein Pointer auf den Stack (C 0 meint also das erste Element des Stacks.)

    data Pointer      = Nil | C Integer deriving (Show)
    data StackElement = A Atom | I Pointer deriving (Show)--Elements, able to be in our Stack 

    instance Eq Pointer where 
        C x == C y = x == y
        _   == _   = False

    instance Ord Pointer where
        compare (C x) (C y) = compare x y
        compare Nil   (C y) = LT 
        compare (C x)  Nil  = GT 
        compare Nil    Nil  = EQ

    instance Eq StackElement where
        (A x) == (A y) = x == y
        (I x) == (I y) = x == y
        _     == _     = False

    type B = Bool --backtrack flag
    type T = Pointer  --Top of Stack
    type C = Pointer  --next Klausel
    type R = Pointer  --backtrack adress
    type P = Pointer  --programmcounter for next command
    type Atom = String -- for MiniL, could be Variable or Name

    type I = (Adressreg, B, Stack) -> (Adressreg, B,  Stack) --Instructionregister, holds one Instruction
    type Zielcode = [String] --Goal after using ubersetzungen

    type Stack = [Maybe StackElement] --Stack


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
    stringToCommand:: Zielcode -> Pointer -> Zielcode -> I
    stringToCommand           []        _            _ = error "Kein Zielcode"
    stringToCommand ("prompt":xs)       (C 0) zielcode = prompt zielcode
    stringToCommand ("returnL":xs)      (C 0) zielcode = returnL zielcode
    stringToCommand ("backtrackQ":xs)   (C 0) zielcode = backtrackQ zielcode
    stringToCommand ("call":xs)         (C 0) zielcode = call zielcode
    stringToCommand ((x:xs):rest)       (C 0) zielcode
                        | x == 'u'                     = unify (snd'(words xs)) zielcode
                        | x == 'p'                     = push (snd'(words xs)) zielcode
                        | otherwise                    = error "Nah fam"
    stringToCommand            (x:xs) auswahl zielcode = stringToCommand xs (addPI auswahl(-1)) zielcode

    snd':: [a] -> a
    snd' = head . tail
    
    -- plus Funktionen für den Typ Pointer
    addPP :: Pointer -> Pointer -> Pointer
    addPP Nil Nil = Nil
    addPP Nil x   = x
    addPP x   Nil = x
    addPP (C x) (C y) = C (x+y)

    addPI :: Pointer -> Integer -> Pointer 
    addPI Nil      x = (C x)
    addPI (C y) x = (C (y+x))

    --Stack und Registerverändernde Operationen
    push:: Atom -> Zielcode -> I
    push atom zielcode ((c,r,t,p),b,stack) = ( (addPI t 1, addPI t 2, addPI t 4, addPI p 1),
                                               b,
                                               stack ++ [Just (I (cFirst zielcode)),Just (I c), Just (I (addPI p 3)), Just (A atom)]
                                             )

    unify :: Atom -> Zielcode -> I
    unify atom zielcode ((c,r,t,p),b,stack) =( (c,r,t,addPI p 1),
                                               not(isThere (addPI c 3) (Just (A atom)) stack),
                                                stack
                                              )

    call :: Zielcode -> I
    call zielcode ((c,r,t,p),b,stack) = if isThere c (Just (I Nil)) stack
                                        then (
                                             (c,r,t, addPI p 1),
                                             True,
                                             stack
                                             )
                                        else (
                                            (c,r,t, searchStack c stack),
                                            b,
                                            replace c (Just (I (cNext (searchStack c stack) zielcode))) stack []
                                            )

    returnL :: Zielcode -> I
    returnL zielcode ((c,r,t,p),b,stack) = if not(isThere r (Just (I Nil)) stack)
                                           then (
                                                (c,(addPI (searchStack r stack) 1), t, (searchStack (addPI r 1) stack)),
                                                b,
                                                stack
                                                )
                                           else (
                                                (c,r,t, (searchStack (addPI r 1) stack)),
                                                b,
                                                stack
                                                )

    backtrackQ :: Zielcode -> I
    backtrackQ zielcode ((c,r,t,p),b,stack) = if b
                                              then if isThere c (Just (I Nil)) stack && not(isThere r (Just (I Nil)) stack)
                                                   then backtrackQ zielcode (((searchStack r stack), (addPI (searchStack r stack) 1), (addPI (searchStack r stack) 4), p),b, stack)
                                                   else if isThere c (Just (I Nil)) stack
                                                        then ((c,r,t,cLast zielcode), b, stack)
                                                        else ((c,r,t, searchStack c stack), False, replace c (Just (I (cNext (searchStack c stack) zielcode))) stack [])
                                              else (
                                                   (c,r,t,addPI p 1),
                                                   b,
                                                   stack
                                                   )
    
    --Prompt nicht korrekt
    prompt :: Zielcode -> I
    prompt zielcode tupel@((c,r,t,p),b,stack)
          | b == False = tupel
          | b == True  = ((c,r,t,Nil),b,stack)
    
    promptY :: Zielcode -> I 
    promptY zielcode ((c,r,t,p),b,stack) = ((c,r,t, addPI p (-1)), True, stack)

    promptN :: Zielcode -> I 
    promptN zielcode ((c,r,t,p),b,stack) = ((c,r,t,Nil),b,stack)

    --Hilfsoperationen für env, geben alle einen Pointer zurück, der auf ein Element im Stack zeigt
    --returns the index of the first command of the first Pk
    cFirst :: Zielcode -> Pointer
    cFirst     [] = error "Something went wrong whilst translating"
    cFirst (x:xs) = C 0

    --returns the index of the first command of the c+1-(fst/snd/thrd/th) Programmklausel 
    cNext:: Pointer -> Zielcode -> Pointer
    cNext c         [] = error "Something went wrong whilst translating2"
    cNext Nil     ziel = Nil
    cNext c@(C x) ziel
            | c > letzteKlausel (cLast ziel) (reverse ziel) [] = Nil 
            | otherwise                                         = lookForReturn (drop (fromInteger x) ziel) (x+1)

    --returns the index of the last command(always prompt)
    cLast:: Zielcode -> Pointer
    cLast     [] = error "something went wrong whilst translating3"
    cLast (x:xs) = C $ (toInteger (length (x:xs)) -1)

    --Returns the index of the first command of the programms goal 
    cGoal :: Zielcode -> Pointer
    cGoal     [] = error "something went wrong whilst translating4"
    cGoal (x:xs) = cGoal' (reverse(x:xs)) (toInteger (length (x:xs)))

    cGoal' :: Zielcode -> Integer -> Pointer
    cGoal' []             index = error "No Goal found."
    cGoal' ("returnL":xs) index = C (index)
    cGoal' (x:xs) index = cGoal' xs (index-1)

    --replaces StackElement at the Index Stelle of Stack with newElement. (stack[stelle] = newElement) 
    replace :: Pointer -> Maybe StackElement -> Stack -> Stack -> Stack
    replace _        _          []  akk = error "Stack went empty whilst replaceing"
    replace Nil      _          _   akk = error "Can't replace at Stelle Nil"
    replace (C 0) newElement (x:xs) akk = akk++[newElement]++ xs
    replace (C z) newElement (x:xs) akk = replace (C (z-1)) newElement xs (akk++[x])

    --returns the pointer of Stack at Index stelle. (stack[stelle])
    searchStack :: Pointer -> Stack -> Pointer
    searchStack Nil      stack             = error "Can't search for Stelle Nil"
    searchStack stelle   []                = error "Stack went empty whilst searching"
    searchStack (C 0) ((Just (A x)):xs) = error "Stack contained an Atom and not a Integer"
    searchStack (C 0) ((Just (I x)):xs) = x
    searchStack (C 0) (Nothing:xs)      = Nil
    searchStack (C z) (Nothing:xs)      = searchStack (C (z-1)) xs
    searchStack (C z) ((Just (A x)):xs) = searchStack (C (z-1)) xs
    searchStack (C z) ((Just (I x)):xs) = searchStack (C (z-1)) xs

    --returns True if StackElement is at Index stelle. (stack[stelle] == gesucht)
    isThere :: Pointer -> Maybe StackElement -> Stack -> Bool
    isThere Nil      _       _         = error "Can't lookup Nil-te Stelle"
    isThere stelle gesucht []          = False
    isThere  (C 0) gesucht (x:xs)      = gesucht == x
    isThere  (C z) gesucht (x:xs)      = isThere (C (z-1)) gesucht xs

    --Hilfsfunktion fuer cNext
    lookForReturn :: Zielcode -> Integer -> Pointer
    lookForReturn []             zahl = Nil
    lookForReturn ("returnL":xs) zahl = C zahl
    lookForReturn (x:xs)         zahl = lookForReturn xs (zahl+1)

    --Hilfsfunktion fuer cNext
    letzteKlausel :: Pointer -> Zielcode -> Zielcode -> Pointer
    letzteKlausel c            []              akk = Nil
    letzteKlausel c  ("returnL":xs)             [] = letzteKlausel (addPI c (-1)) xs ["returnL"] 
    letzteKlausel c  ("returnL":xs)    ["returnL"] = c
    letzteKlausel c          (x:xs)            akk = letzteKlausel (addPI c (-1)) xs akk

    --shows the Command supposed to be next in I at Point I
    showCommand :: Zielcode -> (Adressreg,B,Stack) -> Pointer -> String
    showCommand zielcode@(string:rest) zustand@((c,r,t,p),b,stack) x 
                                           | (C 0) == x = head zielcode
                                           | (C (toInteger (length(zielcode)))) <= x = error "Suchanfrage out of range"
                                           | x < (C 0)  = error "Keine Negativen Suchanfragen"
                                           | otherwise  = showCommand rest zustand (addPI x (-1))


    --Testing Stuff
    befehlsZyklus :: Zielcode -> I
    befehlsZyklus zielcode tupel@((c,r,t,p),b,stack) 
                                    | p == Nil  = tupel
                                    | showCommand zielcode tupel p == "prompt" = tupel
                                    | otherwise = befehlsZyklus zielcode (stringToCommand zielcode p zielcode tupel)


    
 
    main :: IO()
    main = do
             let zielcode = uebersetzungMiniL(parser(tokenizer "p:-q.\nq:-r.\nr.\n:-p,r." [])) []
             let start = ((Nil, Nil, C (-1), (cGoal zielcode)), False, [])
             let tupel@((c,r,t,p),b,stack) = befehlsZyklus zielcode start
             when (b) (putStrLn "no (more) solutions")
             input <- getChar 
             when (input == ';') (print (befehlsZyklus zielcode ((c,r,t,(addPI p (-1))),True,stack)))
             putStrLn "Done"

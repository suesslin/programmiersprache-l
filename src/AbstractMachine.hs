module AbstractMachine where

import Control.Exception
import Data.Maybe
import Models
import Parser
import Stack
import Tokenizer

-- TODO: Reorganize signatures: Zielcode -> ... (better currying/partial application)
-- TODO: Reconsider places that used fromJust (unsafe)
-- FIXME: In some places, regs@ refers to the regs and the stack. This is wrong! Fix it.

-- Register
type B = Bool

type T = Pointer

type C = Pointer

type R = Pointer

type P = Pointer

type Addressreg = (B, T, C, R, P)

newtype Atom = A String deriving (Eq)

type Symbol = Atom

type Arity = Int

data Argument
  = ATNot
  | ATNeg
  | ATAtom Atom
  | ATStr Symbol Arity -- Für push (GroundL)
  | ATChp -- Für push (GroundL)
  | ATEndAtom
  deriving (Eq, Show)

instance Show Atom where
  show (A str) = str

-- TODO: Merge CodeAtom and Argument (Atom is contained in Argument)
data StackElement
  = CodeAtom Atom
  | CodeAddress Pointer
  | StackAddress Pointer
  | CodeArg Argument
  deriving (Eq)

instance Show StackElement where
  show (CodeAtom atom) = show atom
  show (CodeAddress Nil) = "nil"
  show (CodeAddress adr) = "c" ++ show adr
  show (StackAddress adr) = "s" ++ show adr
  show (CodeArg arg) = case arg of
    ATNot -> "not"
    ATNeg -> "neg"
    (ATAtom atom) -> show atom

-- Helper
stackItemToInt :: StackElement -> Maybe Pointer
stackItemToInt (CodeAddress x) = Just x
stackItemToInt (StackAddress x) = Just x
stackItemToInt _ = Nothing

-- Unsafe operation that gets the pointer from Stack stack at location i.
-- Can fail if i is out of range or if the item is no Pointer <=> Nothing (fromJust fails)
unsafePointerFromStackAtLocation :: Int -> Stack StackElement -> Pointer
unsafePointerFromStackAtLocation i stack =
  fromJust . stackItemToInt $ stackItemAtLocation i stack

type I = (Addressreg, Stack StackElement) -- why is this named I? Stack [String] needs rework

-- Commands, necessary for having a List of named partially applied functions
data Command
  = Unify (Atom -> I -> I) Atom
  | Push (Atom -> I -> Zielcode -> I) Atom
  | Push' (Argument -> I -> Zielcode -> I) Argument
  | Call (I -> Zielcode -> I)
  | Prompt (I -> Zielcode -> I)
  | Backtrack (I -> Zielcode -> I)
  | Return' (Argument -> I -> I) Argument
  | Return (I -> I)

instance Show Command where
  show (Unify fkt atom) = "unify" ++ " " ++ show atom
  show (Push fkt atom) = "push" ++ " " ++ show atom
  show (Push' fkt arg) = "push" ++ " " ++ show arg
  show (Call _) = "call"
  show (Prompt _) = "prompt"
  show (Backtrack _) = "backtrack?"
  show (Return _) = "return"
  show (Return' _ arg) = "return'" ++ show arg

instance Eq Command where
  (==) (Unify _ atom1) (Unify _ atom2) = atom1 == atom2
  (==) (Push _ atom1) (Push _ atom2) = atom1 == atom2
  (==) (Push' _ arg1) (Push' _ arg2) = arg1 == arg2
  (==) (Call _) (Call _) = True
  (==) (Prompt _) (Prompt _) = True
  (==) (Backtrack _) (Backtrack _) = True
  (==) (Return _) (Return _) = True
  (==) _ _ = False

-- Zielcode is the returntype of L Code Translation
type Zielcode = Stack Command

{----------------------------------------------------------
   MiniL; Üb credit: Lukas; angepasst
-----------------------------------------------------------}

codeGen :: Tree -> Zielcode
codeGen parsetree = üb parsetree (Stack [])

üb :: Tree -> Zielcode -> Zielcode
-- If there are no Programmklauseln
üb (TP (Programm [] (Ziel lits))) akk = üb (TZ (Ziel lits)) akk
-- If there are Programmklauseln
üb (TP (Programm klauseln@(pklausel : pklauseln) (Ziel lits))) akk
  | null pklauseln = üb (TZ (Ziel lits)) $ üb (TPk pklausel) akk
  | otherwise = üb (TP (Programm pklauseln (Ziel lits))) $ üb (TPk pklausel) akk
-- Üb(Atom.)
üb (TPk (Pk1 (NVLTerm atom _))) akk = übHead (A atom) akk <> Stack [Return returnL]
-- Üb(Atom :- Seq)
üb (TPk (Pk2 (NVLTerm atom _) (Ziel seq))) akk =
  let akk' = übHead (A atom) akk
   in übBody seq akk' <> Stack [Return returnL]
üb (TZ (Ziel literals)) akk = übBody literals akk <> Stack [Prompt prompt]
üb _ akk = error $ "Failure in :- Seq translation." ++ show akk

übHead :: Atom -> Zielcode -> Zielcode
übHead atom akk = akk <> Stack [Unify unify atom, Backtrack backtrackQ]

-- TODO: Instead of using let, create separate functions
übBody :: [Literal] -> Zielcode -> Zielcode
-- Üb_Body([not Atom | Sequenz]): Negation durch Scheitern
übBody ((Literal False (LTNVar (NVLTerm atom _))) : seq) akk =
  let akk' =
        akk
          <> Stack
            [ Push' push' ATNot,
              Push' push' (ATAtom $ A atom),
              Call call,
              Backtrack backtrack',
              Return' returnL' ATNeg,
              Backtrack backtrack'
            ]
   in übBody seq akk'
-- Üb_Body([Atom | Sequenz])
übBody ((Literal _ (LTNVar (NVLTerm atom _))) : seq) akk =
  let akk' = akk <> Stack [Push push (A atom), Call call, Backtrack backtrackQ]
   in übBody seq akk'
übBody [] akk = akk
übBody _ _ = error "Failure in übBody."

{--------------------------------------------------------------
   Instruktionen
 ---------------------------------------------------------------}

push :: Atom -> I -> Zielcode -> I
push atom ((b, t, c, _, p), stack) code =
  ( (b, addPi t 4, addPi t 1, addPi t 2, addPi p 1),
    stackTake (pToInt (addPi t 1)) stack
      <> Stack
        [CodeAddress $ cFirst code, StackAddress c, CodeAddress $ addPi p 3, CodeAtom atom]
      <> stackDrop (pToInt (addPi t 4)) stack
  )

-- Push für Negation durch Scheitern
push' :: Argument -> I -> Zielcode -> I
push' arg (regs@(b, t, c, r, p), stack) code =
  ((b, t +<- 4, t +<- 1, t +<- 2, p), newStackForPush (regs, stack) arg code)

-- Push für GroundL
push'' :: Argument -> (I -> (Zielcode -> I))
-- push STR Symbol Arity
push'' arg@(ATStr sym arity) ((b, t, c, r, p), stack) _ =
  ( (b, t +<- 1, c, r, p +<- 1),
    stackReplaceAtLocation
      (pToInt $ t +<- 1)
      (CodeArg arg)
      stack
  )
-- Push CHP
-- TODO: UP Register
push'' ATChp ((b, t, c, r, p), stack) code =
  ( (b, t +<- 1, t +<- 1, t +<- 2, p +<- 1),
    stackReplaceAtLocation
      (pToInt $ t +<- 2)
      (CodeAddress c)
      ( stackReplaceAtLocation
          (pToInt $ t +<- 1)
          (CodeAddress $ cFirst code)
          stack
      )
  )
push'' ATEndAtom ((b, t, c, r, p), stack) _ =
  ( (b, t, c, r, p +<- 1),
    stackReplaceAtLocation
      (pToInt $ c +<- 5)
      (CodeAddress t)
      ( stackReplaceAtLocation
          (pToInt $ c +<- 2)
          (CodeAddress $ p +<- 3)
          stack
      )
  )
push'' _ _ _ = error "Case not covered by GroundL pattern matching for push."

newStackForPush :: I -> (Argument -> (Zielcode -> Stack StackElement))
newStackForPush (regs@(b, t, c, r, p), stack) arg code =
  stackWriteToLocation (pToInt $ t +<- 4) (CodeArg arg)
    . stackWriteToLocation (pToInt $ t +<- 2) (CodeAddress c)
    $ newConditionalStackForPush (regs, stack) arg code

newConditionalStackForPush :: I -> (Argument -> (Zielcode -> Stack StackElement))
newConditionalStackForPush ((_, t, _, _, p), stack) ATNot _ =
  stackWriteToLocation (pToInt $ t +<- 3) (CodeAddress $ p +<- 4) $
    stackWriteToLocation (pToInt $ t +<- 1) (CodeAddress Nil) stack
newConditionalStackForPush ((_, t, _, _, p), stack) _ code =
  stackWriteToLocation (pToInt $ t +<- 3) (CodeAddress $ p +<- 3) $
    stackWriteToLocation (pToInt $ t +<- 1) (CodeAddress $ cFirst code) stack

unify :: Atom -> I -> I
unify atom ((_, t, c, r, p), stack) =
  let b' = stackItemAtLocation (pToInt (addPi c 3)) stack /= CodeAtom atom
   in ((b', t, c, r, addPi p 1), stack)

-- TODO: Auseinanderziehen
call :: I -> Zielcode -> I
call ((b, t, c, r, p), stack) code =
  if stackItemAtLocation (pToInt c) stack == CodeAddress Nil -- TODO,actually just undefinied
    then ((True, t, c, r, addPi p 1), stack)
    else
      let p' = unsafePointerFromStackAtLocation (pToInt c) stack
          stack' =
            stackReplaceAtLocation
              (pToInt c)
              ( CodeAddress $
                  cNext code (fromJust . stackItemToInt $ stackItemAtLocation c stack)
              )
              stack
       in ((b, t, c, r, p'), stack')

-- possible problem; nur logisches entkellern, untested
returnL :: I -> I
returnL ((b, t, c, r, p), stack) =
  let p' = unsafePointerFromStackAtLocation (pToInt (addPi r 1)) stack
   in if stackItemAtLocation (pToInt r) stack /= CodeAddress Nil
        then
          let r' = (fromJust . stackItemToInt $ stackItemAtLocation r stack) +<- 1
           in ((b, t, c, r', p'), stack)
        else ((b, t, c, r, p'), stack)

-- ((b, t, c, r', p'), stack)

--  in error $
--       "Irgendwas " ++ show stack ++ "\nr:" ++ show r ++ "\n\nr':"
--         ++ show (stackItemToInt $ stackItemAtLocation r stack)
--         ++ "\n\n"

-- Return für Negation durch Scheitern
returnL' :: Argument -> I -> I
returnL' arg (regs, stack) =
  newStackForReturnIfNoBackjump $ newStackForReturnIfNeg arg (regs, stack)

newStackForReturnIfNeg :: Argument -> I -> I
newStackForReturnIfNeg ATNeg ((b, t, c, r, p), stack) =
  ((False, t, c, r, p), stackWriteToLocation (pToInt $ r -<- 1) (CodeAddress Nil) stack)
newStackForReturnIfNeg _ (regs, stack) = (regs, stack)

newStackForReturnIfNoBackjump :: I -> I
newStackForReturnIfNoBackjump ((b, t, c, r, p), stack)
  | stackItemAtLocation (pToInt r) stack /= CodeAddress Nil =
    let p' = (fromJust . stackItemToInt $ stackItemAtLocation (pToInt r + 1) stack)
        r' = (fromJust . stackItemToInt $ stackItemAtLocation (pToInt r) stack) +<- 1
     in ((b, t, c, r', p'), stack)
  | otherwise =
    ((b, t, c, r, p +<- 1), stack)

backtrackQ :: I -> Zielcode -> I
backtrackQ (regs@(True, _, _, _, _), stack) code = backtrack (regs, stack) code
backtrackQ (regs, stack) code = noBacktrack (regs, stack)

-- Backtrack flag is set to True
backtrack :: I -> Zielcode -> I
backtrack i@(_, stack) code =
  let (regs'@(_, _, c', _, _), stack') = physicalPoppingIfCpNilAndBackjumpNot i
   in if unsafeIsStackNilForRegister c' stack'
        then backtrackCpNil (regs', stack') code
        else backtrackCpNotNil (regs', stack') code

backtrackCpNil :: I -> Zielcode -> I
backtrackCpNil ((b, t, c, r, _), stack) code = ((b, t, c, r, cLast code), stack)

backtrackCpNotNil :: I -> Zielcode -> I
backtrackCpNotNil ((_, t, c, r, _), stack) code =
  ( (False, t, c, r, unsafePointerFromStackAtLocation (pToInt c) stack),
    stackReplaceAtLocation (pToInt c) (CodeAddress $ cNext code c) stack
  )

noBacktrack :: I -> I
noBacktrack ((b, t, c, r, p), stack) = ((b, t, c, r, addPi p 1), stack)

physicalPoppingIfCpNilAndBackjumpNot :: I -> I
physicalPoppingIfCpNilAndBackjumpNot ((b, t, c, r, p), stack)
  | unsafeIsStackNilForRegister c stack && not (unsafeIsStackNilForRegister r stack) =
    ( ( b,
        addPi c 3,
        unsafePointerFromStackAtLocation (pToInt r) stack,
        addPi c 1,
        p
      ),
      stack
    )
  | otherwise = ((b, t, c, r, p +<- 1), stack)

unsafeIsStackNilForRegister :: Pointer -> Stack StackElement -> Bool
unsafeIsStackNilForRegister (Pointer regAddr) stack =
  CodeAddress Nil == stackItemAtLocation regAddr stack
unsafeIsStackNilForRegister Nil _ = error "Empty register (Nil) but expected an address."

-- Backtrack? für Negation durch Scheitern
backtrackQ' :: I -> Zielcode -> I
backtrackQ' (regs@(True, _, _, _, _), stack) code = backtrack' (regs, stack) code
backtrackQ' (regs, stack) code = noBacktrack (regs, stack)

-- Backtrack flag is set to True
backtrack' :: I -> Zielcode -> I
backtrack' i@(_, stack) code =
  let (regs'@(_, _, c', _, _), stack') = physicalPoppingIfCpNilAndBackjumpNot i
   in if unsafeIsStackNilForRegister c' stack'
        then backtrackCpNil' (regs', stack') code
        else backtrackCpNotNil (regs', stack') code

backtrackCpNil' :: I -> Zielcode -> I
backtrackCpNil' ((b, t, c, r, _), stack) code
  | stackItemAtLocation (pToInt c + 3) stack == CodeArg ATNot =
    ((b, t, c, r, unsafePointerFromStackAtLocation (pToInt $ c +<- 2) stack), stack)
  | otherwise =
    ((b, t, c, r, cLast code), stack)

-- TODO: Discuss how else to solve this: Since prompt ist the last instruction, perhaps --       impurely through main?
prompt :: I -> Zielcode -> I -- greedy prompt without IO, temporary solution
prompt reg@((b, t, c, r, p), stack) code =
  if b
    then ((b, t, c, r, Nil), stack) -- should be nil or undefinied, fix by using stack?
    else ((True, t, c, r, addPi p (-1)), stack)

prompt' :: I -> Zielcode -> IO ()
prompt' reg@((b, t, c, r, p), stack) code
  | b = do
    putStrLn "no (more) solutions."
  | otherwise = do
    putStrLn "yes. more?"
    answer <- getLine
    if answer == ";"
      then undefined --evalFromPrompt ((True, t,c,r,p-1), stack) code TODO!!
      else putStrLn "Wrong input, aborting."

{--------------------------------------------------------------------
   Helpers; manually tested.
 --------------------------------------------------------------------}

transformN :: [Command] -> Int -> Stack String
transformN code amount = Stack (map (take amount . show) code)

cFirst :: Zielcode -> Pointer
cFirst (Stack code) = Pointer $ stackLocationFirstItemOfKind "unify" (transformN code 5) -- doesnt really use command datatype, rather its show repr.

--currently tells you distance to next "unify" given a location, hence no absolute value. TODO: FIX ME!!!, error lies in the use of drop.
cNext :: Zielcode -> Pointer -> Pointer
cNext (Stack code) Nil = Nil
cNext (Stack code) p@(Pointer address) =
  case stackLocationFirstItemOfKind' "unify" (transformN (drop (address + 1) code) 5) of
    (Just relativeItemLocation) -> (p +<- 1) + Pointer relativeItemLocation
    Nothing -> Nil

cLast :: Zielcode -> Pointer
cLast (Stack code) = Pointer $ stackLocationFirstItemOfKind "prompt" (transformN code 6)

-- FIXME: Reconsider if this should really be 0 and not Nil (Pointer) in case of Nothing
--        Our consideration about until now is that 0 should be okay.
cGoal :: Zielcode -> Pointer
cGoal (Stack code) = case stackLocationLastItemOfKind' "return" (transformN code 6) of
  (Just location) -> Pointer location +<- 1
  Nothing -> 0

-- the +1 is needed because start of goal is determined by checking the address of the last return statement

{---------------------------------------------------------------------
   Evaluator Functions -> take generated code list and call functions
 ---------------------------------------------------------------------}

-- evaluator(s), there might be a better solution for our command datatype
callZielcode :: Command -> I -> Zielcode -> I
callZielcode (Push _ atom) reg code = push atom reg code
callZielcode (Push' _ arg) reg code = push' arg reg code
callZielcode (Unify _ atom) reg _ = unify atom reg
callZielcode (Call _) reg code = call reg code
callZielcode (Backtrack _) reg code = backtrackQ reg code
callZielcode (Return _) reg _ = returnL reg
callZielcode (Return' _ arg) reg _ = returnL' arg reg
callZielcode (Prompt _) reg code = prompt reg code

{- callPrompt':: Command -> I -> Zielcode -> IO()
callPrompt' (Prompt' name inst) reg code = prompt' reg code
callPrompt' _ _ _ = error $ "eval prompt failed." -}

--TODO, for prompt implementation
{- callFromPrompt :: I -> Zielcode -> IO()
callFromPrompt reg (Stack (firstfkt:rest)) = do
   putStrLn "reeval"
   let newreg = callZielcode firstfkt reg (Stack rest)
   prompt newreg code  -}

runner :: I -> Zielcode -> Zielcode -> I
runner reg (Stack (firstfkt : rest)) code = runner (callZielcode firstfkt reg code) (Stack rest) code
runner reg (Stack []) code = reg

-- code :: Zielcode
-- code = codeGen (parse $ tokenize "p :- q. q :- r. r. :- p, r.")

-- initial :: I
-- initial = ((False, Pointer (-1), Nil, Nil, cGoal code), initStack)

-- initStack :: Stack StackElement
-- initStack = stackNewEmpty

module AbstractMachineBase where

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

instance Show Atom where
  show (A str) = str

data StackElement = CodeAtom Atom | CodeAddress Pointer deriving (Eq)

instance Show StackElement where
  show (CodeAtom atom) = show atom
  show (CodeAddress Nil) = "nil"
  show (CodeAddress adr) = "c" ++ show adr

--helper
stackItemToInt :: StackElement -> Maybe Pointer
stackItemToInt (CodeAddress x) = Just x
stackItemToInt (CodeAtom x) = Nothing

type I = (Addressreg, Stack StackElement) -- why is this named I? Stack [String] needs rework

-- Commands, necessary for having a List of named partially applied functions
data Command
  = Unify String (Atom -> I -> I) Atom
  | Push String (Atom -> I -> Zielcode -> I) Atom
  | Call String (I -> Zielcode -> I)
  | Prompt String (I -> Zielcode -> I)
  | Backtrack String (I -> Zielcode -> I)
  | Return String (I -> I)

-- Prompt' String (I -> Zielcode -> IO())

instance Show Command where
  show (Unify name fkt atom) = name ++ " " ++ show atom
  show (Push name fkt atom) = name ++ " " ++ show atom
  show (Call name inst) = name
  show (Prompt name inst) = name
  show (Backtrack name inst) = name
  show (Return name inst) = name

--show (Instruktion name inst) = name

instance Eq Command where
  (==) (Unify name1 fkt1 atom1) (Unify name2 fkt2 atom2) = (name1 == name2) && (atom1 == atom2)
  (==) (Push name1 fkt1 atom1) (Push name2 fkt2 atom2) = (name1 == name2) && (atom1 == atom2)
  (==) (Call name1 inst1) (Call name2 inst2) = name1 == name2
  --(==) (Instruktion name1 inst1) (Instruktion name2 inst2) = name1 == name2
  (==) _ _ = False

-- Zielcode is the returntype of L Code Translation
type Zielcode = Stack Command

{----------------------------------------------------------
   MiniL; Üb credit: Lukas; angepasst
-----------------------------------------------------------}

codeGen :: Tree -> Zielcode
codeGen parsetree = üb parsetree (Stack [])

üb :: Tree -> Zielcode -> Zielcode
üb (TP (Programm klauseln@(pklausel : pklauseln) (Ziel lits))) akk
  | null klauseln = üb (TZ (Ziel lits)) akk
  | null pklauseln = üb (TZ (Ziel lits)) $ üb (TPk pklausel) akk
  | otherwise = üb (TP (Programm pklauseln (Ziel lits))) $ üb (TPk pklausel) akk
-- Üb(Atom.)
üb (TPk (Pk1 (NVLTerm atom _))) akk = übHead (A atom) akk <> Stack [Return "return" returnL]
-- Üb(Atom :- Seq)
üb (TPk (Pk2 (NVLTerm atom _) (Ziel seq))) akk =
  let akk' = übHead (A atom) akk
   in übBody seq akk' <> Stack [Return "return" returnL]
-- Üb(:- Seq) -- TODO !!! error in translations of code with no klauseln, only ziel i.e. ":-p,r.".
üb (TZ (Ziel literals)) akk = übBody literals akk <> Stack [Prompt "prompt" prompt]
üb _ akk = error $ "Failure in :- Seq translation." ++ show akk

-- üb ([not Atom | Seqeunz]) [Negation durch Scheitern]

übHead :: Atom -> Zielcode -> Zielcode
übHead atom akk = akk <> Stack [Unify "unify" unify atom, Backtrack "backtrack?" backtrackQ]

übBody :: [Literal] -> Zielcode -> Zielcode
übBody ((Literal polarity (LTNVar (NVLTerm atom _))) : seq) akk =
  let akk' = akk <> Stack [Push "push" push (A atom), Call "call" call, Backtrack "backtrack?" backtrackQ]
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
        [CodeAddress $ cFirst code, CodeAddress c, CodeAddress $ addPi p 3, CodeAtom atom]
      <> stackDrop (pToInt (addPi t 4)) stack
  )

unify :: Atom -> I -> I
unify atom ((_, t, c, r, p), stack) =
  let b' = stackItemAtLocation (pToInt (addPi c 3)) stack /= CodeAtom atom
   in ((b', t, c, r, addPi p 1), stack)

call :: I -> Zielcode -> I
call ((b, t, c, r, p), stack) code =
  if stackItemAtLocation (pToInt c) stack == CodeAddress Nil -- TODO,actually just undefinied
    then ((True, t, c, r, addPi p 1), stack)
    else
      let p' = fromJust . stackItemToInt $ stackItemAtLocation (pToInt c) stack
          stack' =
            stackInsertAtLocation
              (pToInt c)
              (CodeAddress (cNext code (fromJust . stackItemToInt $ stackItemAtLocation (pToInt c) stack)))
              stack
       in ((b, t, c, r, p'), stack')

-- possible problem; nur logisches entkellern, untested
returnL :: I -> I
returnL ((b, t, c, r, p), stack) =
  let p' = fromJust . stackItemToInt $ stackItemAtLocation (pToInt (addPi r 1)) stack
   in if stackItemAtLocation (pToInt r) stack /= CodeAddress Nil
        then
          ( (b, t, c, addPi (fromJust (stackItemToInt $ stackItemAtLocation (pToInt r) stack)) 1, p'),
            stack
          )
        else ((b, t, c, r, p'), stack)

backtrackQ :: I -> Zielcode -> I
backtrackQ (regs@(b, _, _, _, _), stack) code =
  if b then backtrack (regs, stack) code else noBacktrack (regs, stack)

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
  ( (False, t, c, r, fromJust . stackItemToInt $ stackItemAtLocation (pToInt c) stack),
    stackInsertAtLocation (pToInt c) (CodeAddress $ cNext code c) stack
  )

noBacktrack :: I -> I
noBacktrack ((b, t, c, r, p), stack) = ((b, t, c, r, addPi p 1), stack)

physicalPoppingIfCpNilAndBackjumpNot :: I -> I
physicalPoppingIfCpNilAndBackjumpNot ((b, _, c, r, p), stack)
  | unsafeIsStackNilForRegister c stack && not (unsafeIsStackNilForRegister r stack) =
    ( ( b,
        addPi c 3,
        fromJust . stackItemToInt $ stackItemAtLocation (pToInt r) stack,
        addPi c 1,
        p
      ),
      stack
    )
  | otherwise = undefined

unsafeIsStackNilForRegister :: Pointer -> Stack StackElement -> Bool
unsafeIsStackNilForRegister (Pointer regAddr) stack =
  CodeAddress Nil == stackItemAtLocation regAddr stack
unsafeIsStackNilForRegister Nil _ = error "Empty register (Nil) but expected an address."

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
cNext (Stack code) (Pointer address) =
  addPi
    (Pointer $ stackLocationFirstItemOfKind "unify" (transformN (drop (address + 1) code) 5))
    1

-- +1 needed because drop shrinks list by one

cLast :: Zielcode -> Pointer
cLast (Stack code) = Pointer $ stackLocationFirstItemOfKind "prompt" (transformN code 6)

cGoal :: Zielcode -> Pointer
cGoal (Stack code) =
  addPi
    (Pointer $ stackLocationLastItemOfKind "return" (transformN code 6))
    1

-- the +1 is needed because start of goal is determined by checking the address of the last return statement

{---------------------------------------------------------------------
   Evaluator Functions -> take generated code list and call functions
 ---------------------------------------------------------------------}

-- evaluator(s), there might be a better solution for our command datatype
callZielcode :: Command -> I -> Zielcode -> I
callZielcode (Push name fkt atom) reg code = push atom reg code
callZielcode (Unify name fkt atom) reg code = unify atom reg
callZielcode (Call name inst) reg code = call reg code
callZielcode (Backtrack name inst) reg code = backtrackQ reg code
callZielcode (Return name inst) reg code = returnL reg
callZielcode (Prompt name inst) reg code = prompt reg code

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

code :: Zielcode
code = codeGen (parse $ tokenize "p :- q. q :- r. r. :- p, r.")

initial :: I
initial = ((False, Pointer (-1), Nil, Nil, cGoal code), initStack)

initStack :: Stack StackElement
initStack = stackNewEmpty

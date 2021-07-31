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

type Up = Pointer

type E = Pointer 

type AddressRegs = (B, T, C, R, P)

type AddressRegs' = (B, T, C, R, P, Up)

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
  | ATEndEnv --data Stack Argument (könnte bspw ENdEnv o.ä. enthalten)
  | ATStr Atom' -- Suggestion
  | ATVar Variable -- ^ 
  | ATPush
  | ATUnify 
  deriving (Eq, Show) 

type Addressreg = (B, T, C, R, P)

newtype Atom = A String deriving (Eq)

{------------------------- 
  Datentypen für ML 
 ----------------------------}
type Linearization = (String, Arity)

newtype Atom' = Str Linearization deriving (Eq)
newtype Variable = Var (String, Pointer) deriving (Eq)

instance Show Atom' where 
  show (Str lin) = "Str " ++ show lin

instance Show Variable where
  show (Var (name, addr)) = "Var " ++ show name ++ show addr  
{- 
  Bestehende Datentypen
 -}

--data Stack Argument (könnte bspw ENdEnv o.ä. enthalten)

instance Show Atom where
  show (A Str) = Str

-- TODO: Merge CodeAtom and Argument (Atom is contained in Argument)
data StackElement
  = CodeAtom Atom
  | CodeVariable Variable 
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
    ATPush -> "push"
    ATUnify -> "unify"
    (ATAtom atom) -> show atom
    
--helper
stackItemToInt :: StackElement -> Maybe Pointer
stackItemToInt (CodeAddress x) = Just x
stackItemToInt (StackAddress x) = Just x
stackItemToInt _ = Nothing

-- Unsafe operation that gets the pointer from Stack stack at location i.
-- Can fail if i is out of range or if the item is no Pointer <=> Nothing (fromJust fails)
unsafePointerFromStackAtLocation :: Int -> Stack StackElement -> Pointer
unsafePointerFromStackAtLocation i stack =
  fromJust . stackItemToInt $ stackItemAtLocation i stack

type MLStack = Stack StackElement

-- Commands, necessary for having a List of named partially applied functions
data Command
  = Unify (Atom -> (AddressRegs, MLStack) -> (AddressRegs, MLStack)) Atom
  | Push (Atom -> (AddressRegs, MLStack) -> Zielcode -> (AddressRegs, MLStack)) Atom
  | Push' (Argument -> (AddressRegs, MLStack) -> Zielcode -> (AddressRegs, MLStack)) Argument
  | Call ((AddressRegs, MLStack) -> Zielcode -> (AddressRegs, MLStack))
  | Prompt ((AddressRegs, MLStack) -> Zielcode -> (AddressRegs, MLStack))
  | Backtrack ((AddressRegs, MLStack) -> Zielcode -> (AddressRegs, MLStack))
  | Return' (Argument -> (AddressRegs, MLStack) -> (AddressRegs, MLStack)) Argument
  | Return ((AddressRegs, MLStack) -> (AddressRegs, MLStack))

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
   InStruktionen
 ---------------------------------------------------------------}

push :: Atom -> (AddressRegs, MLStack) -> Zielcode -> (AddressRegs, MLStack)
push atom ((b, t, c, _, p), stack) code =
  ( (b, addPi t 4, addPi t 1, addPi t 2, addPi p 1),
    stackTake (pToInt (addPi t 1)) stack
      <> Stack
        [CodeAddress $ cFirst code, StackAddress c, CodeAddress $ addPi p 3, CodeAtom atom]
      <> stackDrop (pToInt (addPi t 4)) stack
  )

-- Push für Negation durch Scheitern
push' :: Argument -> (AddressRegs, MLStack) -> Zielcode -> (AddressRegs, MLStack)
push' arg (regs@(b, t, c, r, p), stack) code =
  ((b, t +<- 4, t +<- 1, t +<- 2, p), newStackForPush (regs, stack) arg code)

-- Push für GroundL
push'' :: Argument -> ((AddressRegs, MLStack) -> (Zielcode -> (AddressRegs, MLStack)))
-- push Str Symbol Arity
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

newStackForPush :: (AddressRegs, MLStack) -> (Argument -> (Zielcode -> Stack StackElement))
newStackForPush (regs@(b, t, c, r, p), stack) arg code =
  stackWriteToLocation (pToInt $ t +<- 4) (CodeArg arg)
    . stackWriteToLocation (pToInt $ t +<- 2) (CodeAddress c)
    $ newConditionalStackForPush (regs, stack) arg code

newConditionalStackForPush :: (AddressRegs, MLStack) -> (Argument -> (Zielcode -> Stack StackElement))
newConditionalStackForPush ((_, t, _, _, p), stack) ATNot _ =
  stackWriteToLocation (pToInt $ t +<- 3) (CodeAddress $ p +<- 4) $
    stackWriteToLocation (pToInt $ t +<- 1) (CodeAddress Nil) stack
newConditionalStackForPush ((_, t, _, _, p), stack) _ code =
  stackWriteToLocation (pToInt $ t +<- 3) (CodeAddress $ p +<- 3) $
    stackWriteToLocation (pToInt $ t +<- 1) (CodeAddress $ cFirst code) stack

unify :: Atom -> (AddressRegs, MLStack) -> (AddressRegs, MLStack)
unify atom ((_, t, c, r, p), stack) =
  let b' = stackItemAtLocation (pToInt (addPi c 3)) stack /= CodeAtom atom
   in ((b', t, c, r, addPi p 1), stack)

-- TODO: Auseinanderziehen
call :: (AddressRegs, MLStack) -> Zielcode -> (AddressRegs, MLStack)
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
returnL :: (AddressRegs, MLStack) -> (AddressRegs, MLStack)
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
returnL' :: Argument -> (AddressRegs, MLStack) -> (AddressRegs, MLStack)
returnL' arg (regs, stack) =
  newStackForReturnIfNoBackjump $ newStackForReturnIfNeg arg (regs, stack)

newStackForReturnIfNeg :: Argument -> (AddressRegs, MLStack) -> (AddressRegs, MLStack)
newStackForReturnIfNeg ATNeg ((b, t, c, r, p), stack) =
  ((False, t, c, r, p), stackWriteToLocation (pToInt $ r -<- 1) (CodeAddress Nil) stack)
newStackForReturnIfNeg _ (regs, stack) = (regs, stack)

newStackForReturnIfNoBackjump :: (AddressRegs, MLStack) -> (AddressRegs, MLStack)
newStackForReturnIfNoBackjump ((b, t, c, r, p), stack)
  | stackItemAtLocation (pToInt r) stack /= CodeAddress Nil =
    let p' = (fromJust . stackItemToInt $ stackItemAtLocation (pToInt r + 1) stack)
        r' = (fromJust . stackItemToInt $ stackItemAtLocation (pToInt r) stack) +<- 1
     in ((b, t, c, r', p'), stack)
  | otherwise =
    ((b, t, c, r, p +<- 1), stack)

backtrackQ :: (AddressRegs, MLStack) -> Zielcode -> (AddressRegs, MLStack)
backtrackQ (regs@(True, _, _, _, _), stack) code = backtrack (regs, stack) code
backtrackQ (regs, stack) code = noBacktrack (regs, stack)

-- Backtrack flag is set to True
backtrack :: (AddressRegs, MLStack) -> Zielcode -> (AddressRegs, MLStack)
backtrack state@(_, stack) code =
  let (regs'@(_, _, c', _, _), stack') = physicalPoppingIfCpNilAndBackjumpNot state
   in if unsafeIsStackNilForRegister c' stack'
        then backtrackCpNil (regs', stack') code
        else backtrackCpNotNil (regs', stack') code

backtrackCpNil :: (AddressRegs, MLStack) -> Zielcode -> (AddressRegs, MLStack)
backtrackCpNil ((b, t, c, r, _), stack) code = ((b, t, c, r, cLast code), stack)

backtrackCpNotNil :: (AddressRegs, MLStack) -> Zielcode -> (AddressRegs, MLStack)
backtrackCpNotNil ((_, t, c, r, _), stack) code =
  ( (False, t, c, r, unsafePointerFromStackAtLocation (pToInt c) stack),
    stackReplaceAtLocation (pToInt c) (CodeAddress $ cNext code c) stack
  )

noBacktrack :: (AddressRegs, MLStack) -> (AddressRegs, MLStack)
noBacktrack ((b, t, c, r, p), stack) = ((b, t, c, r, addPi p 1), stack)

physicalPoppingIfCpNilAndBackjumpNot :: (AddressRegs, MLStack) -> (AddressRegs, MLStack)
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
backtrackQ' :: (AddressRegs, MLStack) -> Zielcode -> (AddressRegs, MLStack)
backtrackQ' (regs@(True, _, _, _, _), stack) code = backtrack' (regs, stack) code
backtrackQ' (regs, stack) code = noBacktrack (regs, stack)

-- Backtrack flag is set to True
backtrack' :: (AddressRegs, MLStack) -> Zielcode -> (AddressRegs, MLStack)
backtrack' state@(_, stack) code =
  let (regs'@(_, _, c', _, _), stack') = physicalPoppingIfCpNilAndBackjumpNot state
   in if unsafeIsStackNilForRegister c' stack'
        then backtrackCpNil' (regs', stack') code
        else backtrackCpNotNil (regs', stack') code

backtrackCpNil' :: (AddressRegs, MLStack) -> Zielcode -> (AddressRegs, MLStack)
backtrackCpNil' ((b, t, c, r, _), stack) code
  | stackItemAtLocation (pToInt c + 3) stack == CodeArg ATNot =
    ((b, t, c, r, unsafePointerFromStackAtLocation (pToInt $ c +<- 2) stack), stack)
  | otherwise =
    ((b, t, c, r, cLast code), stack)

-- Backtrack? für GroundL

-- TODO: Discuss how else to solve this: Since prompt ist the last inStruction, perhaps --       impurely through main?
prompt :: (AddressRegs, MLStack) -> Zielcode -> (AddressRegs, MLStack) -- greedy prompt without IO, temporary solution
prompt reg@((b, t, c, r, p), stack) code =
  if b
    then ((b, t, c, r, Nil), stack) -- should be nil or undefinied, fix by using stack?
    else ((True, t, c, r, addPi p (-1)), stack)

prompt' :: (AddressRegs, MLStack) -> Zielcode -> IO ()
prompt' reg@((b, t, c, r, p), stack) code
  | b = do
    putStrLn "no (more) solutions."
  | otherwise = do
    putStrLn "yes. more?"
    answer <- getLine
    if answer == ";"
      then undefined --evalFromPrompt ((True, t,c,r,p-1), stack) code TODO!!
      else putStrLn "Wrong input, aborting."

{---------------------------------------------------------------------- 
  Hilfsfunktionen für ML 
 ----------------------------------------------------------------------}

-- Funktion zur Linearisierung von Atomen und Variablen 

linearize :: LTerm -> [Atom']
linearize (LTNVar (NVLTerm atom [])) = [Str (atom, 0)]
linearize (LTNVar (NVLTerm atom subatoms)) = [Str (atom, length subatoms)] ++ concatMap linearize subatoms
linearize _ = error "linearize called on non-atom" -- valid?

-- Funktion zum finden einer Kelleradresse 
-- Eventuell Problem, siehe Zulip

type I' = ((B,T,C,R,P,E),Stack StackElement)

sAdd :: I' -> Argument -> Argument -> Pointer 
sAdd regs@((b,t,c,r,p,e),stack) symb ATUnify =  sAddHelper regs (stackItemAtLocation e stack) e 
sAdd ((b,t,Nil,r,p,e),stack) symb ATPush = Nil -- correct?
sAdd regs@((b,t,c,r,p,e), stack) symb ATPush = sAddHelper regs (stackItemAtLocation (c+3) stack) (c+3) 
sAdd _ _ _ = error "something went wrong in s_add"

sAddHelper :: I' -> StackElement -> Pointer -> Pointer    
sAddHelper (reg,stack) (CodeArg (ATVar (Var (name, addr)))) currentLoc = addr
sAddHelper (reg,stack) (CodeArg ATEndEnv) currentLoc = Nil --stand in für stack argument o.ä. => EndEnv Pointer/Stackinhalt
sAddHelper (reg,stack) item currentLoc = sAddHelper (reg,stack) (stackItemAtLocation (currentLoc+1) stack) currentLoc+1

-- Dereferenzierungsfunktion; an welchen Term ist Var gebunden
-- TODO stand in value für richtigen Wert

deref :: Stack StackElement -> (Pointer -> Pointer)  
deref stack addr = 
  let addr2 = Pointer 1 -- FIXME stand in 
  in case (stackItemAtLocation addr stack) of 
    (CodeArg (ATStr _)) -> addr  
    (CodeArg (ATVar _)) -> derefVar --stack addr2 
    _ -> error $ "Deref has to be called on an adress containing an atom or a Variable"  -- set new stack with Var Symb add2; then check add2 for being nil; if yes return addr, if no recurse with add2

-- check first if statement, return addr or flag 
derefVar :: Stack StackElement -> (Pointer -> (Pointer -> Pointer))  
derefVar stack addr addr2 = 
  let stack' =  -- create new stack with item changed
      stackReplaceAtLocation 
      (pToInt addr)
      (CodeArg . ATVar $ Var Symbol addr2) -- FIXME: Wo kommt Symbol her? 
      stack
   in 
     if addr2 == Nil
       then addr
       else deref stack' addr2
derefHelper _ _ _ = error "something went wrong in derefVar" 

-- Aritätsfunktion; can this be called on something other than Var or Atom?

arity :: I -> Pointer -> Arity
arity (regs, stack) addr = 
  case arityHelper (stackItemAtLocation addr stack) of 
    Just x -> x 
    Nothing -> error $ "arity was called on non Symbol Element"

arityHelper :: StackElement -> Maybe Int -- maybe this should be pointer 
arityHelper (CodeArg (ATStr (Str (name, arity)))) = Just arity 
arityHelper (CodeArg (ATVar (Var _))) = Just 0   
arityHelper _ = Nothing  

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
callZielcode :: Command -> (AddressRegs, MLStack) -> Zielcode -> (AddressRegs, MLStack)
callZielcode (Push _ atom) reg code = push atom reg code
callZielcode (Push' _ arg) reg code = push' arg reg code
callZielcode (Unify _ atom) reg _ = unify atom reg
callZielcode (Call _) reg code = call reg code
callZielcode (Backtrack _) reg code = backtrackQ reg code
callZielcode (Return _) reg _ = returnL reg
callZielcode (Return' _ arg) reg _ = returnL' arg reg
callZielcode (Prompt _) reg code = prompt reg code

{- callPrompt':: Command -> (AddressRegs, MLStack) -> Zielcode -> IO()
callPrompt' (Prompt' name inst) reg code = prompt' reg code
callPrompt' _ _ _ = error $ "eval prompt failed." -}

--TODO, for prompt implementation
{- callFromPrompt :: (AddressRegs, MLStack) -> Zielcode -> IO()
callFromPrompt reg (Stack (firstfkt:rest)) = do
   putStrLn "reeval"
   let newreg = callZielcode firstfkt reg (Stack rest)
   prompt newreg code  -}

runner :: (AddressRegs, MLStack) -> Zielcode -> Zielcode -> (AddressRegs, MLStack)
runner reg (Stack (firstfkt : rest)) code = runner (callZielcode firstfkt reg code) (Stack rest) code
runner reg (Stack []) code = reg

-- code :: Zielcode
-- code = codeGen (parse $ tokenize "p :- q. q :- r. r. :- p, r.")

-- initial :: (AddressRegs, MLStack)
-- initial = ((False, Pointer (-1), Nil, Nil, cGoal code), initStack)

-- initStack :: Stack StackElement
-- initStack = stackNewEmpty

module AbstractMachine where

import Control.Exception
import Data.Maybe
import Models
import Parser
import Stack
import Tokenizer

-- TODO: Update Registers in Instruction types (datatype Command)
-- TODO: Make sure all the new instructions like Return' are used
-- TODO: Rewrite Symbol as data Symbol = SymA Atom | SymV Variable
-- TODO: Reorganize signatures: Zielcode -> ... (better currying/partial application)
-- TODO: Reconsider places that used fromJust (unsafe)
-- FIXME: In some places, regs@ refers to the regs and the stack. This is wrong! Fix it.

-- Register
--Instruktionsregister, Int ist Placeholder, kp was das für ein Typ werden wird, habs selber nicht gebraucht (Marco)
type I = Int

--Flagregister
type B = Bool

--AdressRegister
type T = Pointer

type C = Pointer

type R = Pointer

type P = Pointer

type E = Pointer

type Up = Pointer

type Ut = Pointer

type Tt = Pointer

--ZählRegister
type Pc = Int

type Sc = Int

type Ac = Pointer

--Kombination der Register, AddressRegs/Addressreg für MiniL, AddressRegs' ??, FullAddresReg für ML
type AddressRegs = (B, T, C, R, P)

type AddressRegs' = (B, T, C, R, P, Up, E)

-- TODO: Use one register only and fix it everywhere else
type FullAddressreg = (P, T, C, R, E, Up, Ut, Tt, B, Pc, Sc, Ac) -- (Marco)

-- Zielcode is the returntype of L Code Translation
type Zielcode = Stack Command

--Speicherbereiche
type Speicherbereiche = (MLStack, Us, Trail) --Muss erweitert werden mit Env, hab ich aber bisher nicht gebraucht (Marco)

type MLStack = Stack StackElement

type Env = Stack

type Us = Stack StackElement

type Trail = Stack StackElement

--Was den Funktionen übegeben wird
type RegisterKeller = (FullAddressreg, Speicherbereiche)

newtype Atom = A String deriving (Eq) --So habe ich es benutzt (Marco)

newtype Variable' = V String deriving (Eq) --So habe ich es benutzt (Marco)

type Symbol = Atom

type Arity = Int

data Argument
  = ATNot
  | ATNeg
  | ATAtom Atom
  | ATStr Symbol Arity -- Für push (GroundL)
  | ATStr' Atom Arity -- Marco's Vorschlag
  | ATChp -- Für push (GroundL)
  | ATEndAtom
  | ATBegEnv
  | ATEndEnv --data Stack Argument (könnte bspw ENdEnv o.ä. enthalten)
  | -- |
    ATVar Variable
  | ATVar' Variable' Pointer --Marco's Vorschlag, sehe keinen Vorzug ATVar oder ATStr Symbol zu übergeben. Variable' oder Atom reichen aus.
  | ATPush
  | ATUnify
  deriving (Eq, Show)

type Addressreg = (B, T, C, R, P)

{-------------------------
  Datentypen für ML
 ----------------------------}
data Linearization = Linearization String Arity deriving (Eq, Show)

data Exp = ExpLin Linearization | ExpSym Symbol

-- TODO: Consider merging them in a "Symbol" type
newtype Atom' = Str Linearization deriving (Eq)

data Variable = Var String Pointer deriving (Eq)

instance Show Atom' where
  show (Str lin) = "Str " ++ show lin

instance Show Variable where
  show (Var name addr) = "Var " ++ show name ++ show addr

instance Show Variable' where -- Marco's Vorschlag
  show (V str) = str

{-
  Bestehende Datentypen
 -}

--data Stack Argument (könnte bspw ENdEnv o.ä. enthalten)

instance Show Atom where
  show (A str) = str

-- TODO: Merge CodeAtom and Argument (Atom is contained in Argument)
data StackElement
  = CodeAtom Atom
  | CodeAddress Pointer
  | StackAddress Pointer
  | UsAddress Pointer
  | TrailAddress Pointer
  | CodeArg Argument
  deriving (Eq)

instance Show StackElement where
  show (CodeAtom atom) = show atom
  show (CodeAddress Nil) = "nil"
  show (CodeAddress adr) = "c" ++ show adr
  show (StackAddress adr) = "s" ++ show adr
  show (UsAddress adr) = "u" ++ show adr
  show (TrailAddress adr) = "t" ++ show adr
  show (CodeArg arg) = case arg of
    (ATStr sym arityVal) -> show sym ++ "/" ++ show arityVal
    ATNot -> "not"
    ATNeg -> "neg"
    ATPush -> "push"
    ATUnify -> "unify"
    ATChp -> "chp"
    ATBegEnv -> "BegEnv"
    ATEndEnv -> "EndEnv"
    ATEndAtom -> "EndAtom"
    (ATAtom atom) -> show atom
    (ATVar var) -> show var --Placeholder hab ich hingeschrieben, weil kb auf non exhaustive Pattern (Marco) würde diese zwei gerne durch meine unten ersetzen :)
    (ATStr' atom arity) -> concat ["STR", " ", show atom, "/", show arity] -- Marco's Vorschlag
    (ATVar' variable element) -> concat ["VAR", " ", show variable, " ", show element] -- Marco's Vorschlag

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

-- TODO: Use all registers (see next todo)
-- TODO: Update AddressRegs to latest datatype
--       cp. AddressRegs vs. AddressRegs
-- Commands, necessary for having a List of named partially applied functions
data Command
  = Unify (Atom -> (AddressRegs, MLStack) -> (AddressRegs, MLStack)) Atom
  | Unify' (Argument -> RegisterKeller -> RegisterKeller) Argument
  | Push (Atom -> (AddressRegs', MLStack) -> Zielcode -> (AddressRegs', MLStack)) Atom
  | Push' (Argument -> (AddressRegs', MLStack) -> Zielcode -> (AddressRegs', MLStack)) Argument
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

{----------------------------------------------------------
   MiniL; Üb credit: Lukas; angepasst
-----------------------------------------------------------}

codeGen :: Tree -> Zielcode
codeGen parsetree = üb parsetree (Stack [])

-- TODO: Check if commands are added in the right order (Stack is LIFO/FILO)
üb :: Tree -> Zielcode -> Zielcode
-- If there are no Programmklauseln
üb (TP (Programm [] (Ziel lits))) akk = üb (TZ (Ziel lits)) akk
-- If there are Programmklauseln
üb (TP (Programm klauseln@(pklausel : pklauseln) (Ziel lits))) akk
  | null pklauseln = üb (TZ (Ziel lits)) $ üb (TPk pklausel) akk
  | otherwise = üb (TP (Programm pklauseln (Ziel lits))) $ üb (TPk pklausel) akk
-- Üb(Atom.)
üb (TPk (Pk1 atom)) akk = übHead atom akk <> Stack [Return returnL]
-- Üb(Atom :- Seq)
üb (TPk (Pk2 atom (Ziel seq))) akk =
  let akk' = übHead atom akk
   in übBody seq akk' <> Stack [Return returnL]
üb (TZ (Ziel literals)) akk = übBody literals akk <> Stack [Prompt prompt]
üb _ akk = error $ "Failure in :- Seq translation." ++ show akk

-- übHead(Atom.)
übHead :: NVLTerm -> (Zielcode -> Zielcode)
übHead atom@(NVLTerm _ _) = übUnify [ExpLin $ linearize atom]

-- TODO: Instead of using let, create separate functions
übBody :: [Literal] -> Zielcode -> Zielcode
-- ÜbBody([not Atom | Sequenz])
übBody ((Literal False (LTNVar atom)) : seq) akk =
  übBody
    seq
    $ übPush
      [ExpLin $ linearize atom]
      (akk <> Stack [Push' push'' ATNot, Push' push'' ATChp])
      <> Stack
        [ Push' push'' ATEndAtom,
          Call call,
          Backtrack backtrackQ',
          Return' returnL' ATNeg,
          Backtrack backtrackQ'
        ]
-- Üb_Body([Atom | Sequenz])
übBody ((Literal _ (LTNVar atom)) : seq) akk =
  übBody
    seq
    $ übPush [ExpLin $ linearize atom] (akk <> Stack [Push' push'' ATChp])
      <> Stack [Push' push'' ATEndAtom, Call call, Backtrack backtrackQ']
übBody [] akk = akk
übBody _ _ = error "Failure in übBody."

übEnv :: [Atom] -> Stack Command -> Stack Command
übEnv [] akk = akk
-- ÜbEnv([Symbol|Sequenz])
übEnv ((A sym) : seq) akk =
  übEnv seq (akk <> Stack [Push' push'' (ATVar' (V sym) Nil)])
    <> Stack [Push' push'' ATEndEnv]

-- -- Üb_Body([not Atom | Sequenz]): Negation durch Scheitern
-- übBody ((Literal False (LTNVar (NVLTerm atom _))) : seq) akk =
--   let akk' =
--         akk
--           <> Stack
--             [ Push' push'' ATNot,
--               Push' push'' (ATAtom $ A atom),
--               Call call,
--               Backtrack backtrackQ',
--               Return' returnL' ATNeg,
--               Backtrack backtrackQ'
--             ]
--    in übBody seq akk'

übPush :: [Exp] -> Zielcode -> Zielcode
-- ÜbPush([])
übPush [] akk = akk
übPush [ExpSym (A sym)] akk = akk <> Stack [Push' push'' (ATVar' (V sym) Nil)]
-- ÜbPush(Symbol/Arity)
übPush [ExpLin (Linearization sym arity)] akk =
  akk <> Stack [Push' push'' $ ATStr (A sym) arity]
-- ÜbPush([Exp | Sequenz])
übPush (exp : seq) akk = übPush seq $ übPush [exp] akk

übUnify :: [Exp] -> Zielcode -> Zielcode
-- übUnify(Symbol/Arity)
übUnify [ExpLin (Linearization sym arity)] akk =
  akk <> Stack [Unify' unify' (ATStr (A sym) arity)]
übUnify [ExpSym (A sym)] akk =
  akk <> Stack [Unify' unify' (ATVar' (V sym) Nil)]
-- übUnify([Exp | Sequenz])
übUnify (exp : seq) akk =
  übUnify seq $ übUnify [exp] akk <> Stack [Backtrack backtrackQ']
-- übUnify([])
übUnify [] akk = akk

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
push'' :: Argument -> ((AddressRegs', MLStack) -> (Zielcode -> (AddressRegs', MLStack)))
-- push Str Symbol Arity
push'' arg@(ATStr sym arity) ((b, t, c, r, p, up, e), stack) _ =
  ( (b, t +<- 1, c, r, p +<- 1, up, e),
    stackReplaceAtLocation
      (pToInt $ t +<- 1)
      (CodeArg arg)
      stack
  )
-- Push CHP
-- TODO: UP Register
push'' ATChp ((b, t, c, r, p, up, e), stack) code =
  ( (b, t +<- 7, t +<- 1, t +<- 2, p +<- 1, t + 7, e),
    stackReplaceAtLocation
      (pToInt $ t +<- 2)
      (CodeAddress c)
      ( stackReplaceAtLocation
          (pToInt $ t +<- 1)
          (CodeAddress $ cFirst code)
          stack
      )
  )
push'' ATEndAtom ((b, t, c, r, p, up, e), stack) _ =
  ( (b, t, c, r, p +<- 1, up, e),
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

-- lin(Atom) -> Linearisierung
linearize :: NVLTerm -> Linearization
linearize (NVLTerm atom []) = Linearization atom 0
linearize (NVLTerm atom subatoms) = Linearization atom $ length subatoms

-- Funktion zum finden einer Kelleradresse
-- Eventuell Problem, siehe Zulip

type I' = ((B, T, C, R, P, E), Stack StackElement) -- Kann entfernt werden oder ? (Marco)

sAdd :: RegisterKeller -> Argument -> Argument -> Pointer
sAdd all@(addressreg@(p, t, c, r, e, up, ut, tt, b, pc, sc, ac), (stack, us, trail)) symb ATUnify = sAddHelper all (stackItemAtLocation e stack) e
sAdd all@(addressreg@(p, t, Nil, r, e, up, ut, tt, b, pc, sc, ac), (stack, us, trail)) symb ATPush = Nil -- correct?
sAdd all@(addressreg@(p, t, c, r, e, up, ut, tt, b, pc, sc, ac), (stack, us, trail)) symb ATPush = sAddHelper all (stackItemAtLocation (c + 3) stack) (c + 3)
sAdd _ _ _ = error "something went wrong in s_add"

sAddHelper :: RegisterKeller -> StackElement -> Pointer -> Pointer
sAddHelper (reg, stacks@(stack, us, trail)) (CodeArg (ATVar (Var name addr))) currentLoc = addr
sAddHelper (reg, stacks@(stack, us, trail)) (CodeArg ATEndEnv) currentLoc = Nil --stand in für stack argument o.ä. => EndEnv Pointer/Stackinhalt
sAddHelper (reg, stacks@(stack, us, trail)) item currentLoc = sAddHelper (reg, stacks) (stackItemAtLocation (currentLoc + 1) stack) currentLoc + 1

-- Dereferenzierungsfunktion; an welchen Term ist Var gebunden
-- TODO stand in value für richtigen Wert

deref :: MLStack -> (Pointer -> Pointer)
deref stack addr =
  case stackItemAtLocation addr stack of
    (CodeArg (ATStr _ _)) -> addr
    stackItemVar@(CodeArg (ATVar (Var _ addr2))) ->
      derefVar stack addr addr2 stackItemVar
    _ -> error "Should have not been reachable: contained neither ATStr or ATVar"

derefVar :: MLStack -> Pointer -> Pointer -> StackElement -> Pointer
derefVar stack addr addr2 stackItemVar =
  let stack' = stackReplaceAtLocation (pToInt addr) stackItemVar stack
   in if isPNil addr2 then addr else deref stack' addr2

-- Aritätsfunktion; can this be called on something other than Var or Atom?

arity :: MLStack -> Pointer -> Arity
arity stack addr =
  case arityHelper (stackItemAtLocation addr stack) of
    Just x -> x
    Nothing -> error "arity was called on non Symbol Element"

arityHelper :: StackElement -> Maybe Int -- maybe this should be pointer
arityHelper (CodeArg (ATStr name arityVal)) = Just arityVal
arityHelper (CodeArg (ATVar (Var _ _))) = Just 0
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

{--------------------------------------------------------------------
              ML Unify Hilffunktionen
---------------------------------------------------------------------}

--Makroinstruktionen
addAC :: Int -> FullAddressreg -> FullAddressreg
addAC n adressreg@(p, t, c, r, e, up, ut, tt, b, pc, sc, ac) = case ac of
  Pointer i -> (p, t, c, r, e, up, ut, tt, b, pc, sc, ac +<- n)
  Nil -> adressreg

restoreAcUpQ :: Us -> FullAddressreg -> FullAddressreg
restoreAcUpQ us adressreg@(p, t, c, r, e, up, ut, tt, b, pc, sc, ac)
  | ac == Pointer 0 = (p, t, c, r, e, unsafePointerFromStackAtLocation (pToInt ut) us, ut -<- 2, tt, b, pc, sc, unsafePointerFromStackAtLocation (pToInt (ut -<- 1)) us)
  | otherwise = adressreg

saveAcUpQ :: RegisterKeller -> RegisterKeller
saveAcUpQ all@(addressreg@(p, t, c, r, e, up, ut, tt, b, pc, sc, ac), (stack, us, trail))
  | up <= unsafePointerFromStackAtLocation (pToInt (c +<- 5)) stack
      && deref stack up /= up
      && getArity (stackItemAtLocation (pToInt (deref stack up)) stack) /= 0 =
    ( (p, t, c, r, e, deref stack (up +<- 1), ut +<- 2, tt, b, pc, sc, 0),
      ( stack,
        us <> Stack [StackAddress ac, StackAddress (up +<- 1)],
        trail
      )
    )
  | otherwise = all

{--------------------------------------------------------------------
              ML Unify
---------------------------------------------------------------------}

unify' :: Argument -> RegisterKeller -> RegisterKeller
unify' arg all@(addressreg@(p, t, c, r, e, up, ut, tt, b, pc, sc, ac), (stack, us, trail))
  | pc >= 1 = unifyPushModus arg all
  | otherwise = unifyNonPushModus arg all

unifyPushModus :: Argument -> RegisterKeller -> RegisterKeller
unifyPushModus arg all@(addressreg@(p, t, c, r, e, up, ut, tt, b, pc, sc, ac), (stack, us, trail)) = case arg of
  ATStr' atom ar -> (((p -<- 1) +<- getArity (CodeArg arg), t +<- 1, c, r, e, up, ut, tt, b, pc, sc, ac), (stack <> Stack [CodeArg arg], us, trail))
  ATVar' var add -> (((p -<- 1) +<- getArity (CodeArg arg), t +<- 1, c, r, e, up, ut, tt, b, pc, sc, ac), (stack <> Stack [CodeArg (ATVar' var (sAdd all arg ATUnify))], us, trail))
  _ -> error "Mitgegebenes Argument für PushModus muss Lineares Atom oder eine Variable sein"

-- TODO: Refactor this. This is abnormous and beyond the possibility of understanding
unifyNonPushModus :: Argument -> RegisterKeller -> RegisterKeller
unifyNonPushModus arg all@(addressreg@(p, t, c, r, e, up, ut, tt, b, pc, sc, ac), (stack, us, trail)) = case arg of
  (ATStr' (A str) arity) ->
    if sameSymbol str all
      then
        let (p', t', c', r', e', up', ut', tt', b', pc', sc', ac') = restoreAdd arity all
         in ((p', t', c', r', e', up' +<- 1, ut', tt', b', pc', sc', ac'), (stack <> Stack [CodeArg arg], us, trail <> Stack [TrailAddress (deref stack up)]))
      else
        let (CodeArg (ATVar' symb add)) = getCodeArgFromStack all
         in if V str /= symb || Pointer arity /= add
              then ((p, t, c, r, e, up, ut, tt, True, pc, sc, ac), (stack, us, trail))
              else
                let (p', t', c', r', e', up', ut', tt', b', pc', sc', ac') = arityValue arity all
                 in saveAcUpQ ((p' +<- 1, t', c', r', e', up' +<- 1, ut', tt', b', pc', sc', ac'), (stack, us, trail))
  (ATVar' var add) ->
    let (adressreg'@(p', t', c', r', e', up', ut', tt', b', pc', sc', ac'), (stack', us', trail')) =
          if sameSymbolButNil arg var all
            then
              let element@(CodeArg (ATVar' symb up)) = stackItemAtLocation (pToInt (derefsAddu arg all)) stack
               in scGreaterOne ((p, t, c, r, e, up, ut, tt +<- 1, b, pc, arityUP all, ac), (replaceStack element all, us, trail <> Stack [TrailAddress (derefsAddu arg all)]))
            else
              let all'@((p', t', c', r', e', up', ut', tt', b', pc', sc', ac'), (stack', us', trail')) = ((p, t, c, r, e, up, ut +<- 1, tt, b, pc, sc, ac), (stack, us <> Stack [StackAddress t], trail))
               in ((p', pointerFromUsAt ut' us', c', r', e', up', ut' -<- 1, tt', not (unification (derefsAddu arg all') up all'), pc', sc', ac'), (stack', us', trail'))
     in (up1 $ restoreAcUpQ us' $ addAC (-1) adressreg', (stack', us', trail'))
  _ -> error "Mitgegebenes Argument für NonPush-Modus muss Lineares Atom oder eine Variable sein"

-- ML Unify Teilfunktionen
restoreAdd :: Arity -> RegisterKeller -> FullAddressreg
restoreAdd arity all@(addressreg@(p, t, c, r, e, up, ut, tt, b, pc, sc, ac), (stack, us, trail)) = restoreAcUpQ us (addAC (-1) (p, t +<- 1, c, r, e, up, ut, tt +<- 1, b, arity, sc, ac))

getCodeArgFromStack :: RegisterKeller -> StackElement
getCodeArgFromStack all@(addressreg@(p, t, c, r, e, up, ut, tt, b, pc, sc, ac), (stack, us, trail)) = stackItemAtLocation (pToInt (deref stack up)) stack

sameSymbol :: String -> RegisterKeller -> Bool
sameSymbol str all@(addressreg@(p, t, c, r, e, up, ut, tt, b, pc, sc, ac), (stack, us, trail)) = stackItemAtLocation (pToInt (deref stack up)) stack == CodeArg (ATVar' (V str) Nil)

sameSymbolButNil :: Argument -> Variable' -> RegisterKeller -> Bool
sameSymbolButNil arg var all@(addressreg@(p, t, c, r, e, up, ut, tt, b, pc, sc, ac), all2@(stack, us, trail)) = stackItemAtLocation (pToInt (derefsAddu arg all)) stack == CodeArg (ATVar' var Nil)

arityValue :: Arity -> RegisterKeller -> FullAddressreg
arityValue arity all@(addressreg@(p, t, c, r, e, up, ut, tt, b, pc, sc, ac), (stack, us, trail)) =
  if arity >= 1
    then restoreAcUpQ us $ addAC arity addressreg
    else restoreAcUpQ us $ addAC (-1) addressreg

arityUP :: RegisterKeller -> Int
arityUP all@(addressreg@(p, t, c, r, e, up, ut, tt, b, pc, sc, ac), (stack, us, trail)) = getArity (stackItemAtLocation (pToInt up) stack)

derefsAddu :: Argument -> RegisterKeller -> Pointer
derefsAddu arg all@(addressreg@(p, t, c, r, e, up, ut, tt, b, pc, sc, ac), (stack, us, trail)) = deref stack (sAdd all arg ATUnify)

scGreaterOne :: RegisterKeller -> RegisterKeller
scGreaterOne all@(addressreg@(p, t, c, r, e, up, ut, tt, b, pc, sc, ac), all2@(stack, us, trail)) = if sc >= 1 then scGreaterOne ((p, t, c, r, e, up +<- 1, ut, tt, b, pc, (sc -1) + arityUP all, ac), all2) else all

replaceStack :: StackElement -> RegisterKeller -> MLStack
replaceStack element@(CodeArg arg) all@(addressreg@(p, t, c, r, e, up, ut, tt, b, pc, sc, ac), (stack, us, trail)) = stackReplaceAtLocation (pToInt (derefsAddu arg all)) element stack
replaceStack _ _ = error "Dont need the other StackElements"

up1 :: FullAddressreg -> FullAddressreg
up1 (p, t, c, r, e, up, ut, tt, b, pc, sc, ac) = (p, t, c, r, e, up +<- 1, ut, tt, b, pc, sc, ac)

pointerFromUsAt :: Pointer -> Us -> Pointer
pointerFromUsAt ut = unsafePointerFromStackAtLocation (pToInt ut)

getArity :: StackElement -> Int
getArity (CodeArg (ATStr' _ arity)) = arity
getArity (CodeArg (ATVar' _ _)) = 0
getArity _ = error "What"

--Dummy sAdd for no errors
--sAdd :: Argument -> t0 -> RegisterKeller -> Pointer
--sAdd = error "not implemented"

unification :: Pointer -> Pointer -> RegisterKeller -> Bool
unification add1 add2 all@(addressreg@(p, t, c, r, e, up, ut, tt, b, pc, sc, ac), (stack, us, trail)) = undefined
module AbstractMachine where

import Control.Exception
import Data.Maybe
import Models
import Parser
import Stack
import Tokenizer

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

type AddressRegs = (B, T, C, R, P, Up, E, Ut, Tt, Pc, Sc, Ac)

-- Zielcode is the returntype of L Code Translation
type Zielcode = Stack Command

-- Speicherbereiche
-- TODO: Muss erweitert werden mit Env
type Speicherbereiche = (MLStack, Us, Trail)

type MLStack = Stack StackElement

type Env = Stack

type Us = Stack StackElement

type Trail = Stack StackElement

--Was den Funktionen übegeben wird

type RegisterKeller = (AddressRegs, Speicherbereiche)

newtype Atom = A String deriving (Eq)

newtype Variable = V String deriving (Eq)

type Arity = Int

data Argument
  = ATNot
  | ATNeg
  | ATPos
  | ATAtom Atom
  | ATStr Atom Arity
  | ATChp -- Für push (GroundL)
  | ATEndAtom
  | ATBegEnv
  | ATEndEnv Int
  | ATVar Variable Pointer
  | ATPush
  | ATUnify
  deriving (Eq, Show)

{-------------------------
  Datentypen für ML
 ----------------------------}
data Linearization = Linearization String Arity deriving (Eq, Show)

data Exp = ExpLin Linearization | ExpSym Atom

instance Show Variable where
  show (V str) = str

{----------------------------------------
  Bestehende Datentypen
 -----------------------------------------}

--data Stack Argument (könnte bspw ENdEnv o.ä. enthalten)

instance Show Atom where
  show (A str) = str

-- Data type that covers all types needed for the code stack of the abstract machine
data StackElement
  = CodeAddress Pointer
  | StackAddress Pointer
  | UsAddress Pointer
  | TrailAddress Pointer
  | CodeArg Argument
  deriving (Eq)

instance Show StackElement where
  show (CodeAddress Nil) = "nil"
  show (CodeAddress adr) = "c" ++ show adr
  show (StackAddress adr) = "s" ++ show adr
  show (UsAddress adr) = "u" ++ show adr
  show (TrailAddress adr) = "t" ++ show adr
  show (CodeArg arg) = case arg of
    ATNot -> "not"
    ATNeg -> "neg"
    ATPos -> "pos"
    ATPush -> "push"
    ATUnify -> "unify"
    ATChp -> "chp"
    ATBegEnv -> "BegEnv"
    (ATEndEnv n) -> "EndEnv " ++ show n
    ATEndAtom -> "EndAtom"
    (ATAtom atom) -> show atom
    (ATStr atom arity) -> concat ["STR", " ", show atom, "/", show arity]
    (ATVar variable element) -> concat ["VAR", " ", show variable, " ", show element]

--helper
stackItemToInt :: StackElement -> Maybe Pointer
stackItemToInt (CodeAddress x) = Just x
stackItemToInt (StackAddress x) = Just x
stackItemToInt (UsAddress x) = Just x
stackItemToInt (TrailAddress x) = Just x
stackItemToInt _ = Nothing

-- Unsafe operation that gets the pointer from Stack stack at location i.
-- Can fail if i is out of range or if the item is no Pointer <=> Nothing (fromJust fails)
unsafePointerFromStackAtLocation :: Pointer -> Stack StackElement -> Pointer
unsafePointerFromStackAtLocation i stack =
  fromJust . stackItemToInt $ stackItemAtLocation i stack

safePointerFromStackAtLocation :: Pointer -> Stack StackElement -> Pointer
safePointerFromStackAtLocation addr stack =
  fromMaybe Nil (stackItemToInt $ stackItemAtLocation addr stack)

-- Commands, necessary for having a List of named partially applied functions
data Command
  = Unify (Argument -> RegisterKeller -> RegisterKeller) Argument
  | Push (Argument -> (RegisterKeller -> Zielcode -> RegisterKeller)) Argument
  | Call (RegisterKeller -> Zielcode -> RegisterKeller)
  | Return (Argument -> RegisterKeller -> RegisterKeller) Argument
  | Backtrack (RegisterKeller -> Zielcode -> RegisterKeller)
  | Prompt (RegisterKeller -> Zielcode -> IO ())

instance Show Command where
  show (Unify _ args) = "unifyML " ++ show args
  show (Push _ args) = "pushML " ++ show args
  show (Call _) = "callML"
  show (Return _ args) = "returnML " ++ show args
  show (Backtrack _) = "backtrackML"
  show (Prompt _) = "promptML"

instance Eq Command where
  (==) (Unify _ expr1) (Unify _ expr2) = expr1 == expr2
  (==) (Push _ expr1) (Push _ expr2) = expr1 == expr2
  (==) (Call _) (Call _) = True
  (==) (Backtrack _) (Backtrack _) = True
  (==) (Return _ arg1) (Return _ arg2) = arg1 == arg2
  (==) (Prompt _) (Prompt _) = True
  (==) _ _ = False

{----------------------------------------------------------
   Translations
-----------------------------------------------------------}

codeGen :: Tree -> Zielcode
codeGen parsetree = üb parsetree (Stack [])

-- Main translation function.
-- Takes a parse tree and tries to generate a so called "Zielcode".
-- The latter is a Stack of Commands, such as push and backtrack.
-- TODO: Check if commands are added in the right order (Stack is LIFO/FILO)
üb :: Tree -> Zielcode -> Zielcode
--ML

--Üb(VarSeq, :- Sequenz.)
üb (TP (Programm' [] (varSeq, Ziel literals))) akk =
  übBody literals (übEnv (map V varSeq) (akk <> Stack [Push push ATBegEnv])) <> Stack [Prompt prompt]
--Üb(VarSeq, Atom :- Sequenz.)
üb (TP (Programm' ((varSeq, Pk2 atom (Ziel literals)) : rest) ziel)) akk =
  üb
    (TP (Programm' rest ziel))
    (übBody literals (übHead atom (übEnv (map V varSeq) (akk <> Stack [Push push ATBegEnv]))) <> Stack [Return returnL ATPos])
--Üb(VarSeq, Atom.)
üb (TP (Programm' ((varSeq, Pk1 atom) : rest) ziel)) akk =
  üb
    (TP (Programm' rest ziel))
    (übHead atom (übEnv (map V varSeq) (akk <> Stack [Push push ATBegEnv])) <> Stack [Return returnL ATPos])
--MiniL/GroundL
-- If there are no Programmklauseln
üb (TP (Programm [] (Ziel lits))) akk = üb (TZ (Ziel lits)) akk
-- If there are Programmklauseln
üb (TP (Programm klauseln@(pklausel : pklauseln) (Ziel lits))) akk
  | null pklauseln = üb (TZ (Ziel lits)) $ üb (TPk pklausel) akk
  | otherwise = üb (TP (Programm pklauseln (Ziel lits))) $ üb (TPk pklausel) akk
-- Üb(Atom.)
üb (TPk (Pk1 atom)) akk = übHead atom akk <> Stack [Return returnL ATPos]
-- Üb(Atom :- Seq)
üb (TPk (Pk2 atom (Ziel seq))) akk =
  let akk' = übHead atom akk
   in übBody seq akk' <> Stack [Return returnL ATPos]
üb (TZ (Ziel literals)) akk = übBody literals akk <> Stack [Prompt prompt]
üb _ akk = error $ "Failure in :- Seq translation." ++ show akk

-- übHead(Atom.)
übHead :: NVLTerm -> (Zielcode -> Zielcode)
übHead atom@(NVLTerm _ _) = übUnify [ExpLin $ linearize atom]

übBody :: [Literal] -> Zielcode -> Zielcode
-- ÜbBody([not Atom | Sequenz])
übBody ((Literal False (LTNVar nvlt@(NVLTerm atom subatoms))) : seq) akk =
  übBody
    seq
    $ übPush
      [ExpLin $ linearize nvlt]
      (akk <> Stack [Push push ATNot, Push push ATChp])
      <> Stack
        [ Push push ATEndAtom,
          Call call,
          Backtrack backtrack,
          Return returnL ATNeg,
          Backtrack backtrack
        ]
-- Üb_Body([Atom | Sequenz])
übBody ((Literal _ (LTNVar nvlt@(NVLTerm atom subatoms))) : seq) akk =
  übBody
    seq
    $ übPush [ExpLin $ linearize nvlt] (akk <> Stack [Push push ATChp])
      <> Stack [Push push ATEndAtom, Call call, Backtrack backtrack]
übBody [] akk = akk
übBody _ _ = error "Failure in übBody."

übEnv :: [Variable] -> Stack Command -> Stack Command
übEnv var = übEnvHelper var $ length var

type VariableCount = Int

übEnvHelper :: [Variable] -> VariableCount -> Stack Command -> Stack Command
übEnvHelper [] n akk = akk <> Stack [Push push $ ATEndEnv n]
übEnvHelper (var : seq) n akk =
  übEnvHelper seq n (akk <> Stack [Push push (ATVar var Nil)])

übPush :: [Exp] -> Zielcode -> Zielcode
-- ÜbPush([])
übPush [] akk = akk
übPush [ExpSym (A sym)] akk = akk <> Stack [Push push (ATVar (V sym) Nil)]
-- ÜbPush(Symbol/Arity)
übPush [ExpLin (Linearization sym arity)] akk =
  akk <> Stack [Push push $ ATStr (A sym) arity]
-- ÜbPush([Exp | Sequenz])
übPush (exp : seq) akk = übPush seq $ übPush [exp] akk

übUnify :: [Exp] -> Zielcode -> Zielcode
-- übUnify(Symbol/Arity)
übUnify [ExpLin (Linearization sym arity)] akk =
  akk <> Stack [Unify unify (ATStr (A sym) arity)]
übUnify [ExpSym (A sym)] akk =
  akk <> Stack [Unify unify (ATVar (V sym) Nil)]
-- übUnify([Exp | Sequenz])
übUnify (exp : seq) akk =
  übUnify seq $ übUnify [exp] akk <> Stack [Backtrack backtrack]
-- übUnify([])
übUnify [] akk = akk

{--------------------------------------------------------------
   Instruktionen
 ---------------------------------------------------------------}

-- Push für GroundL
push :: Argument -> (RegisterKeller -> (Zielcode -> RegisterKeller))
-- push Str Symbol Arity
push
  arg@(ATStr (A sym) arity)
  ( (b, t, c, r, p, up, e, ut, tt, pc, sc, ac),
    (stack, us, trail)
    )
  _ =
    ( (b, t +<- 1, c, r, p +<- 1, up, e, ut, tt, pc, sc, ac),
      ( stackReplaceAtLocation
          (t +<- 1)
          (CodeArg arg)
          stack,
        us,
        trail
      )
    )
-- Push CHP
push ATChp ((b, t, c, r, p, up, e, ut, tt, pc, sc, ac), (stack, us, trail)) code =
  ( (b, t +<- 7, t +<- 1, t +<- 2, p +<- 1, t + 7, e, ut, tt, pc, sc, ac),
    ( stackReplaceAtLocation
        (t +<- 2)
        (CodeAddress c)
        ( stackReplaceAtLocation
            (t +<- 1)
            (CodeAddress $ cFirst code)
            stack
        ),
      us,
      trail
    )
  )
push ATBegEnv ((b, t, c, r, p, up, e, ut, tt, pc, sc, ac), (stack, us, trail)) _ =
  ((b, t, c, r, p, up, Nil, ut, tt, pc, sc, ac), (stack, us, trail))
push
  var@(ATVar sym _)
  rs@((b, t, c, r, p, up, e, ut, tt, pc, sc, ac), (stack, us, trail))
  _ =
    ( (b, t +<- 1, c, r, p, up, e, ut, tt, pc, sc, ac),
      ( stackReplaceAtLocation
          (pToInt $ t +<- 1)
          (CodeArg $ ATVar sym (sAdd rs var ATPush))
          stack,
        us,
        trail
      )
    )
push ATEndAtom ((b, t, c, r, p, up, e, ut, tt, pc, sc, ac), (stack, us, trail)) _ =
  ( (b, t, c, r, p +<- 1, up, e, ut, tt, pc, sc, ac),
    ( stackReplaceAtLocation
        (c +<- 5)
        (CodeAddress t)
        ( stackReplaceAtLocation
            (c +<- 2)
            (CodeAddress $ p +<- 3)
            stack
        ),
      us,
      trail
    )
  )
push (ATEndEnv n) (regs@(_, t, c, _, p, _, _, _, _, _, _, _), (stack, us, trail)) _ =
  ( regs,
    ( stackReplaceAtLocation (c +<- 5) (CodeAddress t) $
        stackReplaceAtLocation (c +<- 2) (CodeAddress $ p +<- 3) stack,
      us,
      trail
    )
  )
push _ _ _ = error "Case not covered by GroundL pattern matching for push."

-- ML call Befehl
call :: RegisterKeller -> Zielcode -> RegisterKeller
call ((b, t, c, r, p, up, e, ut, tt, pc, sc, ac), stacks@(stack, us, trail)) code =
  if stackItemAtLocation c stack == CodeAddress Nil
    then ((True, t, c, r, p +<- 1, up, e, ut, tt, pc, sc, ac), stacks)
    else
      let p' = safePointerFromStackAtLocation c stack
          stacks' =
            ( stackWriteToLocation
                c
                (CodeAddress (cNext code (safePointerFromStackAtLocation c stack)))
                stack,
              us,
              trail
            )
       in ((b, t, c, r, p', up, e, ut, tt, pc, sc, ac), stacks')

-- Return für ML

returnL :: Argument -> RegisterKeller -> RegisterKeller
returnL ATNeg regkeller = returnLNeg regkeller
returnL ATPos regkeller = returnLPos regkeller
returnL _ _ = error "returnL resulted in an error. Possible use of wrong argument."

returnLPos :: RegisterKeller -> RegisterKeller
returnLPos ((b, t, c, r, p, up, e, ut, tt, pc, sc, ac), (stack, us, trail)) =
  let p' = safePointerFromStackAtLocation (r +<- 1) stack
      e' = safePointerFromStackAtLocation (r +<- 2) stack
   in if stackItemAtLocation r stack /= CodeAddress Nil
        then
          ( (b, t, c, safePointerFromStackAtLocation r stack +<- 1, p', up, e', ut, tt, pc, sc, ac),
            (stack, us, trail)
          )
        else ((b, t, c, r, p', up, e', ut, tt, pc, sc, ac), (stack, us, trail))

returnLNeg :: RegisterKeller -> RegisterKeller
returnLNeg ((b, t, c, r, p, up, e, ut, tt, pc, sc, ac), (stack, us, trail)) =
  ((False, t, c, r, p, up, e, up, tt, pc, sc, ac), (stackWriteToLocation (r -<- 1) (CodeAddress Nil) stack, us, trail))

-- Backtrack? für GroundL
backtrack :: RegisterKeller -> Zielcode -> RegisterKeller
backtrack all@((b, t, c, r, p, up, e, ut, tt, pc, sc, ac), register@(stack, us, trail)) code
  | b =
    backtrackAfterSchleife
      ( backtrackISchleife
          (safePointerFromStackAtLocation (c +<- 4) stack +<- 1)
          (backtrackAfterWhile (backtrackWhile all))
      )
      code
  | otherwise = ((b, t, c, r, p +<- 1, up, e, ut, tt, pc, sc, ac), register)

backtrackWhile :: RegisterKeller -> RegisterKeller
backtrackWhile all@((b, t, c, r, p, up, e, ut, tt, pc, sc, ac), stacks@(stack, us, trail))
  | backtrackCNilRnotNil all =
    backtrackWhile
      ( ( b,
          t,
          safePointerFromStackAtLocation r stack,
          safePointerFromStackAtLocation r stack +<- 1,
          p,
          up,
          e,
          ut,
          tt,
          pc,
          sc,
          ac
        ),
        stacks
      )
  | otherwise = all

backtrackAfterWhile :: RegisterKeller -> RegisterKeller
backtrackAfterWhile
  ((b, t, c, r, p, up, e, ut, tt, pc, sc, ac), stacks@(stack, us, trail)) =
    ((b, safePointerFromStackAtLocation (c +<- 5) stack, c, r, p, c +<- 6, safePointerFromStackAtLocation (c +<- 5) stack +<- 1, Pointer 0, tt, 0, sc, Nil), stacks)

backtrackCNilRnotNil :: RegisterKeller -> Bool
backtrackCNilRnotNil ((b, t, c, r, p, up, e, ut, tt, pc, sc, ac), (stack, us, trail)) =
  safePointerFromStackAtLocation c stack == Nil
    && safePointerFromStackAtLocation r stack /= Nil

backtrackISchleife :: Pointer -> RegisterKeller -> RegisterKeller
backtrackISchleife i all@((b, t, c, r, p, up, e, ut, tt, pc, sc, ac), (stack, us, trail))
  | i <= tt = backtrackISchleife (i +<- 1) (backtrackISchleifeIf i all)
  | otherwise = all

backtrackISchleifeIf :: Pointer -> RegisterKeller -> RegisterKeller
backtrackISchleifeIf i all@(register@(b, t, c, r, p, up, e, ut, tt, pc, sc, ac), (stack, us, trail))
  | safePointerFromStackAtLocation i trail <= t =
    let (CodeArg (ATVar symbol add)) = stackItemAtLocation (safePointerFromStackAtLocation i trail) stack
     in (register, (stackReplaceAtLocation (safePointerFromStackAtLocation i trail) (CodeArg (ATVar symbol Nil)) stack, us, trail))
  | otherwise = all

backtrackAfterSchleife :: RegisterKeller -> Zielcode -> RegisterKeller
backtrackAfterSchleife
  all@(register@(b, t, c, r, p, up, e, ut, tt, pc, sc, ac), stacks@(stack, us, trail)) =
    backtrackIfThenElse ((b, t, c, r, p, up, e, ut, safePointerFromStackAtLocation (c +<- 4) stack, pc, sc, ac), stacks)

backtrackIfThenElse :: RegisterKeller -> Zielcode -> RegisterKeller
backtrackIfThenElse
  all@(register@(b, t, c, r, p, up, e, ut, tt, pc, sc, ac), stacks@(stack, us, trail))
  code =
    if safePointerFromStackAtLocation c stack == Nil
      then ((b, t, c, r, cLast code, up, e, ut, tt, pc, sc, ac), stacks)
      else ((False, t, c, r, safePointerFromStackAtLocation c stack, up, e, ut, tt, pc, sc, ac), (backtrackReplace all code, us, trail))

backtrackReplace :: RegisterKeller -> Zielcode -> MLStack
backtrackReplace
  all@(register@(b, t, c, r, p, up, e, ut, tt, pc, sc, ac), stacks@(stack, us, trail))
  code =
    stackReplaceAtLocation c (CodeAddress $ cNext code (safePointerFromStackAtLocation c stack)) stack

-- Prompt für ML

prompt :: RegisterKeller -> Zielcode -> IO ()
prompt ((b, t, c, r, p, up, e, ut, tt, pc, sc, ac), (stack, us, trail)) code
  | b = putStrLn "no (more) solutions"
  | otherwise = do
    putStrLn $ display stack
    putStrLn "more?"
    answer <- getLine
    if answer == ";"
      then callFromPrompt ((True, t, c, r, p -<- 1, up, e, ut, tt, pc, sc, ac), (stack, us, trail)) code
      else print "Wrong input, aborting."

{----------------------------------------------------------------------
  Hilfsfunktionen für ML
 ----------------------------------------------------------------------}

-- Funktion zur Linearisierung von Atomen und Variablen

-- lin(Atom) -> Linearisierung
linearize :: NVLTerm -> Linearization
linearize (NVLTerm atom []) = Linearization atom 0
linearize (NVLTerm atom subatoms) = Linearization atom $ length subatoms

-- Funktion zum finden einer Kelleradresse
-- TODO Eventuell Problem, siehe Zulip; maybe refactor using takeWhile

sAdd :: RegisterKeller -> Argument -> Argument -> Pointer
sAdd
  all@(addressreg@(b, t, c, r, p, up, e, ut, tt, pc, sc, ac), (stack, us, trail))
  symb
  ATUnify = sAddHelper all (stackItemAtLocation e stack) e
sAdd all@(addressreg@(b, t, Nil, r, p, up, e, ut, tt, pc, sc, ac), (stack, us, trail)) symb ATPush = Nil -- TODO correct?
sAdd all@(addressreg@(b, t, c, r, p, up, e, ut, tt, pc, sc, ac), (stack, us, trail)) symb ATPush = sAddHelper all (stackItemAtLocation (c + 3) stack) (c + 3)
sAdd _ _ _ = error "something went wrong in s_add"

sAddHelper :: RegisterKeller -> StackElement -> Pointer -> Pointer
sAddHelper (reg, stacks@(stack, us, trail)) (CodeArg (ATVar (V name) addr)) currentLoc =
  addr
sAddHelper (reg, stacks@(stack, us, trail)) (CodeArg (ATEndEnv _)) currentLoc = Nil --stand in für stack argument o.ä. => EndEnv Pointer/Stackinhalt
sAddHelper (reg, stacks@(stack, us, trail)) item currentLoc =
  sAddHelper (reg, stacks) (stackItemAtLocation (currentLoc + 1) stack) currentLoc + 1

-- Dereferenzierungsfunktion; an welchen Term ist Var gebunden

deref :: MLStack -> (Pointer -> Pointer)
deref stack addr =
  case stackItemAtLocation addr stack of
    (CodeArg (ATStr _ _)) -> addr
    stackItemVar@(CodeArg (ATVar _ addr2)) ->
      derefVar stack addr addr2 stackItemVar
    _ -> error "Should have not been reachable: contained neither ATStr or ATVar"

derefVar :: MLStack -> Pointer -> Pointer -> StackElement -> Pointer
derefVar stack addr addr2 stackItemVar =
  let stack' = stackReplaceAtLocation addr stackItemVar stack
   in if isPNil addr2 then addr else deref stack' addr2

-- Aritätsfunktion; gibt Arität eines Atoms zurück

arity :: MLStack -> Pointer -> Arity
arity stack addr =
  case arityHelper (stackItemAtLocation addr stack) of
    Just x -> x
    Nothing -> error "arity was called on non Symbol Element"

arityHelper :: StackElement -> Maybe Arity
arityHelper (CodeArg (ATStr _ arityVal)) = Just arityVal
arityHelper _ = Nothing

-- Displayfunktion für Prompt; untested

display :: MLStack -> String
display stack@(Stack content) =
  -- Erstelle einen Substack bis zum Ende des Env
  let stackpart = Stack (takeWhile (not . isStackElemEndEnv) content)
   in displayHelper stackpart stack 1 "" -- Initialisierung des Stacks mit relativer Adresse 1 und leerem String

isStackElemEndEnv :: StackElement -> Bool
isStackElemEndEnv (CodeArg (ATEndEnv _)) = True
isStackElemEndEnv _ = False

displayHelper :: MLStack -> MLStack -> Pointer -> String -> String
displayHelper stackpart orgstack addr str =
  -- Überprüfung des Inhalts an Punkt addr
  case stackItemAtLocation addr stackpart of
    CodeArg (ATVar _ _) ->
      -- neuer Teil des Strings
      let str' = str ++ displayTerm orgstack (deref orgstack addr)
       in displayHelper stackpart orgstack (addr + 1) str' -- rekursives Weiterschreiben
    _ -> displayHelper stackpart orgstack (addr + 1) str

displayTerm :: MLStack -> Pointer -> String
displayTerm stack addr =
  case stackItemAtLocation (deref stack addr) stack of
    CodeArg (ATVar symb Nil) -> show symb
    CodeArg (ATStr (A symb) arity) ->
      show arity ++ "( " ++ displayTerm stack (deref stack addr + 1) ++ ") "
    _ -> ""

{--------------------------------------------------------------------
   Helpers; manually tested; changed for ML.
 --------------------------------------------------------------------}

-- A small explanation for this function:
-- the next "unify" etc is found by doing a string compare.
-- TransformN transforms items of a given stack to strings of length N
transformN :: [Command] -> Int -> Stack String
transformN code amount = Stack (map (take amount . show) code)

cFirst :: Zielcode -> Pointer
cFirst (Stack code) = Pointer $ stackLocationFirstItemOfKind "unify" (transformN code 5)

cNext :: Zielcode -> Pointer -> Pointer
cNext (Stack code) Nil = Nil
cNext (Stack code) p@(Pointer address) =
  case stackLocationFirstItemOfKind' "unify" (transformN (drop (address + 1) code) 5) of
    (Just relativeItemLocation) -> (p +<- 1) + Pointer relativeItemLocation
    Nothing -> Nil

cLast :: Zielcode -> Pointer
cLast (Stack code) = Pointer $ stackLocationFirstItemOfKind "prompt" (transformN code 6)

cGoal :: Zielcode -> Pointer
cGoal (Stack code) = case stackLocationLastItemOfKind' "return" (transformN code 6) of
  (Just location) -> Pointer location +<- 1
  Nothing -> Nil

-- the +1 is needed because start of goal is determined by checking the address of the last return statement

{---------------------------------------------------------------------
   Evaluator Functions -> take generated code list and call functions
 ---------------------------------------------------------------------}

callZielcode :: Command -> RegisterKeller -> Zielcode -> RegisterKeller
-- TODO: Prompt has to be called in Main (?)
callZielcode (Prompt _) regkeller code = regkeller
callZielcode (Push _ arg) regkeller code = push arg regkeller code
callZielcode (Unify _ arg) regkeller _ = unify arg regkeller
callZielcode (Backtrack _) regkeller code = backtrack regkeller code
callZielcode (Return _ arg) regkeller code = returnL arg regkeller
callZielcode (Call _) regkeller code = call regkeller code

-- this should be used for calling prompt in main
callPrompt :: Command -> RegisterKeller -> Zielcode -> IO ()
callPrompt (Prompt _) regsStacks code = prompt regsStacks code
callPrompt _ _ _ = error "Calling prompt resulted in an error."

-- use this for backtracking after reaching the first prompt
callFromPrompt :: RegisterKeller -> Zielcode -> IO ()
callFromPrompt regkeller code = do
  putStrLn "reeval..."
  let newregstack = runner regkeller code code
   in prompt newregstack code

runner :: RegisterKeller -> Zielcode -> Zielcode -> RegisterKeller
runner regkeller (Stack [firstfkt]) code = callZielcode firstfkt regkeller code
runner regkeller (Stack (firstfkt : rest)) code = runner (callZielcode firstfkt regkeller code) (Stack rest) code
runner regkeller (Stack []) code = error "Runner called on empty Zielcode."

{--------------------------------------------------------------------
              ML Unify Hilffunktionen
---------------------------------------------------------------------}
--Makroinstruktionen
addAC :: Int -> RegisterKeller -> RegisterKeller
addAC n all@(addressreg@(b, t, c, r, p, up, e, ut, tt, pc, sc, ac), stacks) = case ac of
  Pointer i -> ((b, t, c, r, p, up, e, ut, tt, pc, sc, ac +<- n), stacks)
  Nil -> all

restoreAcUpQ :: RegisterKeller -> RegisterKeller
restoreAcUpQ all@(addressreg@(b, t, c, r, p, up, e, ut, tt, pc, sc, ac), stacks@(stack, us, trail))
  | ac == Pointer 0 = ((b, t, c, r, p, safePointerFromStackAtLocation ut us, e, ut -<- 2, tt, pc, sc, safePointerFromStackAtLocation (ut -<- 1) us), stacks)
  | otherwise = all

saveAcUpQ :: RegisterKeller -> RegisterKeller
saveAcUpQ all@(addressreg@(b, t, c, r, p, up, e, ut, tt, pc, sc, ac), (stack, us, trail))
  | up <= safePointerFromStackAtLocation (c +<- 5) stack
      && deref stack up /= up
      && getArity (stackItemAtLocation (deref stack up) stack) /= 0 =
    ( (b, t, c, r, p, deref stack (up +<- 1), e, ut +<- 2, tt, pc, sc, 0),
      ( stack,
        us <> Stack [StackAddress ac, StackAddress (up +<- 1)],
        trail
      )
    )
  | otherwise = all

{--------------------------------------------------------------------
              ML Unify
---------------------------------------------------------------------}
unify :: Argument -> RegisterKeller -> RegisterKeller
unify arg all@(addressreg@(b, t, c, r, p, up, e, ut, tt, pc, sc, ac), (stack, us, trail))
  | pc >= 1 = p1 $ unifyPushModus arg all
  | otherwise = p1 $ unifyNonPushModus arg all

unifyPushModus :: Argument -> RegisterKeller -> RegisterKeller
unifyPushModus arg all@(addressreg@(b, t, c, r, p, up, e, ut, tt, pc, sc, ac), (stack, us, trail)) = case arg of
  ATVar var add -> ((b, t +<- 1, c, r, p, up, e, ut, tt, (pc -1) + getArity (CodeArg arg), sc, ac), (stackReplaceAtLocation (t +<- 1) (CodeArg (ATVar var (sAdd all arg ATUnify))) stack, us, trail))
  ATStr atom ar -> ((b, t +<- 1, c, r, p, up, e, ut, tt, (pc -1) + getArity (CodeArg arg), sc, ac), (stackReplaceAtLocation (t +<- 1) (CodeArg arg) stack, us, trail))
  _ -> error "Mitgegebenes Argument für PushModus muss Lineares Atom oder eine Variable sein"

unifyNonPushModus :: Argument -> RegisterKeller -> RegisterKeller
unifyNonPushModus arg all@(addressreg@(b, t, c, r, p, up, e, ut, tt, pc, sc, ac), (stack, us, trail)) = case arg of
  (ATVar var add) -> addRestoreUp $ whileSc $ arityUpToSc $ unifyVarNonPIfThenElse arg all
  (ATStr (A str) arity) -> unifyStrNonPIfThenElse arg all
  _ -> error "Mitgegebenes Argument für NonPush-Modus muss Lineares Atom oder eine Variable sein"

-- Hilfsfunktionen für den Fall, dass eine Variable unifiziert werden soll (unifyNonPushModus case arg = ATVar var add)
unifyVarNonPIfThenElse :: Argument -> RegisterKeller -> RegisterKeller
unifyVarNonPIfThenElse arg@(ATVar var add) all@(addressreg@(b, t, c, r, p, up, e, ut, tt, pc, sc, ac), (stack, us, trail)) =
  if sameSymbol arg all
    then addToStackAndTrailVar arg all
    else restoreT $ unifyProzedur (deref stack (sAdd all arg ATUnify)) up $ saveT all
unifyVarNonPIfThenElse arg _ = error "Argument has to be ATVar"

arityUpToSc :: RegisterKeller -> RegisterKeller
arityUpToSc all@(addressreg@(b, t, c, r, p, up, e, ut, tt, pc, sc, ac), (stack, us, trail)) =
  ((b, t, c, r, p, up, e, ut, tt, pc, arity stack up, ac), (stack, us, trail))

whileSc :: RegisterKeller -> RegisterKeller
whileSc all@(addressreg@(b, t, c, r, p, up, e, ut, tt, pc, sc, ac), (stack, us, trail))
  | sc >= 1 = whileSc ((b, t, c, r, p, up +<- 1, e, ut, tt, pc, sc -1 + arity stack up, ac), (stack, us, trail))
  | otherwise = all

addRestoreUp :: RegisterKeller -> RegisterKeller
addRestoreUp all@(addressreg@(b, t, c, r, p, up, e, ut, tt, pc, sc, ac), (stack, us, trail)) =
  up1 $ restoreAcUpQ $ addAC (-1) all

-- Holt t vom Hilfsstack us zurück
restoreT :: RegisterKeller -> RegisterKeller
restoreT all@(addressreg@(b, t, c, r, p, up, e, ut, tt, pc, sc, ac), (stack, us, trail)) = ((b, safePointerFromStackAtLocation ut us, c, r, p, up, e, ut -<- 1, tt, pc, sc, ac), (stack, us, trail))

-- Speichert T in us
saveT :: RegisterKeller -> RegisterKeller
saveT all@(addressreg@(b, t, c, r, p, up, e, ut, tt, pc, sc, ac), (stack, us, trail)) = ((b, t, c, r, p, up, e, ut +<- 1, tt, pc, sc, ac), (stack, stackReplaceAtLocation (ut +<- 1) (CodeAddress t) us, trail))

sameSymbol :: Argument -> RegisterKeller -> Bool
sameSymbol arg@(ATVar var add) all@(addressreg@(b, t, c, r, p, up, e, ut, tt, pc, sc, ac), (stack, us, trail)) = stackItemAtLocation (deref stack (sAdd all arg ATUnify)) stack == CodeArg (ATVar var Nil)
sameSymbol _ _ = error "Vergleich mit dieser Funktion war für Variablen gedacht"

-- FIXME: CodeAddress hier richtig?
addToStackAndTrailVar :: Argument -> RegisterKeller -> RegisterKeller
addToStackAndTrailVar
  arg@(ATVar var add)
  all@(addressreg@(b, t, c, r, p, up, e, ut, tt, pc, sc, ac), (stack, us, trail)) =
    ( (b, t, c, r, p, up, e, ut, tt +<- 1, pc, sc, ac),
      ( stackReplaceAtLocation (deref stack (sAdd all arg ATUnify)) (CodeArg (ATVar var up)) stack,
        us,
        stackReplaceAtLocation (tt +<- 1) (CodeAddress (sAdd all arg ATUnify)) trail
      )
    )
addToStackAndTrailVar _ _ = error "War für Variablen gedacht"

--Erhöht up um 1
up1 :: RegisterKeller -> RegisterKeller
up1 ((b, t, c, r, p, up, e, ut, tt, pc, sc, ac), stacks) =
  ((b, t, c, r, p, up +<- 1, e, ut, tt, pc, sc, ac), stacks)

--Erhöht p um 1
p1 :: RegisterKeller -> RegisterKeller
p1 ((b, t, c, r, p, up, e, ut, tt, pc, sc, ac), stacks) =
  ((b, t, c, r, p +<- 1, up, e, ut, tt, pc, sc, ac), stacks)

--Hilfsfunktionen für den Fall, dass eine structure cell unifiziert werden soll (unifyNonPushModus case arg = ATStr symbol add)
unifyStrNonPIfThenElse :: Argument -> RegisterKeller -> RegisterKeller
unifyStrNonPIfThenElse
  arg@(ATStr (A str) arity)
  all@(addressreg@(b, t, c, r, p, up, e, ut, tt, pc, sc, ac), (stack, us, trail)) =
    if sameSymbolForStr arg all
      then addRestoreUp $ addToStackAndTrailStr arg all
      else
        let (CodeArg arg2@(ATStr symb ar)) = stackItemAtLocation (deref stack up) stack
         in checkDereferencedUp arg arg2 all
unifyStrNonPIfThenElse _ _ = error "Diese Funktion soll nur mit Structure cells aufgerufen werden"

sameSymbolForStr :: Argument -> RegisterKeller -> Bool
sameSymbolForStr (ATStr symb@(A str) arity) all@(addressreg@(b, t, c, r, p, up, e, ut, tt, pc, sc, ac), (stack, us, trail)) =
  stackItemAtLocation (deref stack up) stack == CodeArg (ATVar (V str) Nil)
sameSymbolForStr _ _ = error "sameSymbolForStr gibt nur einen Wahrheitswert zurück für ATStr Argumente"

--Adds the Argument as a Var to the stack and as a Str to the top of stack, adds an address pointing at the dereferenced unification point to the trail, updates the tops of the stacks modiefied and sets the pushcounter to the arity of the pushed cell
addToStackAndTrailStr :: Argument -> RegisterKeller -> RegisterKeller
addToStackAndTrailStr arg@(ATStr (A str) arity) all@(addressreg@(b, t, c, r, p, up, e, ut, tt, pc, sc, ac), (stack, us, trail)) =
  ( (b, t +<- 1, c, r, p, up, e, ut, tt +<- 1, arity, sc, ac),
    ( stackReplaceAtLocation (t +<- 1) (CodeArg arg) $ stackReplaceAtLocation (deref stack up) (CodeArg (ATVar (V str) (t +<- 1))) stack,
      us,
      stackReplaceAtLocation (tt +<- 1) (CodeAddress (deref stack up)) trail
    )
  )
addToStackAndTrailStr _ _ = error "addToStackAndTrailStr soll nur mit ATStr Argumenten aufgerufen werden"

checkDereferencedUp :: Argument -> Argument -> RegisterKeller -> RegisterKeller
checkDereferencedUp arg@(ATStr symb arity) arg2@(ATStr symb2 arity2) all@(addressreg@(b, t, c, r, p, up, e, ut, tt, pc, sc, ac), stacks@(stack, us, trail)) =
  if symb /= symb2 || arity /= arity2
    then ((True, t, c, r, p, up, e, ut, tt, pc, sc, ac), stacks)
    else up1 $ restoreAcUpQ $ addAC (arity -1) $ saveAcUpQ all
checkDereferencedUp _ _ _ = error "This function checks if the unification of two cells was unsuccesful"

--to get the Arity of the to be unified Argument in push mode
getArity :: StackElement -> Int
getArity (CodeArg (ATStr _ arity)) = arity
getArity (CodeArg (ATVar _ _)) = 0
getArity _ = error "What"

--TODO unify Prozedur, setzt b im Endeffekt
unifyProzedur :: Pointer -> Up -> RegisterKeller -> RegisterKeller
unifyProzedur add1 add2 all@(addressreg@(b, t, c, r, p, up, e, ut, tt, pc, sc, ac), (stack, us, trail)) = unifyProzedur' True (addressreg, (stackPush (CodeAddress add2) $ stackPush (CodeAddress add1) stack, us, trail))

unifyProzedur' :: Bool -> RegisterKeller -> RegisterKeller
unifyProzedur' weiter all@(addressreg@(b, t, c, r, p, up, e, ut, tt, pc, sc, ac), (stack, us, trail)) =
  if weiter && stackEmpty stack
    then check2Unify (getD (stackPeekTop stack) stack) (getD (stackPeekTop (stackPop stack)) stack) weiter (addressreg, (stackPop $ stackPop stack, us, trail))
    else ((not weiter, t, c, r, p, up, e, ut, tt, pc, sc, ac), (stack, us, trail))

--Holt die dereferenierte Adresse des StackElementes
getD :: StackElement -> MLStack -> Pointer
getD (CodeAddress pointer) stack = deref stack pointer
getD _ _ = undefined

check2Unify :: Pointer -> Pointer -> Bool -> RegisterKeller -> RegisterKeller
check2Unify d1 d2 weiter all@(addressreg@(b, t, c, r, p, up, e, ut, tt, pc, sc, ac), (stack, us, trail)) =
  if d1 /= d2
    then
      let arg@(CodeArg (ATVar var symb)) = stackItemAtLocation d1 stack
       in check2UnifyIf arg d1 d2 weiter all
    else unifyProzedur' weiter all

check2UnifyIf :: StackElement -> Pointer -> Pointer -> Bool -> RegisterKeller -> RegisterKeller
check2UnifyIf arg@(CodeArg (ATVar var Nil)) d1 d2 weiter all@((b, t, c, r, p, up, e, ut, tt, pc, sc, ac), (stack, us, trail)) =
  unifyProzedur'
    weiter
    ( (b, t, c, r, p, up, e, ut, tt +<- 1, pc, sc, ac),
      ( stackReplaceAtLocation d1 (CodeArg (ATVar var d2)) stack,
        us,
        stackReplaceAtLocation (tt +<- 1) (CodeAddress d1) trail
      )
    )
check2UnifyIf (CodeArg (ATVar _ add)) d1 d2 weiter all@((b, t, c, r, p, up, e, ut, tt, pc, sc, ac), (stack, us, trail)) =
  let arg2@(CodeArg (ATVar var2 add2)) = stackItemAtLocation d2 stack
   in check3UnifyIf arg2 d1 d2 weiter all
check2UnifyIf _ _ _ _ _ = error "Nur mit Argumenten des Typs ATVar soll diese Funktion aufgerufen werden (Check2)"

check3UnifyIf :: StackElement -> Pointer -> Pointer -> Bool -> RegisterKeller -> RegisterKeller
check3UnifyIf arg2@(CodeArg (ATVar var2 Nil)) d1 d2 weiter all@((b, t, c, r, p, up, e, ut, tt, pc, sc, ac), (stack, us, trail)) =
  unifyProzedur'
    weiter
    ( (b, t, c, r, p, up, e, ut, tt +<- 1, pc, sc, ac),
      ( stackReplaceAtLocation d1 (CodeArg (ATVar var2 d1)) stack,
        us,
        stackReplaceAtLocation (tt +<- 1) (CodeAddress d2) trail
      )
    )
check3UnifyIf _ d1 d2 weiter all@((b, t, c, r, p, up, e, ut, tt, pc, sc, ac), (stack, us, trail)) =
  let (arg@(CodeArg (ATStr symb arity)), arg2@(CodeArg (ATStr symb2 arity2))) = (stackItemAtLocation d1 stack, stackItemAtLocation d2 stack)
   in checkForUnify (arg, arg2) d1 d2 weiter all

checkForUnify :: (StackElement, StackElement) -> Pointer -> Pointer -> Bool -> RegisterKeller -> RegisterKeller
checkForUnify (arg@(CodeArg (ATStr symb arity)), arg2@(CodeArg (ATStr symb2 arity2))) d1 d2 weiter all@((b, t, c, r, p, up, e, ut, tt, pc, sc, ac), (stack, us, trail)) =
  if symb /= symb2 || arity /= arity2
    then unifyProzedur' False all
    else pushD1D2 d1 d2 1 arity weiter all
checkForUnify _ _ _ _ _ =
  error "checkForUnify is suppossed to be called with two structure cells"

pushD1D2 :: Pointer -> Pointer -> Int -> Arity -> Bool -> RegisterKeller -> RegisterKeller
pushD1D2 d1 d2 i arity weiter all@(addressreg@(b, t, c, r, p, up, e, ut, tt, pc, sc, ac), (stack, us, trail))
  | i <= arity =
    pushD1D2
      d1
      d2
      (i + 1)
      arity
      weiter
      ( addressreg,
        ( stackPush (CodeAddress (d2 +<- i)) $ stackPush (CodeAddress (d1 +<- i)) stack,
          us,
          trail
        )
      )
  | otherwise = unifyProzedur' weiter all
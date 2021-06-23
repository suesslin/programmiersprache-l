module AbstractMachine where

import Parser
import Models
import Tokenizer
import Stack
import Data.Maybe
import Control.Exception

-- Register 
type B = Bool
type T = Int
type C = Int
type R = Int
type P = Int
type Adressreg = (B, T, C, R, P)

newtype Atom = A String deriving Eq
instance Show Atom where
   show (A str) = str

data StackElement = CodeAtom Atom | CodeAdress Int | Nil deriving (Eq)

instance Show StackElement where
   show (CodeAtom atm) = show atm
   show (CodeAdress adr) = "c" ++ show adr
   show Nil = "nil"

--helper
stackElementToInt :: StackElement -> Maybe Int
stackElementToInt (CodeAdress x) = Just x
stackElementToInt (CodeAtom x) = Nothing
stackElementToInt Nil = Nothing

type I = (Adressreg, Stack StackElement) -- why is this named I? Stack [String] needs rework

-- Commands, necessary for having a List of named partially applied functions 
data Command = Unify String (Atom -> I -> I) Atom
             | Push String (Atom -> I -> Zielcode -> I) Atom
             | Call String (I -> Zielcode -> I)
             | Prompt String (I -> Zielcode -> I)
             | Backtrack String (I -> Zielcode -> I)
             | Return String (I -> I)
             -- Prompt' String (I -> Zielcode -> IO())

instance Show Command where
   show (Unify name fkt atm) = name ++ " " ++ show atm
   show (Push name fkt atm) = name ++ " " ++ show atm
   show (Call name inst) = name
   show (Prompt name inst) = name
   show (Backtrack name inst) = name
   show (Return name inst) = name
   --show (Instruktion name inst) = name

instance Eq Command where
   (==) (Unify name1 fkt1 atm1) (Unify name2 fkt2 atm2) = (name1 == name2) && (atm1 == atm2)
   (==) (Push name1 fkt1 atm1) (Push name2 fkt2 atm2) = (name1 == name2) && (atm1 == atm2)
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
üb (TP (Programm klauseln@(pklausel:pklauseln) (Ziel lits))) akk
   | null klauseln  = üb (TZ (Ziel lits)) akk 
   | null pklauseln = üb (TZ (Ziel lits)) $ üb (TPk pklausel) akk
   | otherwise      = üb (TP (Programm pklauseln (Ziel lits))) $ üb (TPk pklausel) akk

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
übBody ((Literal polarity (LTNVar (NVLTerm atom _))):seq) akk = 
   let akk' = akk <> Stack [Push "push" push (A atom), Call "call" call, Backtrack "backtrack?" backtrackQ] 
   in übBody seq akk'
übBody [] akk = akk
übBody _ _ = error "Failure in übBody."


{-------------------------------------------------------------- 
   Instruktionen
 ---------------------------------------------------------------}


push :: Atom -> I -> Zielcode -> I
push atm ((b,t,c,r,p), stack) code = ((b,t+4,t+1,c+1,p+1), Stack [CodeAdress (cFirst code), CodeAdress c, CodeAdress (p+3), CodeAtom atm])

unify :: Atom -> I -> I
unify atm ((b,t,c,r,p), stack) = ((stackItemInLocation stack (c+3) /= CodeAtom atm,t,c,r,p+1), stack)

call :: I -> Zielcode -> I
call ((b,t,c,r,p),stack) code =
   if stackItemInLocation stack c == Nil -- TODO,actually just undefinied
   then ((True,t,c,r,p+1), stack)
   else let newC = (fromJust $ stackElementToInt $ stackItemInLocation stack c)
        in ((b,t,c,r,newC), stackWriteToLocation stack c (CodeAdress (cNext code newC)))

-- possible problem; nur logisches entkellern, untested
returnL :: I -> I
returnL ((b,t,c,r,p), stack) =
   let newP = fromJust $ stackElementToInt $ stackItemInLocation stack (r+1)
   in if stackItemInLocation stack r /= Nil
      then ((b,t,c, fromJust (stackElementToInt $ stackItemInLocation stack r) +1, newP), stack)
      else ((b,t,c,r,newP), stack)

backtrackQ :: I -> Zielcode -> I
backtrackQ reg@((b,t,c,r,p), stack) code = 
      if b 
      then let newreg@((b',t',c',r', p'), stack') = until (\((b,t,c,r,p), stack) -> stackItemInLocation stack c /= Nil || stackItemInLocation stack r == Nil) backtrackWhile reg --untested
               newC = fromJust $ stackElementToInt $ stackItemInLocation stack' c'
           in case stackItemInLocation stack' c' of 
            Nil -> ((b',t',c',r', cLast code), stack') 
            _ -> ((False,t',c',r', newC), stackWriteToLocation stack c (CodeAdress (cNext code newC)))
      else ((b,t,c,r,p+1), stack) 
   where backtrackWhile :: I -> I 
         backtrackWhile ((b,t,c,r,p), stack) = backtrackWhile ((b,c+3,fromJust $ stackElementToInt $ stackItemInLocation stack r,p,c+1), stack)

prompt :: I -> Zielcode -> I -- greedy prompt without IO, temporary solution
prompt reg@((b,t,c,r,p), stack) code = 
   if b 
   then ((b,t,c,r,-1), stack) -- should be nil or undefinied, fix by using stack?
   else ((True,t,c,r,p-1), stack)


prompt':: I -> Zielcode -> IO ()
prompt' reg@((b,t,c,r,p), stack) code
   | b = do
      putStrLn "no (more) solutions."
   | otherwise = do
      putStrLn "yes. more?"
      answer <- getLine
      if answer == ";" then undefined --evalFromPrompt ((True, t,c,r,p-1), stack) code TODO!!
      else putStrLn "Wrong input, aborting."


{-------------------------------------------------------------------- 
   Helpers; manually tested.
 --------------------------------------------------------------------}

transformN :: [Command] -> Int -> Stack String 
transformN code amount = Stack (map (take amount . show) code)

cFirst :: Zielcode -> Int
cFirst (Stack code) = stackLocationFirstItemOfKind (transformN code 5) "unify" -- doesnt really use command datatype, rather its show repr.

cNext :: Zielcode -> Int -> Int
cNext (Stack code) adress = stackLocationFirstItemOfKind (transformN (drop (adress+1) code) 5) "unify" +1
-- +1 needed because drop shrinks list by one 

cLast :: Zielcode -> Int 
cLast (Stack code) = stackLocationFirstItemOfKind (transformN code 6) "prompt"

cGoal :: Zielcode -> Int 
cGoal (Stack code) = stackLocationLastItemOfKind (transformN code 6) "return" +1
-- the +1 is needed because start of goal is determined by checking the adress of the last return statement


{--------------------------------------------------------------------- 
   Evaluator Functions -> take generated code list and call functions
 ---------------------------------------------------------------------}


-- evaluator(s), there might be a better solution for our command datatype 
callZielcode :: Command -> I -> Zielcode -> I
callZielcode (Push name fkt atm) reg code = push atm reg code
callZielcode (Unify name fkt atm) reg code = unify atm reg
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
runner reg (Stack (firstfkt:rest)) code = runner (callZielcode firstfkt reg code) (Stack rest) code      
runner reg (Stack []) code = reg 

code :: Zielcode
code = codeGen (parse $ tokenize "p :- q. q :- r. r. :- p, r.")

initial :: I
initial = ((False,-1,0,0,cGoal code), initStack)
-- is zero ok here? 

teststate :: I 
teststate = ((False, 3,2,2,1), initStack)
initStack :: Stack StackElement
initStack = stackNewEmpty 

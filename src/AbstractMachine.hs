module AbstractMachine where
   
import Parser
import Models
import Tokenizer
import Data.Maybe

-- Register 
type B = Bool
type T = Int
type C = Int
type R = Int
type P = Int
type Adressreg = (B, T, C, R, P)

-- Stack 
newtype Stack a = Stack [a] deriving (Show,Eq)

instance Semigroup (Stack a) where 
   (<>) (Stack content1) (Stack content2) = Stack (content1++content2)

instance Monoid (Stack a) where 
   mempty = Stack []
   mappend = (<>) 

instance Functor Stack where
   fmap f (Stack content) = Stack (map f content)

stackPeekTop :: Stack a -> Maybe a
stackPeekTop (Stack content) = Just (last' content)  
      where last' :: [a] -> a
            last' [x] = x
            last' (_:xs) = last' xs 
stackPeekTop (Stack []) = Nothing
   -- last' should never get called on empty list, therefore it doesnt the corresponding error pattern
   -- empty list case is handled by stackPeekTop via Maybe 


stackPop :: Stack a -> Maybe (Stack a)
stackPop (Stack (x:xs)) = Just (Stack xs) 
stackPop (Stack []) = Nothing 

stackPush :: Stack a -> a -> Stack a 
stackPush (Stack content) new = Stack (reverse $ new:content) -- suboptimal, quick and dirty solution for Inifite Type Problem when new is appended to the end of content, NEEDS REWORK 

stackSizeOf :: Stack a -> Int 
stackSizeOf (Stack content) = length content 

stackItemInLocation :: Stack a -> Int -> a 
stackItemInLocation (Stack content) 0 = head content 
stackItemInLocation (Stack content) pos = content !! pos  

stackWriteToLocation :: Stack a -> Int -> a -> Maybe (Stack a)
stackWriteToLocation (Stack content) pos val = undefined


data StackElement = StackAtom Atom | StackAdress Int | StackEmpty deriving (Show,Eq)

--helper
stackElementToInt :: StackElement -> Maybe Int 
stackElementToInt (StackAdress x) = Just x
stackElementToInt (StackAtom x) = Nothing 
stackElementToInt StackEmpty = Nothing 


type I = (Adressreg, Stack StackElement) -- why is this named I? Stack [String] needs rework

-- Atom, mainly helper  
newtype Atom = A String deriving Eq
instance Show Atom where 
   show (A str) = str

-- Commands, necessary for having a List of named partially applied functions 
data Command = Unify String (Atom -> I -> I) Atom | Push String (Atom -> I -> Zielcode -> I) Atom | Call String (Callflag -> I -> Zielcode -> I) | Instruktion String (Callflag -> I -> I) 

instance Show Command where 
   show (Unify name fkt atm) = name ++ " " ++ show atm 
   show (Push name fkt atm) = name ++ " " ++ show atm 
   show (Call name inst) = name 
   show (Instruktion name inst) = name 

instance Eq Command where 
   (==) (Unify name1 fkt1 atm1) (Unify name2 fkt2 atm2) = (name1 == name2) && (atm1 == atm2) 
   (==) (Push name1 fkt1 atm1) (Push name2 fkt2 atm2) = (name1 == name2) && (atm1 == atm2)
   (==) (Call name1 inst1) (Call name2 inst2) = name1 == name2 
   (==) (Instruktion name1 inst1) (Instruktion name2 inst2) = name1 == name2
   (==) _ _ = False 

-- Zielcode is the returntype of L Code Translation
type Zielcode = [Command]

-- Callflag for partial application of I -> I functions
type Callflag = Bool

{----------------------------------------------------------  
   MiniL
-----------------------------------------------------------}




--Instruktionen
push :: Atom -> I -> Zielcode -> I 
push atm ((b,t,c,r,p), stack) code = ((b,t+4,t+1,c+1,p+1), Stack [StackAdress (cFirst code), StackAdress c, StackAdress (p+3), StackAtom atm])

unify :: Atom -> I -> I 
unify atm ((b,t,c,r,p), stack) = ((stackItemInLocation stack (c+3) /= StackAtom atm,t,c,r,p+1), stack) 

call :: Callflag -> I -> Zielcode -> I
call true ((b,t,c,r,p),stack) code = 
   if stackItemInLocation stack c == StackEmpty
   then ((true,t,c,r,p+1), stack)
   else let newC = (fromJust $ stackElementToInt $ stackItemInLocation stack c)
        in ((b,t,c,r,newC), fromJust $ stackWriteToLocation stack c (StackAdress (fromJust $ cNext code newC)))                                    

returnL :: Callflag -> I -> I
returnL  = undefined

backtrackQ :: Callflag -> I -> I
backtrackQ  = undefined

prompt :: Callflag -> I -> I
prompt  = undefined

-- env helpers 
cFirst :: Zielcode -> Int 
cFirst code = 0 -- is this valid?

cNext :: Zielcode -> Int -> Maybe Int --maybe use either? 
cNext code i = undefined -- adress of next pk or nil if ci points to last pk 

cGoal :: Zielcode -> Int 
cGoal code = undefined --beginn von ziel

cLast :: Zielcode -> Int 
cLast code = undefined --address of prompt 

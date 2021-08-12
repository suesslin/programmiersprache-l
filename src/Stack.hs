module Stack where

import Data.List
import Data.Maybe

-- Stack
-- Maybe redefine stack top/bottom to make more use of head/tail

newtype Stack a = Stack [a] deriving (Eq)

instance Semigroup (Stack a) where
  (<>) (Stack content1) (Stack content2) = Stack (content1 ++ content2)

instance Monoid (Stack a) where
  mempty = Stack []
  mappend = (<>)

instance Functor Stack where
  fmap f (Stack content) = Stack (map f content)

instance (Show a) => Show (Stack a) where
  show (Stack stackelems) = unlines $ zipWith (\x y -> "s" ++ show x ++ ": " ++ show y) [0 ..] stackelems

stackNewEmpty :: Stack a
stackNewEmpty = Stack []

stackPeekTop :: Stack a -> a
stackPeekTop (Stack content) = last content

stackPeekBottom :: Stack a -> a 
stackPeekBottom (Stack content) = head content 

stackPop :: Stack a -> Stack a
stackPop (Stack content) = Stack (init content)

stackPush :: a -> Stack a -> Stack a
stackPush new (Stack content) = Stack (reverse $ new : reverse content)

-- suboptimal, quick and dirty solution for Inifite Type Problem when new is appended to the end of content, NEEDS REWORK

stackSizeOf :: Stack a -> Int
stackSizeOf (Stack content) = length content

stackItemAtLocation :: (Integral a, Ord a) => a -> Stack b -> b
stackItemAtLocation 0 (Stack content) = head content
stackItemAtLocation pos (Stack content) = content !! fromIntegral (toInteger pos) -- this is a bit suboptimal

-- Replaces an element at a location
stackReplaceAtLocation :: (Integral a, Ord a) => a -> b -> Stack b -> Stack b
stackReplaceAtLocation i elem (Stack []) = Stack [elem]
stackReplaceAtLocation i elem (Stack content) = 
  let i' = fromIntegral (toInteger i)
  in Stack $ concat [take i' content, [elem], drop (i' + 1) content]

stackWriteToLocation :: (Num a, Ord a) => a -> b -> Stack b -> Stack b
stackWriteToLocation pos val (Stack []) = Stack [val]
stackWriteToLocation pos val (Stack content@(x : xs))
  | -1 <= pos && pos <= 0 = Stack [val] <> Stack content
  | pos <= fromIntegral (length content -1) = Stack [x] <> stackWriteToLocation (pos -1) val (Stack xs)
  | otherwise = error "position exceeds listsize."

stackWriteToLocationMultiple :: (Num a, Ord a) => [(a, b)] -> Stack b -> Stack b
stackWriteToLocationMultiple [(loc, val)] stack = stackWriteToLocation loc val stack
stackWriteToLocationMultiple ((loc, val) : xs) stack = stackWriteToLocationMultiple xs (stackWriteToLocation loc val stack)
stackWriteToLocationMultiple _ _ = error "something went wrong whilst trying to create new stack with multiple overwrites."

-- needs actual error handling
stackLocationFirstItemOfKind :: (Eq a, Num b, Enum b) => a -> Stack a -> b
stackLocationFirstItemOfKind item (Stack content) = fst $ head $ filter ((== item) . snd) $ zip [0 ..] content

stackLocationLastItemOfKind :: (Eq a, Num b, Enum b) => a -> Stack a -> b
stackLocationLastItemOfKind item (Stack content) = fst $ last $ filter ((== item) . snd) $ zip [0 ..] content

-- Safe version
stackLocationFirstItemOfKind' :: (Eq a) => a -> Stack a -> Maybe Int
stackLocationFirstItemOfKind' item (Stack content) =
  fst <$> find ((==) item . snd) (zip [0 ..] content)

-- Safe Version
stackLocationLastItemOfKind' :: (Eq a) => a -> Stack a -> Maybe Int
stackLocationLastItemOfKind' item (Stack content) =
  fst <$> find ((==) item . snd) (reverse $ zip [0 ..] content)

stackTake :: Int -> Stack a -> Stack a
stackTake n (Stack a) = Stack $ take n a

-- This should work but doesn't: stackTake n stack = take n <$> stack

stackDrop :: Int -> Stack a -> Stack a
stackDrop n (Stack a) = Stack $ drop n a

stackEmpty :: Stack a -> Bool
stackEmpty (Stack []) = True
stackEmpty _ = False
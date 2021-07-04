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

stackPop :: Stack a -> Stack a
stackPop (Stack content) = Stack (init content)

stackPush :: a -> Stack a -> Stack a
stackPush new (Stack content) = Stack (reverse $ new : reverse content)

-- suboptimal, quick and dirty solution for Inifite Type Problem when new is appended to the end of content, NEEDS REWORK

stackSizeOf :: Stack a -> Int
stackSizeOf (Stack content) = length content

stackItemAtLocation :: Int -> Stack a -> a
stackItemAtLocation 0 (Stack content) = head content
stackItemAtLocation pos (Stack content) = content !! pos

stackWriteToLocation :: Int -> a -> Stack a -> Stack a
stackWriteToLocation pos val (Stack []) = Stack [val]
stackWriteToLocation pos val (Stack content@(x : xs))
  | -1 <= pos && pos <= 0 = Stack [val] <> Stack content
  | pos <= length content -1 = Stack [x] <> stackWriteToLocation (pos -1) val (Stack xs)
  | otherwise = error "position exceeds listsize."

stackLocationFirstItemOfKind :: (Eq a) => a -> Stack a -> Int
stackLocationFirstItemOfKind item (Stack content) = fst $ head $ filter ((== item) . snd) $ zip [0 ..] content

stackLocationLastItemOfKind :: (Eq a) => a -> Stack a -> Int
stackLocationLastItemOfKind item (Stack content) = fst $ last $ filter ((== item) . snd) $ zip [0 ..] content

stackTake :: Int -> Stack a -> Stack a
stackTake n (Stack a) = Stack $ take n a

-- This should work but doesn't: stackTake n stack = take n <$> stack

stackDrop :: Int -> Stack a -> Stack a
stackDrop n (Stack a) = Stack $ drop n a

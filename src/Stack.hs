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

-- special show instance for Stack, for easier debugging. TODO: doesnt work, needs a zip
instance (Show a, Eq a) => Show (Stack a) where
  show (Stack stackelems) = stackShow $ zip [0 ..] stackelems
    where
      stackShow :: (Eq a, Show a) => [(Int, a)] -> String
      stackShow items = unlines $ map (\(x, y) -> "s" ++ show x ++ ": " ++ show y) items

stackNewEmpty :: Stack a
stackNewEmpty = Stack []

stackPeekTop :: Stack a -> a
stackPeekTop (Stack content) = last content

stackPop :: Stack a -> Stack a
stackPop (Stack content) = Stack (init content)

stackPush :: Stack a -> a -> Stack a
stackPush (Stack content) new = Stack (reverse $ new : content)

-- suboptimal, quick and dirty solution for Inifite Type Problem when new is appended to the end of content, NEEDS REWORK

stackSizeOf :: Stack a -> Int
stackSizeOf (Stack content) = length content

-- TODO: Change order: Int -> Stack a -> a
stackItemAtLocation :: Stack a -> Int -> a
stackItemAtLocation (Stack content) 0   = head content
stackItemAtLocation (Stack content) pos = content !! pos

stackWithReplacedItemAt :: Stack a -> Int -> a -> Stack a
stackWithReplacedItemAt (Stack content) pos val
  | pos <= (length content -1) = Stack (take pos content) <> Stack [val] <> Stack (drop (pos + 1) content)
  | otherwise = error "position exceeds listsize."

stackLocationFirstItemOfKind :: (Eq a) => Stack a -> a -> Int
stackLocationFirstItemOfKind (Stack content) item = fst $ head $ filter ((== item) . snd) $ zip [0 ..] content

stackLocationLastItemOfKind :: (Eq a) => Stack a -> a -> Int
stackLocationLastItemOfKind (Stack content) item = fst $ last $ filter ((== item) . snd) $ zip [0 ..] content

stackTake :: Int -> Stack a -> Stack a
stackTake n (Stack a) = Stack $ take n a

-- This should work but doesn't: stackTake n stack = take n <$> stack

stackDrop :: Int -> Stack a -> Stack a
stackDrop n (Stack a) = Stack $ drop n a

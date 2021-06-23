module StackSpec where

import Models
import Parser
import Stack
import Test.HUnit
import Tokenizer

testStackPeekTop =
  TestCase $
    assertEqual
      "stackPeekTop return top element of stack"
      3
      (stackPeekTop (Stack [1, 2, 3]))

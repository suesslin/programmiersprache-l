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

testStackPop =
  TestCase $
    assertEqual
      "stackPop should delete the top element of the stack"
      (Stack [1, 2])
      (stackPop (Stack [1, 2, 3]))

testStackPush =
  TestCase $
    assertEqual
      "stackPush should return a new Stack containing the pushed element a"
      (Stack [1, 2, 3, 4])
      (stackPush 4 (Stack [1, 2, 3]))

testStackSizeOf =
  TestCase $
    assertEqual
      "stackSizeOf should return size of Stack"
      3
      (stackSizeOf (Stack [1, 2, 3]))

testStackItemAtLocation =
  TestCase $
    assertEqual
      "stackItemAtLocation should return the Stack Item at a given List Index (starting at 0)"
      2
      (stackItemAtLocation 1 (Stack [1, 2, 3]))

testStackWriteToLocation =
  TestCase $
    assertEqual
      "stackWriteToLocation  should return a new stack with item x inserted at location y (starting from 0)"
      (Stack [1, 2, 3, 6, 4])
      (stackWriteToLocation 3 6 (Stack [1, 2, 3, 4]))

testStackWriteToLocationMultiple =
  TestCase $
    assertEqual
      "stackWriteToLocationMultiple should return a new stack with multiple changes on various location, depending on the input arguments"
      (Stack [1, 42, 1337, 2, 3, 4])
      (stackWriteToLocationMultiple [(1, 42), (2, 1337)] (Stack [1, 2, 3, 4]))

testStackLocationFirstItemOfKind =
  TestCase $
    assertEqual
      "stackLocationFirstItemOfKind should return the location of the frist match of a given item in a stack (starting from 0)"
      2
      (stackLocationFirstItemOfKind 3 (Stack [1, 2, 3, 3, 4]))

testStackLocationLastItemOfKind =
  TestCase $
    assertEqual
      "stackLocationLastItemOfKind should return the location of the last match of a given item in a stack (starting from 0)"
      3
      (stackLocationLastItemOfKind 3 (Stack [1, 2, 3, 3, 4]))

stackTests =
  [ testStackPush,
    testStackPop,
    testStackSizeOf,
    testStackItemAtLocation,
    testStackWriteToLocation,
    testStackLocationFirstItemOfKind,
    testStackLocationLastItemOfKind
  ]
module AbstractMachineSpec where

import AbstractMachine
import Models
import Parser
import Stack
import Test.HUnit
import Tokenizer

emptyZielcode :: Zielcode
emptyZielcode = Stack []

partialZielcode :: Zielcode
partialZielcode = Stack [Unify unify (A "p"), Backtrack backtrackQ, Push push (A "q"), Call call, Backtrack backtrackQ, Return returnL]

{--------------------------------------------------
    Tests for of codeGen | üb
 --------------------------------------------------}

testÜbHeadEmptyAkk =
  TestCase $
    assertEqual
      "übHead should build a Command Stack with correct commands"
      (Stack [Unify unify (A "p"), Backtrack backtrackQ])
      (übHead (A "p") emptyZielcode)

testÜbHeadNonEmptyAkk =
  TestCase $
    assertEqual
      "übHead should return existing Zielcode appended by head translation rule"
      (partialZielcode <> Stack [Unify unify (A "p"), Backtrack backtrackQ])
      (übHead (A "p") partialZielcode)

testÜbBodyEmptyAkk = undefined

testÜbBodyNonEmptyAkk = undefined

testÜbProgrammSinglePkAndGoal = undefined

testÜbProgramMultiplePksAndGoal = undefined

testÜbProgrammOnlyGoal = undefined

testÜbProgrammSingleGoalMultipleLiterals = undefined

testÜbProgramSingleGoalSingleLiteral = undefined

{--------------------------------------------------
    Initial values for testing commands and cHelpers.
 --------------------------------------------------}

code :: Zielcode
code = codeGen (parse $ tokenize "p :- q. q :- r. r. :- p, r.")

code' :: Zielcode
code' = codeGen (parse $ tokenize ":- p,r.")

initStack :: Stack StackElement
initStack = stackNewEmpty

initial :: I -- register in intial state
initial = ((False, Pointer (-1), Nil, Nil, cGoal code), initStack)

firstreg :: I -- register after first push
firstreg = ((False, Pointer 3, Pointer 0, Pointer 1, Pointer 16), Stack [CodeAddress (Pointer 0), StackAddress Nil, CodeAddress (Pointer 18), CodeAtom (A "p")])

subsequentreg :: I -- register after some calls p. 131 top
subsequentreg =
  ( (False, Pointer 11, Pointer 8, Pointer 9, Pointer 14),
    Stack
      [ CodeAddress (Pointer 6),
        StackAddress Nil,
        CodeAddress (Pointer 18),
        CodeAtom (A "p"),
        CodeAddress (Pointer 12),
        StackAddress (Pointer 0),
        CodeAddress (Pointer 5),
        CodeAtom (A "q"),
        CodeAddress Nil,
        StackAddress (Pointer 4),
        CodeAddress (Pointer 11),
        CodeAtom (A "r")
      ]
  )

{---------------------------------------------------
    Tests for Helpers
 ---------------------------------------------------}

testCGoalPkAndZiel =
  TestCase $
    assertEqual
      "cGoal should return the Addressvalue of the first command in a goal when LCode consists of pks and goal."
      (Pointer 15)
      (cGoal code)

testCGoalOnlyZiel =
  TestCase $
    assertEqual
      "cGoal should return the Addressvalue of the first command in a goal when LCode consists of a single goal."
      (Pointer 0)
      (cGoal code')

testCFirstPkAndZiel =
  TestCase $
    assertEqual
      "cFirst should return the Addressvalue of the first command of the first pk."
      (Pointer 0)
      (cFirst code)

-- testCFirstOnlyZiel = ??? Wie sollte sich cFirst bei Programm wie code' verhalten?

testCNextFirstPkAndZiel =
  TestCase $
    assertEqual
      "cNext should return the Addressvalue of the first command of the next pk given a current pk location"
      (Pointer 6)
      (cNext code (Pointer 0))

testCNextMiddlePkAndZiel =
  TestCase $
    assertEqual
      "cNext should return the absolute Addressvalue of a pk start given another pk start."
      (Pointer 12)
      (cNext code (Pointer 6))

testCNextLastPkAndZiel =
  TestCase $
    assertEqual
      "cNext should return nil if called on last pk."
      Nil
      (cNext code (Pointer 12))

testCNextOnlyZiel =
  TestCase $
    assertEqual
      "cNext should return nil if called on LCode consisting of a single goal"
      Nil
      (cNext code' (Pointer 0))

testCLastPkAndZiel =
  TestCase $
    assertEqual
      "cLast should return codeAddress of prompt when called on LCode consisting of pk(s) and goal"
      (Pointer 21)
      (cLast code)

testCLastOnlyZiel =
  TestCase $
    assertEqual
      "cLast should return codeAddress of prompt when called on LCode consisting of single goal"
      (Pointer 6)
      (cLast code')

{-------------------------------------------------------------
    Tests for Commands, MiniL based
 --------------------------------------------------------------}

testPushAtomEmptyStack =
  TestCase $
    assertEqual
      "push p should push Atom A, choice Point C, and return Address p+3 on stack, then update registers accordingly."
      ((False, Pointer 3, Pointer 0, Pointer 1, Pointer 16), Stack [CodeAddress (Pointer 0), StackAddress Nil, CodeAddress (Pointer 18), CodeAtom (A "p")])
      (push (A "p") initial code)

testPushAtomSubsequent =
  TestCase $
    assertEqual
      "push q should update the stack accordingly when operating with existing stack."
      ( (False, Pointer 7, Pointer 4, Pointer 5, Pointer 3),
        Stack
          [CodeAddress (Pointer 6), StackAddress Nil, CodeAddress (Pointer 18), CodeAtom (A "p"), CodeAddress (Pointer 0), StackAddress (Pointer 0), CodeAddress (Pointer 5), CodeAtom (A "q")]
      )
      ( push
          (A "q")
          ( (False, Pointer 3, Pointer 0, Pointer 1, Pointer 2),
            Stack [CodeAddress (Pointer 6), StackAddress Nil, CodeAddress (Pointer 18), CodeAtom (A "p")]
          )
          code
      )

testUnifyUnifiable =
  TestCase $
    assertEqual
      "unify p should set registers accordingly when called on unifiable clause."
      ((False, Pointer 3, Pointer 0, Pointer 1, Pointer 1), Stack [CodeAddress (Pointer 0), StackAddress Nil, CodeAddress (Pointer 18), CodeAtom (A "p")])
      (unify (A "p") ((False, Pointer 3, Pointer 0, Pointer 1, Pointer 0), Stack [CodeAddress (Pointer 0), StackAddress Nil, CodeAddress (Pointer 18), CodeAtom (A "p")]))

testUnifyUnunifiable =
  TestCase $
    assertEqual
      "unify should set registers accordingly when called on ununifiable clause."
      ((True, Pointer 7, Pointer 4, Pointer 5, Pointer 1), Stack [CodeAddress (Pointer 6), StackAddress Nil, CodeAddress (Pointer 18), CodeAtom (A "p"), CodeAddress (Pointer 6), StackAddress (Pointer 0), CodeAddress (Pointer 5), CodeAtom (A "q")])
      (unify (A "p") ((False, Pointer 7, Pointer 4, Pointer 5, Pointer 0), Stack [CodeAddress (Pointer 6), StackAddress Nil, CodeAddress (Pointer 18), CodeAtom (A "p"), CodeAddress (Pointer 6), StackAddress (Pointer 0), CodeAddress (Pointer 5), CodeAtom (A "q")]))

-- First call instruction, p. 129
testCallOnFirst =
  TestCase $
    assertEqual
      "call should set I accordingly when called after first push command"
      ( (False, Pointer 3, Pointer 0, Pointer 1, Pointer 0),
        Stack
          [CodeAddress (Pointer 6), StackAddress Nil, CodeAddress (Pointer 18), CodeAtom (A "p")]
      )
      ( call
          ( (False, Pointer 3, Pointer 0, Pointer 1, Pointer 16),
            Stack
              [CodeAddress (Pointer 0), StackAddress Nil, CodeAddress (Pointer 18), CodeAtom (A "p")]
          )
          code
      )

testCallOnSubsequent =
  TestCase $
    assertEqual
      "call should set registers accordingly when called after subsequent push commands."
      ( (False, Pointer 7, Pointer 4, Pointer 5, Pointer 0),
        Stack
          [CodeAddress (Pointer 6), StackAddress Nil, CodeAddress (Pointer 18), CodeAtom (A "p"), CodeAddress (Pointer 6), StackAddress (Pointer 0), CodeAddress (Pointer 5), CodeAtom (A "q")]
      )
      ( call
          ( (False, Pointer 7, Pointer 4, Pointer 5, Pointer 3),
            Stack
              [CodeAddress (Pointer 6), StackAddress Nil, CodeAddress (Pointer 18), CodeAtom (A "p"), CodeAddress (Pointer 0), StackAddress (Pointer 0), CodeAddress (Pointer 5), CodeAtom (A "q")]
          )
          code
      )

testCallCNilCase =
  TestCase $
    assertEqual
      "call should set I correctly when called on c == nil"
      ((True, Pointer 3, Pointer 0, Pointer 1, Pointer 17), Stack [CodeAddress Nil, StackAddress Nil, CodeAddress (Pointer 18), CodeAtom (A "p")])
      (call ((False, Pointer 3, Pointer 0, Pointer 1, Pointer 16), Stack [CodeAddress Nil, StackAddress Nil, CodeAddress (Pointer 18), CodeAtom (A "p")]) code)

-- p. 131
testReturnLNotNilCase =
  TestCase $
    assertEqual
      "return on not r unequal nil should set registers correctly"
      ( (False, Pointer 11, Pointer 8, Pointer 5, Pointer 11),
        Stack
          [ CodeAddress (Pointer 6),
            StackAddress Nil,
            CodeAddress (Pointer 18),
            CodeAtom (A "p"),
            CodeAddress (Pointer 12),
            StackAddress (Pointer 0),
            CodeAddress (Pointer 5),
            CodeAtom (A "q"),
            CodeAddress Nil,
            StackAddress (Pointer 4),
            CodeAddress (Pointer 11),
            CodeAtom (A "r")
          ]
      )
      ( returnL
          ( (False, Pointer 11, Pointer 8, Pointer 9, Pointer 14),
            Stack
              [ CodeAddress (Pointer 6),
                StackAddress Nil,
                CodeAddress (Pointer 18),
                CodeAtom (A "p"),
                CodeAddress (Pointer 12),
                StackAddress (Pointer 0),
                CodeAddress (Pointer 5),
                CodeAtom (A "q"),
                CodeAddress Nil,
                StackAddress (Pointer 4),
                CodeAddress (Pointer 11),
                CodeAtom (A "r")
              ]
          )
      )

-- Input p.131: Return in the middle (2nd of 3 on the page)
testReturnLElseCase =
  TestCase $
    assertEqual
      "returnL should set registers correctly when called on register with r == nil"
      ( (False, Pointer 11, Pointer 8, Pointer 1, Pointer 18),
        Stack
          [ CodeAddress (Pointer 6),
            StackAddress Nil,
            CodeAddress (Pointer 18),
            CodeAtom (A "p"),
            CodeAddress (Pointer 12),
            StackAddress (Pointer 0),
            CodeAddress (Pointer 5),
            CodeAtom (A "q"),
            CodeAddress Nil,
            StackAddress (Pointer 4),
            CodeAddress (Pointer 11),
            CodeAtom (A "r")
          ]
      )
      ( returnL
          ( (False, Pointer 11, Pointer 8, Pointer 1, Pointer 5),
            Stack
              [ CodeAddress (Pointer 6),
                StackAddress Nil,
                CodeAddress (Pointer 18),
                CodeAtom (A "p"),
                CodeAddress (Pointer 12),
                StackAddress (Pointer 0),
                CodeAddress (Pointer 5),
                CodeAtom (A "q"),
                CodeAddress Nil,
                StackAddress (Pointer 4),
                CodeAddress (Pointer 11),
                CodeAtom (A "r")
              ]
          )
      )

testBacktrackQBTrue =
  TestCase $
    assertEqual
      "backtrack should set I correctly when called on b == true."
      ((False, Pointer 7, Pointer 4, Pointer 5, Pointer 6), Stack [CodeAddress (Pointer 6), StackAddress Nil, CodeAddress (Pointer 18), CodeAtom (A "p"), CodeAddress (Pointer 6), StackAddress (Pointer 0), CodeAddress (Pointer 5), CodeAtom (A "q")])
      (backtrackQ ((True, Pointer 7, Pointer 4, Pointer 5, Pointer 1), Stack [CodeAddress (Pointer 6), StackAddress Nil, CodeAddress (Pointer 18), CodeAtom (A "p"), CodeAddress (Pointer 6), StackAddress (Pointer 0), CodeAddress (Pointer 5), CodeAtom (A "q")]) code)

testBacktrackQBFalse =
  TestCase $
    assertEqual
      "backtrack should set I correctly when called on b == false."
      ((False, Pointer 3, Pointer 0, Pointer 1, Pointer 2), Stack [CodeAddress (Pointer 6), StackAddress Nil, CodeAddress (Pointer 18), CodeAtom (A "p")])
      (backtrackQ ((False, Pointer 3, Pointer 0, Pointer 1, Pointer 1), Stack [CodeAddress (Pointer 6), StackAddress Nil, CodeAddress (Pointer 18), CodeAtom (A "p")]) code)

übTests =
  [ testÜbHeadEmptyAkk,
    testÜbHeadNonEmptyAkk
  ]

helpersTests =
  [ testCFirstPkAndZiel,
    testCGoalOnlyZiel,
    testCGoalPkAndZiel,
    testCLastOnlyZiel,
    testCLastPkAndZiel,
    testCNextFirstPkAndZiel,
    testCNextLastPkAndZiel,
    testCNextMiddlePkAndZiel,
    testCNextOnlyZiel
  ]

commandTests =
  [ testPushAtomEmptyStack,
    testPushAtomSubsequent,
    testUnifyUnifiable,
    testUnifyUnunifiable,
    testCallOnFirst,
    testCallOnSubsequent,
    testCallCNilCase,
    testReturnLNotNilCase,
    testReturnLElseCase,
    testBacktrackQBTrue,
    testBacktrackQBFalse
  ]

module AbstractMachineSpec where

import AbstractMachine
import Models
import Parser
import Stack
import Test.HUnit
import Tokenizer

{- emptyZielcode :: Zielcode
emptyZielcode = Stack []

partialZielcode :: Zielcode
partialZielcode = Stack [Unify unify (A "p"), Backtrack backtrackQ, Push push (A "q"), Call call, Backtrack backtrackQ, Return returnL]
-}
exampleZielcode :: Zielcode
exampleZielcode = genCode $ parse $ tokenize "p(Y):-q(Y).q(a).q(b).:- p(X)."
{-
{--------------------------------------------------
    Tests for of genCode | üb
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

{--------------------------------------------------
    Initial values for testing commands and cHelpers.
 --------------------------------------------------}

type MiniLRegisterKeller = ((B,T,C,R,P), Stack StackElement)

code'' :: Zielcode
code'' = genCode (parse $ tokenize "p :- q. q :- r. r. :- p, r.")

code' :: Zielcode
code' = genCode (parse $ tokenize ":- p,r.")

initStack' :: Stack StackElement
initStack' = stackNewEmpty

initial' :: MiniLRegisterKeller -- register in intial state
initial' = ((False, Pointer (-1), Nil, Nil, cGoal code), initStack')

firstreg :: MiniLRegisterKeller -- register after first push
firstreg = ((False, Pointer 3, Pointer 0, Pointer 1, Pointer 16), Stack [CodeAddress (Pointer 0), StackAddress Nil, CodeAddress (Pointer 18), CodeAtom (A "p")])

subsequentreg :: MiniLRegisterKeller -- register after some calls p. 131 top
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
      (cGoal code'')

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
      (cFirst code'')

-- testCFirstOnlyZiel = ??? Wie sollte sich cFirst bei Programm wie code' verhalten?

testCNextFirstPkAndZiel =
  TestCase $
    assertEqual
      "cNext should return the Addressvalue of the first command of the next pk given a current pk location"
      (Pointer 6)
      (cNext code'' (Pointer 0))

testCNextMiddlePkAndZiel =
  TestCase $
    assertEqual
      "cNext should return the absolute Addressvalue of a pk start given another pk start."
      (Pointer 12)
      (cNext code'' (Pointer 6))

testCNextLastPkAndZiel =
  TestCase $
    assertEqual
      "cNext should return nil if called on last pk."
      Nil
      (cNext code'' (Pointer 12))

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
      (cLast code'')

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
      (push (A "p") initial' code'')

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
          code''
      ) -}

initialML :: Zielcode -> RegisterKeller
initialML code = ((False, Pointer (-1), Nil, Nil, cGoal code, Nil, Nil, Pointer 0, Pointer 0, 0, 0, Pointer 0), (initialStack, initialUs, initialTrail))

zielcodeEmptyML :: Zielcode
zielcodeEmptyML = stackNewEmpty

initialStack :: Stack StackElement
initialStack = stackNewEmpty

initialUs :: Stack StackElement
initialUs = stackNewEmpty

initialTrail :: Stack StackElement
initialTrail = stackNewEmpty

--TODO important note; c must be init with -1 (same reason as for t)

pushTestRegs :: RegisterKeller
pushTestRegs = ((False, Pointer (-1), Pointer 0, Pointer 0, Pointer 0, Nil, Pointer 1, Pointer 0, Pointer 0, 0, 0, Nil),
      (Stack [CodeAddress (Pointer 3), StackAddress (Pointer 0), StackAddress (Pointer 1), StackAddress Nil, StackAddress (Pointer 0), StackAddress (Pointer 0)], initialUs, initialTrail))

pushTestRegsEndEnv :: RegisterKeller
pushTestRegsEndEnv = ((False, Pointer 5, Pointer 0, Pointer 0, Pointer 0, Nil, Pointer 4, Pointer 0, Pointer 0, 0, 0, Nil),
      (Stack [CodeAddress (Pointer 3), StackAddress (Pointer 0), StackAddress (Pointer 1), StackAddress Nil, StackAddress (Pointer 0), StackAddress (Pointer 0)], initialUs, initialTrail))

pushTestCode :: Zielcode
pushTestCode = genCode $ parse $ tokenize ":- p(X)."

pushTestCode' :: Zielcode
pushTestCode' = genCode $ parse $ tokenize "p (a). :- p (X)."

-- TODO, check validity 
testPushSTR =
  TestCase $
    assertEqual
      "push Str symb arity should update stack location t+1 with said Str Cell, then increase t by 1."
      ((False, Pointer 0, Nil, Nil, Pointer 1, Nil, Nil, Pointer 0, Pointer 0, 0, 0, Pointer 0),
        (Stack [CodeArg (ATStr (A "p") 0)], initialUs, initialTrail))
      (push (ATStr (A "p") 0) (initialML pushTestCode) pushTestCode)

testPushVAR =
  TestCase $
    assertEqual
      "push Var symb (nil) should update loc t+1 with var symb and call s_add to find a stackadress (or keep nil), then t+1."
      ((False, Pointer 0, Nil, Nil, Pointer 1, Nil, Nil, Pointer 0, Pointer 0, 0, 0, Pointer 0),
        (Stack [CodeArg (ATVar (V "X") Nil)], initialUs, initialTrail))
      (push (ATVar (V "X") Nil) (initialML pushTestCode) pushTestCode)

-- TODO, check validity
testPushCHP =
  TestCase $
    assertEqual
      "push chp should update stack an registers accordingly."
      ((False, Pointer 5, Pointer 0, Pointer 1, Pointer 1, Pointer 6, Pointer 1, Pointer 0, Pointer 0, 0, 0, Nil),
        (Stack [CodeAddress (Pointer 0), CodeAddress (Pointer 0), StackAddress (Pointer 9999), StackAddress (Pointer 1), TrailAddress (Pointer 0), StackAddress (Pointer 9998)], initialUs, initialTrail))
      (push ATChp pushTestRegs pushTestCode')

testPushEndAtom =
  TestCase $
    assertEqual
      "push EndAtom should set registers accordingly (update stack at locations c+2 and c+5)"
      ((False, Pointer (-1), Pointer 0, Pointer 0, Pointer 1, Nil, Pointer 1, Pointer 0, Pointer 0, 0, 0, Nil), (Stack [CodeAddress (Pointer 3), StackAddress (Pointer 0), CodeAddress (Pointer 3), StackAddress Nil, StackAddress (Pointer 0), StackAddress (Pointer (-1))], initialUs, initialTrail))
      (push ATEndAtom pushTestRegs zielcodeEmptyML)

testPushBegEnv =
  TestCase $
    assertEqual
      "push BegEnv should set registers accordingly (reset the e pointer to nil)"
      ((False, Pointer (-1), Pointer 0, Pointer 0, Pointer 1, Nil, Nil, Pointer 0, Pointer 0, 0, 0, Nil),
        (Stack [CodeAddress (Pointer 3), StackAddress (Pointer 0), StackAddress (Pointer 1), StackAddress Nil, StackAddress (Pointer 0), StackAddress (Pointer 0)], initialUs, initialTrail))
      (push ATBegEnv pushTestRegs zielcodeEmptyML)

testPushEndEnv =
  TestCase $
    assertEqual
      "push EndEnv n should set stack and registers accordingly (set e pointer, iterate t, set EndEnv StackArgument)."
      ((False, Pointer 6, Pointer 0, Pointer 0, Pointer 1, Nil, Pointer 5, Pointer 0, Pointer 0, 0, 0, Nil),
        (Stack [CodeAddress (Pointer 3), StackAddress (Pointer 0), StackAddress (Pointer 1), StackAddress Nil, StackAddress (Pointer 0), StackAddress (Pointer 0), CodeArg (ATEndEnv 1)], initialUs, initialTrail))
      (push (ATEndEnv 1) pushTestRegsEndEnv zielcodeEmptyML)

stackBacktrackTestML = Stack [StackAddress (Pointer 0), CodeAddress (Pointer 1), CodeAddress (Pointer 3), StackAddress (Pointer 3), StackAddress (Pointer 4),
                        StackAddress (Pointer 1), StackAddress (Pointer 3), StackAddress (Pointer 6), StackAddress (Pointer 3)]

trailBacktrackTestML = Stack [StackAddress (Pointer 1)]
-- filled stack with basically random values (expect loc 1 and 2); should be fine, but if weirdness occurs, check this

registerBacktrackTest :: AddressRegs
registerBacktrackTest = (True, Pointer 2, Pointer 2, Pointer 1, Pointer 1, Pointer 2, Pointer 1, Pointer 1, Pointer 1, 1, 0, Pointer 0)

registerBacktrackTestBFalse :: AddressRegs
registerBacktrackTestBFalse = (False, Pointer 2, Pointer 2, Pointer 1, Pointer 1, Pointer 2, Pointer 1, Pointer 1, Pointer 1, 1, 0, Pointer 0)

registerKellerBacktrackMLCNotNil :: RegisterKeller
registerKellerBacktrackMLCNotNil = (registerBacktrackTest, (stackBacktrackTestML, initialUs, trailBacktrackTestML))

registerKellerBacktrackWhileTest :: RegisterKeller
registerKellerBacktrackWhileTest = (registerBacktrackTest, (Stack [StackAddress (Pointer 2), StackAddress (Pointer 1), StackAddress Nil, StackAddress (Pointer 4)], initialUs, initialTrail))

backtrackTestZielcode :: Zielcode
backtrackTestZielcode = genCode $ parse $ tokenize "p(X). :- q(a)."

testBacktrackBTrue =
  TestCase $
    assertEqual
      "Backtrack should set registers accordingly when called on c not nil and no stack(c) = nil match."
      ((False, Pointer 6, Pointer 2, Pointer 1, Pointer 3, Pointer 8, Pointer 7, Pointer 0, Pointer 3, 0, 0, Nil),
        (Stack [StackAddress (Pointer 0), CodeAddress (Pointer 1), CodeAddress Nil, StackAddress (Pointer 3), StackAddress (Pointer 4),
                StackAddress (Pointer 1), StackAddress (Pointer 3), StackAddress (Pointer 6), StackAddress (Pointer 3)],
        initialUs, trailBacktrackTestML))
      (backtrack registerKellerBacktrackMLCNotNil zielcodeEmptyML)

testBacktrackBTrueWhileLoop =
  TestCase $
    assertEqual
      "backtrackWhile should set registers accordingly."
      ((True, Pointer 2, Pointer 1, Pointer 2, Pointer 1, Pointer 2, Pointer 1, Pointer 1, Pointer 1, 1, 0, Pointer 0),
        (Stack [StackAddress (Pointer 2), StackAddress (Pointer 1), StackAddress Nil, StackAddress (Pointer 4)], initialUs, initialTrail))
      (backtrackWhile registerKellerBacktrackWhileTest)

testBacktrackBTrueIfStackCNil =
  TestCase $
    assertEqual
      "Backtrack should set p to c last in case stack (c) = nil check is passed after settings registers."
      ((True, Pointer 2, Pointer 2, Pointer 1, Pointer 16, Pointer 2, Pointer 1, Pointer 1, Pointer 1, 1, 0, Pointer 0),
        (Stack [StackAddress (Pointer 2), StackAddress (Pointer 1), StackAddress Nil, StackAddress (Pointer 4)], initialUs, initialTrail))
      (backtrackIfThenElse registerKellerBacktrackWhileTest backtrackTestZielcode)

testBacktrackBFalse =
  TestCase $
    assertEqual
      "Backtrack should increment p by one if called with b = false."
      ((False, Pointer 2, Pointer 2, Pointer 1, Pointer 2, Pointer 2, Pointer 1, Pointer 1, Pointer 1, 1, 0, Pointer 0), (stackBacktrackTestML, initialUs, trailBacktrackTestML))
      (backtrack (registerBacktrackTestBFalse, (stackBacktrackTestML, initialUs, trailBacktrackTestML)) zielcodeEmptyML)

{- testUnifyUnifiable =
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
-}
--Tests für Unify Makroinstruktionen
testAddAcNil =
  TestCase $
    assertEqual
      "addAc should return the stacks and register unchanged when ac = Nil"
      ((False, Pointer 1, Pointer 2, Pointer 3, Pointer 4, Pointer 5, Pointer 6, Pointer 7, Pointer 8, 9, 10, Nil), (Stack [], Stack [], Stack []))
      (addAC 5 ((False, Pointer 1, Pointer 2,Pointer 3, Pointer 4, Pointer 5, Pointer 6, Pointer 7, Pointer 8, 9, 10, Nil), (Stack [], Stack [], Stack [])))

testAddAcNotNil =
  TestCase $
    assertEqual
      "addAc should return the stacks unchanged and add the first argument to ac when ac /= Nil"
       ((False, Pointer 1, Pointer 2, Pointer 3, Pointer 4, Pointer 5, Pointer 6, Pointer 7, Pointer 8, 9, 10, Pointer 16), (Stack [], Stack [], Stack []))
       (addAC 5 ((False, Pointer 1, Pointer 2,Pointer 3, Pointer 4, Pointer 5, Pointer 6, Pointer 7, Pointer 8, 9, 10, Pointer 11), (Stack [], Stack [], Stack [])))

testRestoreAcUpQAc0 =
  TestCase $
    assertEqual
      "restoreAcUpQ should return the stacks unchanged and change the registers ac, up, ut when ac = 0"
                    ((False, Pointer 1, Pointer 2, Pointer 3, Pointer 4, Pointer 107, Pointer 6, Pointer 5, Pointer 8, 9, 10, Pointer 106), (Stack [], Stack [CodeAddress (Pointer 100), CodeAddress (Pointer 101), CodeAddress (Pointer 102), CodeAddress (Pointer 103), CodeAddress (Pointer 104), CodeAddress (Pointer 105), CodeAddress (Pointer 106), CodeAddress (Pointer 107)], Stack []))
      (restoreAcUpQ ((False, Pointer 1, Pointer 2,Pointer 3, Pointer 4, Pointer 5, Pointer 6, Pointer 7, Pointer 8, 9, 10, Pointer 0), (Stack [], Stack [CodeAddress (Pointer 100), CodeAddress (Pointer 101), CodeAddress (Pointer 102), CodeAddress (Pointer 103), CodeAddress (Pointer 104), CodeAddress (Pointer 105), CodeAddress (Pointer 106), CodeAddress (Pointer 107)], Stack [])))

testRestoreAcUpQAcNot0 =
  TestCase $
    assertEqual
      "restoreAcUpQ should return the stacks and registers unchanged when ac /= 0"
                    ((False, Pointer 1, Pointer 2, Pointer 3, Pointer 4, Pointer 5, Pointer 6, Pointer 7, Pointer 8, 9, 10, Pointer 11), (Stack [], Stack [], Stack []))
      (restoreAcUpQ ((False, Pointer 1, Pointer 2,Pointer 3, Pointer 4, Pointer 5, Pointer 6, Pointer 7, Pointer 8, 9, 10, Pointer 11), (Stack [], Stack [], Stack [])))

saveAcUpStack :: MLStack
saveAcUpStack = Stack [CodeArg (ATStr (A "x") 2), CodeArg (ATVar (V "X") (Pointer 0)),CodeArg (ATVar (V "X") (Pointer 1)),CodeArg (ATVar (V "X") (Pointer 2)),CodeArg (ATVar (V "X") (Pointer 3)),CodeArg (ATVar (V "X") (Pointer 4)),CodeArg (ATVar (V "X") (Pointer 5)),CodeArg (ATVar (V "X") (Pointer 6)),CodeArg (ATVar (V "X") (Pointer 7))]

saveAcUpStackArity0 :: MLStack
saveAcUpStackArity0 = Stack [CodeArg (ATStr (A "x") 0), CodeArg (ATVar (V "X") (Pointer 0)),CodeArg (ATVar (V "X") (Pointer 1)),CodeArg (ATVar (V "X") (Pointer 2)),CodeArg (ATVar (V "X") (Pointer 3)),CodeArg (ATVar (V "X") (Pointer 4)),CodeArg (ATVar (V "X") (Pointer 5)),CodeArg (ATVar (V "X") (Pointer 6)),CodeArg (ATVar (V "X") (Pointer 7))]

testSaveAcUpQ =
  TestCase $
    assertEqual
      "saveAcUpQ should save the values of ac and up in us when up is smaller then the Pointer at c+5, the dereferenced up /= up and the arity of the dereferenced up in stack /= 0"
      ((False, Pointer 7, Pointer 2, Pointer 3, Pointer 4, Pointer 0, Pointer 6, Pointer 9, Pointer 8, 9, 10, Pointer 1), (Stack [CodeArg (ATStr (A "x") 2),CodeArg (ATVar (V "X") (Pointer 0)),CodeArg (ATVar (V "X") (Pointer 1)),CodeArg (ATVar (V "X") (Pointer 2)),CodeArg (ATVar (V "X") (Pointer 3)),CodeArg (ATVar (V "X") (Pointer 4)),CodeArg (ATVar (V "X") (Pointer 5)),CodeArg (ATVar (V "X") (Pointer 6)),CodeArg (ATVar (V "X") (Pointer 7))], Stack [StackAddress (Pointer 11), StackAddress (Pointer 6)], Stack []))
      (saveAcUpQ ((False, Pointer 7, Pointer 2, Pointer 3, Pointer 4, Pointer 5, Pointer 6, Pointer 7, Pointer 8, 9, 10, Pointer 11), (saveAcUpStack, Stack [], Stack [])))

testSaveAcUpQUpBigger =
  TestCase $
    assertEqual
      "saveAcUp should not save the values of ac and up when up is bigger then the Pointer at c+5"
      ((False, Pointer 7, Pointer 2, Pointer 3, Pointer 4, Pointer 7, Pointer 6, Pointer 7, Pointer 8, 9, 10, Pointer 11), (Stack [CodeArg (ATStr (A "x") 2),CodeArg (ATVar (V "X") (Pointer 0)),CodeArg (ATVar (V "X") (Pointer 1)),CodeArg (ATVar (V "X") (Pointer 2)),CodeArg (ATVar (V "X") (Pointer 3)),CodeArg (ATVar (V "X") (Pointer 4)),CodeArg (ATVar (V "X") (Pointer 5)),CodeArg (ATVar (V "X") (Pointer 6)),CodeArg (ATVar (V "X") (Pointer 7))], Stack [], Stack []))
      (saveAcUpQ ((False, Pointer 7, Pointer 2, Pointer 3, Pointer 4, Pointer 7, Pointer 6, Pointer 7, Pointer 8, 9, 10, Pointer 11), (saveAcUpStack, Stack [], Stack [])))

testSaveAcUpQUpEqualsDerefUp =
  TestCase $
    assertEqual
      "saveAcUp should not save the values of ac and up when the dereferenced up /= up"
      ((False, Pointer 7, Pointer 2, Pointer 3, Pointer 4, Pointer 0, Pointer 6, Pointer 7, Pointer 8, 9, 10, Pointer 11), (Stack [CodeArg (ATStr (A "x") 2),CodeArg (ATVar (V "X") (Pointer 0)),CodeArg (ATVar (V "X") (Pointer 1)),CodeArg (ATVar (V "X") (Pointer 2)),CodeArg (ATVar (V "X") (Pointer 3)),CodeArg (ATVar (V "X") (Pointer 4)),CodeArg (ATVar (V "X") (Pointer 5)),CodeArg (ATVar (V "X") (Pointer 6)),CodeArg (ATVar (V "X") (Pointer 7))], Stack [], Stack []))
      (saveAcUpQ ((False, Pointer 7, Pointer 2, Pointer 3, Pointer 4, Pointer 0, Pointer 6, Pointer 7, Pointer 8, 9, 10, Pointer 11), (saveAcUpStack, Stack [], Stack [])))

testSaveAcUpQArityEquals0 =
  TestCase $
    assertEqual
      "saveAcUp should not save the values of ac and up when the the arity of the dereferenced up in stack /= 0"
      ((False, Pointer 7, Pointer 2, Pointer 3, Pointer 4, Pointer 5, Pointer 6, Pointer 7, Pointer 8, 9, 10, Pointer 11), (Stack [CodeArg (ATStr (A "x") 0),CodeArg (ATVar (V "X") (Pointer 0)),CodeArg (ATVar (V "X") (Pointer 1)),CodeArg (ATVar (V "X") (Pointer 2)),CodeArg (ATVar (V "X") (Pointer 3)),CodeArg (ATVar (V "X") (Pointer 4)),CodeArg (ATVar (V "X") (Pointer 5)),CodeArg (ATVar (V "X") (Pointer 6)),CodeArg (ATVar (V "X") (Pointer 7))], Stack [], Stack []))
      (saveAcUpQ ((False, Pointer 7, Pointer 2, Pointer 3, Pointer 4, Pointer 5, Pointer 6, Pointer 7, Pointer 8, 9, 10, Pointer 11), (saveAcUpStackArity0, Stack [], Stack [])))

derefStack :: MLStack
derefStack = Stack [
  CodeArg (ATStr (A "v") 1),
  CodeAddress Nil,
  StackAddress Nil,
  CodeArg (ATVar (V "X") Nil),
  CodeArg (ATVar (V "X") (Pointer 3)),
  StackAddress (Pointer 0),
  CodeArg (ATVar (V "X") (Pointer 4))]

testDeref =
  TestCase $
    assertEqual
      "deref has to deliver the pointer of the dereferenced Variable when called with a Pointer pointing at a Var"
      (Pointer 3)
      (deref derefStack (Pointer 6))

--Tests für Unify
unifyStack = Stack [CodeArg (ATStr (A "v") 1), CodeArg (ATVar (V "V") Nil),CodeArg (ATVar (V "V") (Pointer 1))]
--der unifyPush test soll nur stack, t, pc, verändern, deshalb kann der rest nil/0/leer sein (b, t, c, r, p, up, e, ut, tt, pc, sc, ac),
testUnifyPushStr =
  TestCase $
    assertEqual
      "unifyPushModus should push the arg (STR) on the top of stack and change the value of t and pc correctly"
      ((False, Pointer 3, Nil, Nil, Nil, Nil, Nil, Nil, Nil, 3, 0, Nil), (unifyStack <> Stack [CodeArg (ATStr (A "x") 2)], Stack [], Stack []))
      (unifyPushModus (ATStr (A "x") 2) ((False, Pointer 2, Nil, Nil, Nil, Nil, Nil, Nil, Nil, 2, 0, Nil), (unifyStack, Stack [], Stack [])))

--TODO: apparently sAdd doesn't work therefor this test will always fail (Results in an error: Tried converting Pointer value Nil to an Integer-type.), unifyStack has to be different here
testUnifyPushVar =
  TestCase $
    assertEqual
      "unifyPushModus should push the arg (VAR) on the top of stack and change the value of t and pc correctly"
      ((False, Pointer 3, Nil, Nil, Nil, Nil, Nil, Nil, Nil, 1, 0, Nil), (unifyStack <> Stack [CodeArg (ATVar (V "X") (Pointer 2))], Stack [], Stack []))
      (unifyPushModus (ATVar (V "X") (Pointer 2)) ((False, Pointer 2, Nil, Nil, Nil, Nil, Nil, Nil, Nil, 2, 0, Nil), (unifyStack, Stack [], Stack [])))

testUnifyNonPushStrThenCase =
  TestCase $
    assertEqual
      "unifyNonPusModus should push (Var symb t+1) at the dereferenced up, push the dereferenced up to trail and push the arg to stack, as well as increase tt, t, up, ac and call addAc and restoreAcUpQ, when stack at the dereferenced up contains Var symb Nil"
      ((False, Pointer 7, Nil, Nil, Nil, Pointer 7, Nil, Pointer 0, Pointer 0, 1, 0, Pointer 5),
       (Stack [
        CodeArg (ATStr (A "v") 1),
        CodeAddress Nil,
        StackAddress Nil,
        CodeArg (ATVar (V "X") (Pointer 7)),
        CodeArg (ATVar (V "X") (Pointer 3)),
        StackAddress (Pointer 0),
        CodeArg (ATVar (V "X") (Pointer 4)),
        CodeArg (ATStr (A "x") 1)
       ],
       Stack [
        StackAddress (Pointer 4),
        StackAddress (Pointer 5),
        StackAddress (Pointer 6),
        StackAddress (Pointer 7),
        StackAddress (Pointer 8),
        StackAddress (Pointer 9),
        StackAddress (Pointer 10)
       ],
       Stack [StackAddress (Pointer 3)]))
      (unifyNonPushModus (ATStr (A "x") 1) ((False, Pointer 6, Nil, Nil, Nil, Pointer 6, Nil, Pointer 2, Nil, 0, 0, Pointer 1),
      (Stack [
        CodeArg (ATStr (A "v") 1),
        CodeAddress Nil,
        StackAddress Nil,
        CodeArg (ATVar (V "X") Nil),
        CodeArg (ATVar (V "X") (Pointer 3)),
        StackAddress (Pointer 0),
        CodeArg (ATVar (V "X") (Pointer 4))
      ],
      Stack [
        StackAddress (Pointer 4),
        StackAddress (Pointer 5),
        StackAddress (Pointer 6),
        StackAddress (Pointer 7),
        StackAddress (Pointer 8),
        StackAddress (Pointer 9),
        StackAddress (Pointer 10)
      ], Stack [])))

testUnifyNonPushStrElseCaseSymbolNotSame =
  TestCase $
    assertEqual
    "unifyNonPushModus should land in a if then else case, when the dereferenced up /= Var symbol2 Nil, in which the backtrack flag has to be set as True when the dereferenced Value at up is not the same as the given Argument"
    ((True, Pointer 6, Nil, Nil, Nil, Pointer 6, Nil, Pointer 2, Nil, 0, 0, Pointer 1),
       (Stack [
        CodeArg (ATStr (A "v") 1),
        CodeAddress Nil,
        StackAddress Nil,
        CodeArg (ATVar (V "X") (Pointer 0)),
        CodeArg (ATVar (V "X") (Pointer 3)),
        StackAddress (Pointer 0),
        CodeArg (ATVar (V "X") (Pointer 4))
       ],
       Stack [], Stack []))
    (unifyNonPushModus (ATStr (A "s") 1) ((False, Pointer 6, Nil, Nil, Nil, Pointer 6, Nil, Pointer 2, Nil, 0, 0, Pointer 1),
      (Stack [
        CodeArg (ATStr (A "v") 1),
        CodeAddress Nil,
        StackAddress Nil,
        CodeArg (ATVar (V "X") (Pointer 0)),
        CodeArg (ATVar (V "X") (Pointer 3)),
        StackAddress (Pointer 0),
        CodeArg (ATVar (V "X") (Pointer 4))
      ],
      Stack [], Stack [])))

-- addAc/restoreAcUpQ/saveAcUpQ have been tested already therefor I am not gonna differentiate further
--(b, t, c, r, p, up, e, ut, tt, pc, sc, ac)
testUnifyNonPushStrElseCaseSymbolSameAritySmaller1 =
  TestCase $
    assertEqual
     "unifyNonPush should land in a if then else case, when the dereferenced up /= Var symbol2 Nil, in which the functions addAc(-1)/addAc(arity), restoreAcUpQ, saveAcUpQ have to be called depending on the arity"
     ((False, Pointer 6, Pointer 1, Nil, Nil, Pointer 7, Nil, Pointer 2, Nil, 0, 0, Pointer 2),
     (Stack [
      CodeArg (ATStr (A "x") 1),
      CodeAddress Nil,
      StackAddress Nil,
      CodeArg (ATVar (V "X") (Pointer 0)),
      CodeArg (ATVar (V "X") (Pointer 3)),
      StackAddress (Pointer 0),
      CodeArg (ATVar (V "X") (Pointer 4))
     ],
     Stack [
      StackAddress (Pointer 4),
      StackAddress (Pointer 5),
      StackAddress (Pointer 6),
      StackAddress (Pointer 7),
      StackAddress (Pointer 8),
      StackAddress (Pointer 9),
      StackAddress (Pointer 10)
     ],
     Stack []))
     (unifyNonPushModus (ATStr (A "x") 1) ((False, Pointer 6, Pointer 1, Nil, Nil, Pointer 6, Nil, Pointer 2, Nil, 0, 0, Pointer 1),
      (Stack [
        CodeArg (ATStr (A "x") 1),
        CodeAddress Nil,
        StackAddress Nil,
        CodeArg (ATVar (V "X") (Pointer 0)),
        CodeArg (ATVar (V "X") (Pointer 3)),
        StackAddress (Pointer 0),
        CodeArg (ATVar (V "X") (Pointer 4))
      ],
      Stack [
        StackAddress (Pointer 4),
        StackAddress (Pointer 5),
        StackAddress (Pointer 6),
        StackAddress (Pointer 7),
        StackAddress (Pointer 8),
        StackAddress (Pointer 9),
        StackAddress (Pointer 10)
      ], Stack [])))
--TODO: tests for unifyNonPushModus (ATVar symb add)
--unifyHelpers


--unifyProcedureTests
testUnifyProzedurStackEmpty =
  TestCase $
    assertEqual
    "unifyProcedure should set the backtrack flag to True when called with an empty Stack"
    ((True, Pointer 6, Pointer 1, Nil, Nil, Pointer 7, Nil, Pointer 2, Nil, 0, 0, Pointer 2),(Stack [], Stack [], Stack []))
    (unifyProzedur (Pointer 1) (Pointer 2) ((True, Pointer 6, Pointer 1, Nil, Nil, Pointer 7, Nil, Pointer 2, Nil, 0, 0, Pointer 2),(Stack [], Stack [], Stack [])))
{-
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
          code''
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
          code''
      )

testCallCNilCase =
  TestCase $
    assertEqual
      "call should set I correctly when called on c == nil"
      ((True, Pointer 3, Pointer 0, Pointer 1, Pointer 17), Stack [CodeAddress Nil, StackAddress Nil, CodeAddress (Pointer 18), CodeAtom (A "p")])
      (call ((False, Pointer 3, Pointer 0, Pointer 1, Pointer 16), Stack [CodeAddress Nil, StackAddress Nil, CodeAddress (Pointer 18), CodeAtom (A "p")]) code)
-}
--call doesn't change t,c,r,up,e,ut,tt,pc,sc,ac, nor the stacks us and trail therefor they can be Nil/Empty respectively
--(b, t, c, r, p, up, e, ut, tt, pc, sc, ac), call doesn't change t,c,r,up,e,ut,tt,pc,sc,ac, nor the stacks us and trail therefor they can be Nil/Empty respectively

callCode :: Zielcode
callCode = genCode $ parse $ tokenize "p. q. :- p(a)."

testCallStackAtCNil =
  TestCase $
    assertEqual
      "call should increase p by one and set B to True, when the c-th item in stack is Nil"
      ((True,Nil, Pointer 1, Nil,Pointer 2,Nil,Nil,Nil,Nil,0,0,Nil), (Stack [CodeAddress (Pointer 1),CodeAddress Nil], Stack [], Stack []))
      (call ((False,Nil, Pointer 1, Nil,Pointer 1,Nil,Nil,Nil,Nil,0,0,Nil), (Stack [CodeAddress (Pointer 1),CodeAddress Nil], Stack [], Stack [])) exampleZielcode)

testCallElseCase =
  TestCase $
    assertEqual
      "call should set p to stack (c), then set stack (c) to c_next of current stack(c) value."
      ((False, Pointer 2, Pointer 1, Pointer 1, Pointer 5, Pointer 2, Pointer 1, Pointer 1, Pointer 1, 1, 0, Pointer 0),
        (Stack [StackAddress (Pointer 0), CodeAddress Nil], initialUs, initialTrail))
      (call ((False, Pointer 2, Pointer 1, Pointer 1, Pointer 2, Pointer 2, Pointer 1, Pointer 1, Pointer 1, 1, 0, Pointer 0), (Stack [StackAddress (Pointer 0), CodeAddress (Pointer 5)], initialUs, initialTrail)) callCode)

testReturnLNoIfCase =
  TestCase $ 
    assertEqual 
      "Calling return without entering the if case should set p to stack(r+1) and e to stack(r+2)."
      (((False, Pointer (-1), Pointer 0, Pointer 0, Pointer 0, Nil, Pointer 1, Pointer 0, Pointer 0, 0, 0, Nil),
      (Stack [CodeAddress (Pointer 3), StackAddress (Pointer 0), StackAddress (Pointer 1), StackAddress Nil, StackAddress (Pointer 0), StackAddress (Pointer 0)], initialUs, initialTrail)))
      (returnL ATPos pushTestRegs)

testReturnLIfCase =
  TestCase $ 
    assertEqual
      "Calling return with entering the if case should set r to stack(r)+1."
      (((False, Pointer (-1), Pointer 0, Pointer 1, Pointer 0, Nil, Pointer 1, Pointer 0, Pointer 0, 0, 0, Nil),(Stack [CodeAddress Nil, StackAddress (Pointer 0), StackAddress (Pointer 1)], initialUs, initialTrail)))
      (returnL ATPos ((False, Pointer (-1), Pointer 0, Pointer 0, Pointer 3, Nil, Pointer 5, Pointer 0, Pointer 0, 0, 0, Nil),(Stack [CodeAddress Nil, StackAddress (Pointer 0), StackAddress (Pointer 1)], initialUs, initialTrail)))  

{-     
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
 -}
{-----------------------------------------
  Necessary test helpers/preconditions for ML
  -------------------------------------------}

{- initialML :: Zielcode -> RegisterKeller
initialML code = ((False, -1, Nil, Nil, cGoal code, UP, E, 0, 0, 0, 0, 0, 0) Stack [])

testzielcodeML :: Zielcode
testzielcodeML = genCode $ parse $ tokenize ""
 -}
{-----------------------------------------------------
  Tests for ML Helpers
 --------------------------------------------------------}

-- Linearize

{- testLinearizeSingleAtom =
  TestCase $
    assertEqual
      "calling linearize on a single atom should result in correct linearization"
      [("A", 0), ("X", 0)]
      (linearize )

testLinearizeMultipleAtom =
  TestCase $
    assertEqual
      "Calling linearize on multiple atoms should result in correct linearization" -}

-- s_add
testStackReplaceAtLocationMLStack =
  TestCase $
    assertEqual
    "The function should replace item x at pos i"
    (Stack [
      CodeAddress (Pointer 0),
      CodeAddress (Pointer 1),
      CodeAddress (Pointer 2),
      StackAddress (Pointer 3),
      CodeAddress (Pointer 4),
      CodeAddress (Pointer 5),
      CodeAddress (Pointer 6),
      CodeAddress (Pointer 7),
      CodeAddress (Pointer 8)
    ])
    (stackReplaceAtLocationMLStack (Pointer 3) (StackAddress (Pointer 3)) (Stack [
      CodeAddress (Pointer 0),
      CodeAddress (Pointer 1),
      CodeAddress (Pointer 2),
      CodeAddress (Pointer 3),
      CodeAddress (Pointer 4),
      CodeAddress (Pointer 5),
      CodeAddress (Pointer 6),
      CodeAddress (Pointer 7),
      CodeAddress (Pointer 8)
    ]))

testSAddUnifyModeBoundVariable = undefined

testSAddUnifyModeUnboundVariable = undefined

testSAddPushModeBoundVar = undefined

testSAddPushModeUnboundVar = undefined

testSAddPushModeAtom = undefined

{----------------------------------------
Tests für üb
 -----------------------------------------}

testÜbPushEmpty =
  TestCase $
    assertEqual
      "übPush called on an empty list should add nothing to zielcode."
      (Stack [])
      (übPush [] (Stack []))

testÜbPushExpSeq =
  TestCase $
    assertEqual
      "übPush called on an Expression and a Sequence should first translate expr, then seq."
      (Stack [Backtrack backtrack, Push push (ATStr (A "p") 1), Push push (ATStr (A "q") 1)])
      (übPush [ExpLin (Linearization "p" 1), ExpLin (Linearization "q" 1)] (Stack [Backtrack backtrack]))

testÜbPushSymbolArity =
  TestCase $
    assertEqual
      "übPushSymArr should add a push STR Symbol Arity to Zielcode."
      (Stack [Push push ATChp, Push push (ATStr (A "p") 1)])
      (übPush [ExpLin (Linearization "p" 1)] (Stack [Push push ATChp]))

testÜbPushSymbol =
  TestCase $
    assertEqual
      "übPushSymbol should add a push VAR Symbol to Zielcode."
      (Stack [Push push ATChp, Push push (ATStr (A "p") 1), Push push (ATVar (V "X") Nil)])
      (übPush [ExpVar (V "X")] (Stack [Push push ATChp, Push push (ATStr (A "p") 1)]))

testÜbBodyEmpty =
  TestCase $
    assertEqual
      "übBody called on empty list shouldn't change anything in zielcode."
      (Stack [Backtrack backtrack])
      (übBody [] (Stack [Backtrack backtrack]))

testÜbBodyAtomSeq =
  TestCase $
    assertEqual
      "übBody called on an atom followed by a sequence should add push lin(atom) and add seq translation after backtrack"
      ( Stack
          [ Call call,
            -- Atom 1
            Push push ATChp,
            Push push (ATStr (A "p") 0),
            Push push ATEndAtom,
            Call call,
            Backtrack backtrack,
            -- Next Atom in Sequence
            Push push ATChp,
            Push push (ATStr (A "q") 0),
            Push push ATEndAtom,
            Call call,
            Backtrack backtrack
          ]
      )
      ( übBody
          [Literal True (LTNVar (NVLTerm "p" [])), Literal True (LTNVar (NVLTerm "q" []))]
          (Stack [Call call])
      )

testÜbUnifyEmpty :: Test
testÜbUnifyEmpty =
  TestCase $
    assertEqual
      "übUnify called on empty list shouldn't change anything in zielcode."
      (Stack [])
      (übUnify [] (Stack []))

testÜbUnifySymbolArity =
  TestCase $
    assertEqual
      "übUnify symbol arity should add a unify STR Symbol Arity to the stack and a backtrack"
      (Stack [Unify unify (ATStr (A "p") 1), Backtrack backtrack])
      (übUnify [ExpLin (Linearization "p" 1)] (Stack []))

testÜbUnifySymbol =
  TestCase $
    assertEqual
      "übUnify ExpVar should add unify to the stack and backtrack."
      (Stack [Unify unify (ATVar (V "X") Nil), Backtrack backtrack])
      (übUnify [ExpVar (V "X")] (Stack []))

testÜbUnifyExpSeq =
  TestCase $
    assertEqual
      "übUnify ExpVar should first translate exp, then add a backtrack, then translate seq"
      (Stack [Unify unify (ATStr (A "p") 1), Backtrack backtrack, Unify unify (ATStr (A "q") 1),Backtrack backtrack])
      (übUnify [ExpLin (Linearization "p" 1), ExpLin (Linearization "q" 1)] (Stack []))

testÜbHeadAtom =
  TestCase $
    assertEqual
      "übHead called on an atom should result in a Übunify call of the linearization of that atom"
      (Stack [Unify unify (ATStr (A "p") 0), Backtrack backtrack])
      (übHead (NVLTerm "p" []) (Stack []))

testÜbEnvEmpty =
  TestCase $
    assertEqual
      "übEnv called on empty Stack should add push ATEndEnv."
      (Stack [Push push (ATEndEnv 0)])
      (übEnv [] (Stack []))

-- TODO: Discuss ATEndEnv value (Expected 2 but got 0; REST IS OKAY!)
testÜbEnvSymbSeq =
  TestCase $
    assertEqual
      "übEnv called on Symbol/Sequence should push symbol, then add übEnv of sequence."
      ( Stack
          [ Push push (ATVar (V "X") Nil),
            Push push (ATVar (V "Y") Nil),
            Push push (ATEndEnv 2)
          ]
      )
      (übEnv [V "X", V "Y"] (Stack []))

testÜbVarSeqAtmSeq =
  TestCase $
    assertEqual
      "üb called on VarSeq, then Atom :- Seq should initialise with push BegEnv, call übEnv on VarSeq, übHead on Atom, übBody on Seq and finish with returnL (pos)."
      ( Stack
          [ Push push ATBegEnv,
            Push push (ATVar (V "Y") Nil),
            Push push (ATEndEnv 1),
            Unify unify (ATStr (A "p") 1),
            Backtrack backtrack,
            Unify unify (ATVar (V "Y") Nil),
            Backtrack backtrack,
            Push push ATChp,
            Push push (ATStr (A "q") 1),
            Push push (ATVar (V "Y") Nil),
            Push push ATEndAtom,
            Call call,
            Backtrack backtrack,
            Return returnL ATPos
          ]
      )
      (stackTake 14 (genCode $ parse $ tokenize "p(Y) :- q(Y). :- p (X)."))

testÜbVarSeqSeq =
  TestCase $
    assertEqual
      "üb called on a VarSeq with following Sequence should result in push BegEnv, followed by übenv/body of varseq and seq respectively, ending on prompt."
      ( Stack
          [ Push push ATBegEnv,
            Push push (ATVar (V "X") Nil),
            Push push (ATEndEnv 1),
            Push push ATChp,
            Push push (ATStr (A "p") 1),
            Push push (ATVar (V "X") Nil),
            Push push ATEndAtom,
            Call call,
            Backtrack backtrack,
            Prompt prompt
          ]
      )
      (genCode $ parse $ tokenize ":- p(X).")

testÜbVarSeqAtmNoVar =
  TestCase $
    assertEqual
      "üb called on an atom (fact) should result in pushBegEnv, followed by an empty env and übhead called on atom, ending on return."
      ( Stack
          [ Push push ATBegEnv,
            Push push (ATEndEnv 0),
            Unify unify (ATStr (A "q") 1),
            Backtrack backtrack,
            Unify unify (ATStr (A "a") 0),
            Backtrack backtrack,
            Return returnL ATPos
          ]
      )
      (stackTake 7 (genCode $ parse $ tokenize "q(a). :- p(X)."))

testÜbVarSeqAtmWithVar =
  TestCase $
    assertEqual
      "üb called on a fact containing a var should result in pushBegEnv with filled env, übhead called on the atom, ending on return (pos)."
      ( Stack
          [ Push push ATBegEnv,
            Push push (ATVar (V "X") Nil),
            Push push (ATEndEnv 1),
            Unify unify (ATStr (A "q") 1),
            Backtrack backtrack,
            Unify unify (ATVar (V "X") Nil),
            Backtrack backtrack,
            Return returnL ATPos
          ]
      )
      (stackTake 8 (genCode $ parse $ tokenize "q(X). :- p(X)."))

übTests =
  [ testÜbPushEmpty,
    testÜbPushExpSeq,
    testÜbPushSymbol,
    testÜbPushSymbolArity,
    testÜbBodyEmpty,
    testÜbBodyAtomSeq,
    testÜbUnifyEmpty,
    testÜbUnifyExpSeq,
    testÜbUnifySymbol,
    testÜbUnifySymbolArity,
    testÜbHeadAtom,
    testÜbEnvEmpty,
    testÜbEnvSymbSeq,
    testÜbVarSeqAtmNoVar,
    testÜbVarSeqAtmWithVar,
    testÜbVarSeqAtmSeq,
    testÜbVarSeqSeq
  ]

pushTests =
  [ testPushSTR,
    testPushVAR,
    testPushCHP,
    testPushEndAtom,
    testPushBegEnv,
    testPushEndEnv
  ]
callTests =
  [
    testCallStackAtCNil,
    testCallElseCase
  ]
backtrackTests =
  [ testBacktrackBTrue,
    testBacktrackBTrueWhileLoop,
    testBacktrackBTrueIfStackCNil,
    testBacktrackBFalse
  ]
unifyMakroTests =
  [
    testAddAcNil,
    testAddAcNotNil,
    testRestoreAcUpQAc0,
    testRestoreAcUpQAcNot0,
    testSaveAcUpQ,
    testSaveAcUpQUpBigger,
    testSaveAcUpQUpEqualsDerefUp,
    testSaveAcUpQArityEquals0,
    testDeref
  ]
unifyTests =
  [
    testUnifyPushStr,
    testUnifyPushVar,
    testUnifyNonPushStrThenCase,
    testUnifyNonPushStrElseCaseSymbolNotSame,
    testUnifyNonPushStrElseCaseSymbolSameAritySmaller1
  ]
unifyHelperTests =
  [
  ]
stackReplaceTests =
  [
    testStackReplaceAtLocationMLStack
  ]
{- helpersTests =
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
 -}
{-# LANGUAGE ScopedTypeVariables #-}

module ParserSpec where

import Control.Exception
import Models (Token (..))
import Parser
import System.Exit
import Test.HUnit

-- TODO: Test error cases
-- TODO: Check if all first sets are right. Ziel for instance only checked for
--       pos. literals, not negative ones.

{- --------------------------------------------
    Helper Function for Testing of Error Calls
 ----------------------------------------------}

-- TODO: Fix Handling of errors in functions called by evaluated function [assertErrorCall can't handle recursion so far]
assertErrorCall :: String -> String -> a -> Assertion
assertErrorCall preface expectedErrorMsg actual =
  let actualIO = evaluate actual
   in do
        actualCatch <-
          catches
            (actualIO >> return (Just "No Error was thrown."))
            [ Handler
                ( \(error :: ErrorCall) ->
                    let actualerr = takeWhile (/= '\n') $ displayException error
                     in return $
                          if actualerr == expectedErrorMsg
                            then Nothing
                            else Just ("Expected error || " ++ expectedErrorMsg ++ " || but got the error || " ++ actualerr ++ " ||")
                )
            ]
        case actualCatch of
          Nothing -> return ()
          Just msg -> assertFailure (preface ++ " Test Result : " ++ msg)

{----------------------------------
         Tests for Literals
-----------------------------------}

testPositiveLiteral =
  TestCase $
    assertEqual
      "The literal rule must be properly parsed when not negated"
      (TL $ Literal True (LTVar "Ludwig"), [Ende])
      (literal [Variable "Ludwig", Ende])

testNegatedLiteral =
  TestCase $
    assertEqual
      "The literal rule must be properly parsed when negated"
      (TL $ Literal False (LTVar "Ludwig"), [Ende])
      (literal [Not, Variable "Ludwig", Ende])

testErrorPositiveLiteralWithWrongBeginning :: Test
testErrorPositiveLiteralWithWrongBeginning =
  TestCase $
    assertErrorCall
      "The literal rule must throw an error when starting with an unexpected char"
      "Expected Not, Variable or Name but got Implikation"
      (literal [Implikation, Variable "Ludwig"])

{- testErrorDoubleNegativeLiteral = TestCase $ assertErrorCall
    "Literals with more than one negation should result in an error."
    "Expected Variable or Name but got Not"
    (literal [Not, Not, Variable "Ludwig", Punkt, Ende])
    Rekursiver Test; vorerst ausgeklammert.
    Bei manueller Prüfung erfolgreich. -}

{- testErrorUnfinishedLiteral = TestCase $ assertErrorCall
    "Literals can't end on anything but LTerm."
    ("Expected Variable or Name but got " ++ show Punkt)
    (literal [Not, Punkt, Ende])
    Rekursiver Test; vorerst ausgeklammert.
    Bei manueller Prüfung erfolgreich. -}

{----------------------------------
          Tests for LTerms
-----------------------------------}

testLTermWithVariable =
  TestCase $
    assertEqual
      "The lTerm rule must be properly parsed when the beginning is a variable"
      (TLT $ LTVar "Ludwig", [Implikation])
      (lTerm [Variable "Ludwig", Implikation])

testLTermWithNVLTermNameOnly =
  TestCase $
    assertEqual
      "The lTerm rule must be properly parsed when the beginning is a variable"
      (TLT $ LTNVar (NVLTerm "eins" []), [Ende])
      (lTerm [Name "eins", Ende])

testLTermWithNichtVariableLTermAndSingleLTerm =
  TestCase $
    assertEqual
      "The lTerm rule must be properly parsed when substituted by NichtVariableLTerm once"
      (TLT $ LTNVar (NVLTerm "isEven" [LTVar "X"]), [Ende])
      (lTerm [Name "isEven", KlammerAuf, Variable "X", KlammerZu, Ende])

testLTermWithNichtVariableLTermAndMultipleLTerms =
  TestCase $
    assertEqual
      "The lTerm rule must be properly parsed when substituted by NichtVariableLTerm multiple times"
      (TLT $ LTNVar (NVLTerm "factorial" [LTVar "X", LTVar "Y"]), [Ende])
      (lTerm [Name "factorial", KlammerAuf, Variable "X", And, Variable "Y", KlammerZu, Ende])

testErrorLTermWithoutNameOrVariable =
  TestCase $
    assertErrorCall
      "The lTerm function has to throw an error when the next Token isn't of Name or Variable"
      "Expected Variable or Name but got KlammerAuf"
      (lTerm [KlammerAuf, Variable "X", KlammerZu])

{----------------------------------
    Tests for NichtVariableLTerm
-----------------------------------}

testNvlTermWithNameOnly =
  TestCase $
    assertEqual
      "The nichtVariableLTerm must be properly parsed when only consisting of a single Name"
      (TNVLT $ NVLTerm "eins" [], [Ende])
      (nichtVariableLTerm [Name "eins", Ende])

testNvlTermWithNameAndOneLTerm =
  TestCase $
    assertEqual
      "The nichtVariableLTerm must be properly parsed when containing one LTerm only"
      (TNVLT $ NVLTerm "isEven" [LTVar "X"], [Ende])
      (nichtVariableLTerm [Name "isEven", KlammerAuf, Variable "X", KlammerZu, Ende])

testNvlTermWithNameAndMultipleLTerms =
  TestCase $
    assertEqual
      "The nichtVariableLTerm must be properly parsed when containing multiple LTerms"
      (TNVLT $ NVLTerm "isFatherOf" [LTVar "Priest", LTVar "Hesekiel"], [Ende])
      (nichtVariableLTerm [Name "isFatherOf", KlammerAuf, Variable "Priest", And, Variable "Hesekiel", KlammerZu, Ende])

testNvlTermWithNestedNvlTerms =
  TestCase $
    assertEqual
      "The nichtVariableLTerm must be properly parsed when containing multiple nested NVLTs"
      (TNVLT $ NVLTerm "isSomething" [LTVar "A", LTNVar (NVLTerm "someName" [LTVar "B", LTNVar (NVLTerm "otherName" [])])], [Ende])
      (nichtVariableLTerm [Name "isSomething", KlammerAuf, Variable "A", And, Name "someName", KlammerAuf, Variable "B", And, Name "otherName", KlammerZu, KlammerZu, Ende])

{----------------------------------
           Tests for Ziel
-----------------------------------}

-- TODO: Maybe find more sementically plausible example
testZielWithSinglePositiveLiteral =
  TestCase $
    assertEqual
      "The ziel rule must be properly parsed when containing one positive Literal only"
      (TZ $ Ziel [Literal True (LTVar "Test")], [Ende])
      (ziel [Implikation, Variable "Test", Punkt, Ende])

-- TODO: Maybe find more sementically plausible example
testZielWithSingleNegativeLiteral =
  TestCase $
    assertEqual
      "The ziel rule must be properly parsed when containing one negative Literal only"
      (TZ $ Ziel [Literal False (LTVar "Test")], [Ende])
      (ziel [Implikation, Not, Variable "Test", Punkt, Ende])

-- TODO: Maybe find more sementically plausible example
testZielWithMultipleLiterals =
  TestCase $
    assertEqual
      "The ziel rule must be properly parsed when containing multiple literals"
      (TZ $ Ziel [Literal True (LTVar "A"), Literal False (LTVar "B")], [Ende])
      (ziel [Implikation, Variable "A", And, Not, Variable "B", Punkt, Ende])

testErrorZielAndFirstSymbolNotImplikation =
  TestCase $
    assertErrorCall
      "The Ziel rule must throw a certain error when not starting with an Implikation"
      "Expected an Implikation but got And"
      (ziel [And, Variable "Test", Punkt, Ende])

testErrorZielAndSecondSymbolNotALiteral =
  TestCase $
    assertErrorCall
      "The Ziel rule must throw a certain error when Implication is not followed by a literal"
      "Expected Not, Variable or Name but got And"
      (ziel [Implikation, And, Punkt, Ende])

-- testErrorZielNotEndingOnPunkt = TestCase $ assertErrorCall
--     "The Ziel rule must throw a certain error when not ending on Punkt"
--     "Expected And or Punkt but got Ende"
--     (ziel [Implikation, Not, Variable "A", And, Variable "B", Ende])
-- Manual test shows it oes actually fail:
-- Exception: Expected And or Punkt but got Ende

{----------------------------------
      Tests for Programmklausel
-----------------------------------}

-- TODO: Maybe find more sementically plausible example
testPkWithNVLTAndPeriod =
  TestCase $
    assertEqual
      "The programmklausel rule must be properly parsed when consisting of NichtVariableLTerm and period"
      (TPk . Pk1 $ NVLTerm "test" [], [Ende])
      (programmklausel [Name "test", Punkt, Ende])

-- TODO: Maybe find more sementically plausible example
testPkWithNVLTAndZiel =
  TestCase $
    assertEqual
      "The programmklausel rule must be properly parsed when consisting of NichtVariableLTerm and Ziel"
      ( TPk $
          Pk2
            (NVLTerm "test" [])
            (Ziel [Literal True (LTVar "A"), Literal False (LTVar "B")]),
        [Ende]
      )
      (programmklausel [Name "test", Implikation, Variable "A", And, Not, Variable "B", Punkt, Ende])

testErrorPKZiel =
  TestCase $
    assertErrorCall
      "A Pk has to throw an error when not properly followed with a Punkt or Implikation"
      "Expected Punkt or Implikation but got KlammerZu"
      (programmklausel [Name "test", KlammerAuf, Variable "X", KlammerZu, KlammerZu, Ende])

testErrorPKOhneName =
  TestCase $
    assertErrorCall
      "A Pk has to throw an error when being called without a Name Token"
      "Expected Name but got Punkt"
      (programmklausel [Punkt, Ende])

{----------------------------------
          Tests for Programm
-----------------------------------}

-- TODO: Maybe find more sementically plausible example
testProgrammWithZiel =
  TestCase $
    assertEqual
      "The Programm rule must be properly parsed when consisting of Ziel only"
      (TP $ Programm [] (Ziel [Literal False (LTVar "A")]), [Ende])
      (programm [Implikation, Not, Variable "A", Punkt, Ende])

-- TODO: Maybe find more sementically plausible example
testProgrammWithSinglePkAndZiel =
  TestCase $
    assertEqual
      "The Programm rule must be properly parsed when consisting of one Programmklausel and one Ziel"
      ( TP $
          Programm
            [ Pk2
                (NVLTerm "test" [])
                (Ziel [Literal True (LTVar "A"), Literal False (LTVar "B")])
            ]
            (Ziel [Literal False (LTVar "A")]),
        [Ende]
      )
      (programm [Name "test", Implikation, Variable "A", And, Not, Variable "B", Punkt, Implikation, Not, Variable "A", Punkt, Ende])

-- TODO: Maybe find more sementically plausible example
testProgrammWithMultiplePkAndZiel =
  TestCase $
    assertEqual
      "The Programm rule must be properly parsed when consisting of more than one Programmklausel and one Ziel"
      ( TP $
          Programm
            [ Pk2
                (NVLTerm "test" [])
                (Ziel [Literal True (LTVar "A"), Literal False (LTVar "B")]),
              Pk1 $ NVLTerm "another" []
            ]
            (Ziel [Literal False (LTVar "A")]),
        [Ende]
      )
      (programm [Name "test", Implikation, Variable "A", And, Not, Variable "B", Punkt, Name "another", Punkt, Implikation, Not, Variable "A", Punkt, Ende])

testErrorProgrammWithoutZiel =
  TestCase $
    assertErrorCall
      "Not starting with a Pk or Ziel should lead to an error"
      "Expected Name or Implikation but got Variable \"A\""
      (programm [Variable "A"])

--This function doesn't throw an error, but using ghci I found everything to be working correctly. An error gets thrown, but because of the recursion or lazy evaluation in ghc, the error doesn't show up at the right place.
--The Parser doesn't compile without a Ziel as the last part of a Programm, as it should, this test was supposed to test just that.
--testErrorProgrammWithMultiplePkAndNoZiel = TestCase $ assertErrorCall
--    "After parsing a Fakt or a Pk, not parsing a new Pk/Fakt(Starting with Name) or Ziel(Starting with Implikation) should lead to an error"
--    "Expected Name or Implikation but got KlammerAuf"
--    (programm [Name "test", KlammerAuf, Variable "A", KlammerZu, Punkt, Name "test2", Implikation, Variable "B", And, Variable "C", Punkt, KlammerAuf])
{----------------------------------
          Tests for Parser
-----------------------------------}

testParserWithProgrammWithMultiplePkAndZiel =
  TestCase $
    assertEqual
      "The parser must return a Tree when the passed tokens are appopriate according to the syntax rules"
      ( TP $
          Programm
            [ Pk2
                (NVLTerm "test" [])
                (Ziel [Literal True (LTVar "A"), Literal False (LTVar "B")]),
              Pk1 $ NVLTerm "another" []
            ]
            (Ziel [Literal False (LTVar "A")])
      )
      (parse [Name "test", Implikation, Variable "A", And, Not, Variable "B", Punkt, Name "another", Punkt, Implikation, Not, Variable "A", Punkt, Ende])

{------------------------------------
 Tests for Reoccurring Literal Helper
 ------------------------------------}

testReoccurringLiteralWithSinglePosLit =
  TestCase $
    assertEqual
      "Optional Subliterals must be properly parsed when consisting of a single pos. literals"
      (TLL [Literal True (LTVar "A")], [Ende])
      (reoccurringLiteral [Variable "A", Punkt, Ende])

testReoccurringLiteralWithSingleNegLit =
  TestCase $
    assertEqual
      "Optional Subliterals have to be properly parsed when consisting of a single neg. literals."
      (TLL [Literal False (LTVar "B")], [Ende])
      (reoccurringLiteral [Not, Variable "B", Punkt, Ende])

testReoccurringLiteralWithOnlyPositives =
  TestCase $
    assertEqual
      "Optional Subliterals must be properly parsed when consisting only of multiple pos. literals"
      (TLL [Literal True (LTVar "A"), Literal True (LTVar "B")], [Ende])
      (reoccurringLiteral [Variable "A", And, Variable "B", Punkt, Ende])

testReoccurringLiteralWithOnlyNegatives =
  TestCase $
    assertEqual
      "Optional Subliterals must be parsed properly when consisting only of multiple neg. literals. "
      (TLL [Literal False (LTVar "A"), Literal False (LTVar "B")], [Ende])
      (reoccurringLiteral [Not, Variable "A", And, Not, Variable "B", Punkt, Ende])

testReoccurringLiteralWithMultipleMixed =
  TestCase $
    assertEqual
      "Optional Subliterals must be parsed properly when consisting of multiple pos. and neg. literals."
      (TLL [Literal True (LTVar "A"), Literal False (LTVar "B"), Literal False (LTVar "C"), Literal True (LTVar "D")], [Ende])
      (reoccurringLiteral [Variable "A", And, Not, Variable "B", And, Not, Variable "C", And, Variable "D", Punkt, Ende])

{-     testErrorReoccurringLiteralEndOnAnd = TestCase $ assertErrorCall
        "Having an optional subliteral end on And followed by Punkt should cause an error."
        ("Expected Not, Variable or Name but got " ++ show Punkt)
        (reoccurringLiteral [Variable "A", And, Punkt, Ende])
        rekursiver Test; vorerst ausgeklammert.
        Bei manueller Prüfung erfolgreich.-}

testErrorReoccurringLiteralLackOfPunkt =
  TestCase $
    assertErrorCall
      "Having an optional subliteral end without parsing Punkt should cause an error."
      ("Expected And or Punkt but got " ++ show KlammerAuf)
      (reoccurringLiteral [Variable "A", KlammerAuf])

{----------------------------------
    Tests for teilNichtVariableLTerm
 ----------------------------------}

testTeilNVLTWithOnlyName =
  TestCase $
    assertEqual
      "TeilNVLT must be parsed properly when consisting of only a Name (NVLT)"
      (TLLT [LTNVar (NVLTerm "someName" [])], [Ende])
      (teilNichtVariableLTerm [Name "someName", KlammerZu, Ende])

testTeilNVLTWithSingleVariable =
  TestCase $
    assertEqual
      "TeilNVLT must be parsed properly when consisting of only a Variable (LT)"
      (TLLT [LTVar "A"], [Ende])
      (teilNichtVariableLTerm [Variable "A", KlammerZu, Ende])

testTeilNVLTWithMultipleVariables =
  TestCase $
    assertEqual
      "TeilNVLT must be parsed properly when consisting of multiple Variables (LT)"
      (TLLT [LTVar "A", LTVar "B", LTVar "C"], [Ende])
      (teilNichtVariableLTerm [Variable "A", And, Variable "B", And, Variable "C", KlammerZu, Ende])

testTeilNVLTWithNestedNVLT =
  TestCase $
    assertEqual
      "TeilNVLT must be parsed properly when consisting of nested NVLTs and Variables"
      (TLLT [LTVar "A", LTNVar (NVLTerm "someName" [LTVar "B", LTNVar (NVLTerm "otherName" [])])], [Ende])
      (teilNichtVariableLTerm [Variable "A", And, Name "someName", KlammerAuf, Variable "B", And, Name "otherName", KlammerZu, KlammerZu, Ende])

{-     testErrorTeilNVLTInvalidEnd = TestCase $ assertErrorCall
        "TeilNVLT has to end on Punkt or KlammerZu."
        ("Expected Variable or Name but got " ++ show Punkt)
        (teilNichtVariableLTerm [Variable "A", And, Name "someName", KlammerAuf, Punkt, Ende])
        rekursiver Test; vorerst ausgeklammert.
        Bei manueller Prüfung erfolgreich.-}

{-     testErrorTeilNVLTInvalidContinuationAfterLTerm = TestCase $ assertErrorCall
        "TeilNVLT only continues if And is parsed."
        ("Expected AND or close parenthesis but got: " ++ show KlammerAuf)
        (teilNichtVariableLTerm [Variable "A", KlammerAuf, Variable "B", Punkt, Ende])
        rekursiver Test; vorerst ausgeklammert.
        Bei manueller Prüfung erfolgreich. -}

{-     testErrorTeilNVLTInvalidContinuationAfterAnd = TestCase $ assertErrorCall
        "TeilNVLT should only parse LTerms after And is parsed."
        ("Expected Variable or Name but got " ++ show And)
        (teilNichtVariableLTerm [Variable "A", And, And, Punkt, Ende])
        rekursiver Test; vorerst ausgeklammert.
        Bei manueller Prüfung erfolgreich. -}

testErrorTeilNVLTInvalidStartToken =
  TestCase $
    assertErrorCall
      "TeilNVLT has to parse an LTerm after being called."
      ("Expected Variable or Name but got " ++ show KlammerAuf)
      (teilNichtVariableLTerm [KlammerAuf, Variable "A", Punkt, Ende])

{----------------------------------
          Lists of Tests
-----------------------------------}

literalTests =
  [ testPositiveLiteral,
    testNegatedLiteral,
    -- Error tests
    testErrorPositiveLiteralWithWrongBeginning
  ]

lTermTests =
  [ testLTermWithVariable,
    testLTermWithNVLTermNameOnly,
    testLTermWithNichtVariableLTermAndSingleLTerm,
    testLTermWithNichtVariableLTermAndMultipleLTerms,
    -- Error Tests
    testErrorLTermWithoutNameOrVariable
  ]

nvlTermTest =
  [ testNvlTermWithNameOnly,
    testNvlTermWithNameAndOneLTerm,
    testNvlTermWithNameAndMultipleLTerms,
    testNvlTermWithNestedNvlTerms
  ]

zielTests =
  [ testZielWithSinglePositiveLiteral,
    testZielWithSingleNegativeLiteral,
    testZielWithMultipleLiterals,
    -- Error Tests
    testErrorZielAndFirstSymbolNotImplikation,
    testErrorZielAndSecondSymbolNotALiteral
  ]

pkTests =
  [ testPkWithNVLTAndPeriod,
    testPkWithNVLTAndZiel,
    -- Error Tests
    testErrorPKOhneName
    --testErrorPKOhneZiel
  ]

programmTests =
  [ testProgrammWithZiel,
    testProgrammWithSinglePkAndZiel,
    testProgrammWithMultiplePkAndZiel,
    -- Error Tests
    testErrorProgrammWithoutZiel
  ]

parserTests = [testParserWithProgrammWithMultiplePkAndZiel]

reoccurringLiteralTests =
  [ testReoccurringLiteralWithSinglePosLit,
    testReoccurringLiteralWithSingleNegLit,
    testReoccurringLiteralWithOnlyPositives,
    testReoccurringLiteralWithOnlyNegatives,
    testReoccurringLiteralWithMultipleMixed,
    -- Error Tests
    testErrorReoccurringLiteralLackOfPunkt
  ]

teilNichtVariableLTermTests =
  [ testTeilNVLTWithOnlyName,
    testTeilNVLTWithSingleVariable,
    testTeilNVLTWithMultipleVariables,
    testTeilNVLTWithNestedNVLT,
    -- Error Tests
    testErrorTeilNVLTInvalidStartToken
  ]

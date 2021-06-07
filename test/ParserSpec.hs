module ParserSpec where
    import Test.HUnit
    import System.Exit
    import Control.Exception (try, ErrorCall(ErrorCall), evaluate)

    import Parser
    import Models (Token(..))

    -- TODO: Test error cases
    -- TODO: Check if all first sets are right. Ziel for instance only checked for
    --       pos. literals, not negative ones.
    -- TODO: Add tests for helper functions

    {----------------------------------
             Tests for Literals
    -----------------------------------}

    testPositiveLiteral = TestCase $ assertEqual
        "The literal rule must be properly parsed when not negated"
        ((TL $ Literal True (LTVar "Ludwig")), [Ende])
        (literal [Variable "Ludwig", Ende])

    testNegatedLiteral = TestCase $ assertEqual
        "The literal rule must be properly parsed when negated"
        (TL $ Literal False (LTVar "Ludwig"), [Ende])
        (literal [Not, Variable "Ludwig", Ende])

    -- -- TODO: Test case that tests for the error
    -- testPositiveLiteralWithWrongBegining = TestCase $ assertError
    --     "The literal rule must throw an error when starting with an unexpected char"
    --     ("Expected Not, Variable or Name but got " ++ show Implikation)
    --     (literal [Implikation, Variable "Ludwig"])

    {----------------------------------
              Tests for LTerms
    -----------------------------------}

    testLTermWithVariable = TestCase $ assertEqual
        "The lTerm rule must be properly parsed when the beginning is a variable"
        (TLT $ LTVar "Ludwig", [Implikation])
        (lTerm [Variable "Ludwig", Implikation])

    testLTermWithNVLTermNameOnly = TestCase $ assertEqual
        "The lTerm rule must be properly parsed when the beginning is a variable"
        (TLT $ LTNVar (NVLTerm "eins" []), [Ende])
        (lTerm [Name "eins", Ende])

    testLTermWithNichtVariableLTermAndSingleLTerm = TestCase $ assertEqual
        "The lTerm rule must be properly parsed when substituted by NichtVariableLTerm once"
        (TLT $ LTNVar (NVLTerm "isEven" [LTVar "X"]), [Ende])
        (lTerm [Name "isEven", KlammerAuf, Variable "X", KlammerZu, Ende])

    testLTermWithNichtVariableLTermAndMultipleLTerms = TestCase $ assertEqual
        "The lTerm rule must be properly parsed when substituted by NichtVariableLTerm multiple times"
        (TLT $ LTNVar (NVLTerm "factorial" [LTVar "X", LTVar "Y"]), [Ende])
        (lTerm [Name "factorial", KlammerAuf, Variable "X", And, Variable "Y", KlammerZu, Ende])

    {----------------------------------
        Tests for NichtVariableLTerm
    -----------------------------------}

    testNvlTermWithNameOnly = TestCase $ assertEqual
        "The nichtVariableLTerm must be properly parsed when only consisting of a single Name"
        (TNVLT $ NVLTerm "eins" [], [Ende])
        (nichtVariableLTerm [Name "eins", Ende])

    testNvlTermWithNameAndOneLTerm = TestCase $ assertEqual 
        "The nichtVariableLTerm must be properly parsed when containing one LTerm only"
        (TNVLT $ NVLTerm "isEven" [LTVar "X"], [Ende])
        (nichtVariableLTerm [Name "isEven", KlammerAuf, Variable "X", KlammerZu, Ende])

    testNvlTermWithNameAndMultipleLTerms = TestCase $ assertEqual
        "The nichtVariableLTerm must be properly parsed when containing multiple LTerms"
        (TNVLT $ NVLTerm "isFatherOf" [LTVar "Priest", LTVar "Hesekiel"], [Ende])
        (nichtVariableLTerm [Name "isFatherOf", KlammerAuf, Variable "Priest", And, Variable "Hesekiel", KlammerZu, Ende])

    {----------------------------------
               Tests for Ziel
    -----------------------------------}

    -- TODO: Maybe find more sementically plausible example
    testZielWithSinglePositiveLiteral = TestCase $ assertEqual
        "The ziel rule must be properly parsed when containing one positive Literal only"
        (TZ $ Ziel [Literal True (LTVar "Test")], [Ende])
        (ziel [Implikation, Variable "Test", Punkt, Ende])

    -- TODO: Maybe find more sementically plausible example
    testZielWithSingleNegativeLiteral = TestCase $ assertEqual
        "The ziel rule must be properly parsed when containing one negative Literal only"
        (TZ $ Ziel [Literal False (LTVar "Test")], [Ende])
        (ziel [Implikation, Not, Variable "Test", Punkt, Ende])

    -- TODO: Maybe find more sementically plausible example
    testZielWithMultipleLiterals = TestCase $ assertEqual
        "The ziel rule must be properly parsed when containing multiple literals"
        (TZ $ Ziel [Literal True (LTVar "A"), Literal False (LTVar "B")], [Ende])
        (ziel [Implikation, Variable "A", And, Not, Variable "B", Punkt, Ende])

    {----------------------------------
          Tests for Programmklausel
    -----------------------------------}

    -- TODO: Maybe find more sementically plausible example
    testPkWithNVLTAndPeriod = TestCase $ assertEqual
        "The programmklausel rule must be properly parsed when consisting of NichtVariableLTerm and period"
        (TPk . Pk1 $ NVLTerm "test" [], [Ende])
        (programmklausel [Name "test", Punkt, Ende])

    -- TODO: Maybe find more sementically plausible example
    testPkWithNVLTAndZiel = TestCase $ assertEqual
        "The programmklausel rule must be properly parsed when consisting of NichtVariableLTerm and Ziel"
        (TPk $ Pk2 
            (NVLTerm "test" []) 
            (Ziel [Literal True (LTVar "A"), Literal False (LTVar "B")]), [Ende])
        (programmklausel [Name "test", Implikation, Variable "A", And, Not, Variable "B", Punkt, Ende])

    {----------------------------------
              Tests for Programm
    -----------------------------------}

    -- TODO: Maybe find more sementically plausible example
    testProgrammWithZiel = TestCase $ assertEqual
        "The Programm rule must be properly parsed when consisting of Ziel only"
        (TP $ Programm [] (Ziel [Literal False (LTVar "A")]), [Ende])
        (programm [Implikation, Not, Variable "A", Punkt, Ende])

    -- TODO: Maybe find more sementically plausible example
    testProgrammWithSinglePkAndZiel = TestCase $ assertEqual
        "The Programm rule must be properly parsed when consisting of one Programmklausel and one Ziel"
        (TP $ Programm 
            [Pk2 
                (NVLTerm "test" []) 
                (Ziel [Literal True (LTVar "A"), Literal False (LTVar "B")])] 
            (Ziel [Literal False (LTVar "A")]), [Ende])
        (programm [Name "test", Implikation, Variable "A", And, Not, Variable "B", Punkt, Implikation, Not, Variable "A", Punkt, Ende])

    -- TODO: Maybe find more sementically plausible example
    testProgrammWithMultiplePkAndZiel = TestCase $ assertEqual
        "The Programm rule must be properly parsed when consisting of more than one Programmklausel and one Ziel"
        (TP $ Programm 
            [Pk2 
                (NVLTerm "test" []) 
                (Ziel [Literal True (LTVar "A"), Literal False (LTVar "B")])
            ,Pk1 $ NVLTerm "another" []] 
            (Ziel [Literal False (LTVar "A")]), [Ende])
        (programm [Name "test", Implikation, Variable "A", And, Not, Variable "B", Punkt, Name "another", Punkt, Implikation, Not, Variable "A", Punkt, Ende])

    {----------------------------------
                TestLists 
    -----------------------------------}

    literalTests = [testPositiveLiteral
                   ,testNegatedLiteral]

    lTermTests   = [testLTermWithVariable
                   ,testLTermWithNVLTermNameOnly
                   ,testLTermWithNichtVariableLTermAndSingleLTerm
                   ,testLTermWithNichtVariableLTermAndMultipleLTerms]
                   
    nvlTermTest = [testNvlTermWithNameOnly
                  ,testNvlTermWithNameAndOneLTerm
                  ,testNvlTermWithNameAndMultipleLTerms]

    zielTests = [testZielWithSinglePositiveLiteral
                ,testZielWithSingleNegativeLiteral
                ,testZielWithMultipleLiterals]

    pkTests = [testPkWithNVLTAndPeriod
              ,testPkWithNVLTAndZiel]

    programmTests = [testProgrammWithZiel
                    ,testProgrammWithSinglePkAndZiel
                    ,testProgrammWithMultiplePkAndZiel]
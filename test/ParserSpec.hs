module ParserSpec where
    import Parser
    import Test.HUnit
    import System.Exit

    testTwoTimesTwoIs4 = TestCase (assertEqual "Two times two is 4" 4 (2 * 2))
import ParserSpec
import StackSpec
import System.Exit
import Test.HUnit

main :: IO ()
main = do
  results <-
    runTestTT . TestList . concat $
      [literalTests, lTermTests, nvlTermTest, zielTests, pkTests, programmTests, reoccurringLiteralTests, teilNichtVariableLTermTests, parserTests, stackTests]

  if errors results + failures results == 0
    then putStrLn "Tests passed."
    else die "Tests failed."
import ParserSpec

import Test.HUnit
import System.Exit


main :: IO ()
main = do
    results <- runTestTT . TestList $
        literalTests ++ lTermTests ++ nvlTermTest ++ zielTests ++ pkTests ++ programmTests
    if errors results + failures results == 0 then
        putStrLn "Tests passed."
    else
        die "Tests failed."
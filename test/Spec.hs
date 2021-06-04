import ParserSpec (testTwoTimesTwoIs4)

import Test.HUnit
import System.Exit


main :: IO ()
main = do
    results <- runTestTT . test $ [testTwoTimesTwoIs4]
    if errors results + failures results == 0 then
        putStrLn "Tests passed."
    else
        die "Tests failed."
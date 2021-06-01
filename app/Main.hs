module Main where

import Tokenizer

main :: IO ()
main = do
    let result = tokenizer "BaCdE:-...;" []
    print "Test"
    print . show $ result
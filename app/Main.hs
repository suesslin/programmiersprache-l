module Main where

import Tokenizer (tokenizer)
import Parser

main :: IO ()
main = do
    let result = tokenizer "BaCdE:-...;" []
    print "Test"
    print . show $ result
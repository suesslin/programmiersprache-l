module Main where

import Parser
import Tokenizer (tokenize)

main :: IO ()
main = do
  let result = tokenize "BaCdE:-...;"
  print "Test"
  print . show $ result
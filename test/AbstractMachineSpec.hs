module AbstractMachineSpec where

import AbstractMachine
import Models
import Parser
import Test.HUnit
import Tokenizer

{- {- testUebersetzungBodySingleLiteral = TestCase $ assertEqual
    "."
    (["push q","call","backtrackQ"])
    (uebersetzungBody [Literal True (LTNVar (NVLTerm "q" []))] [])  -}

testUebersetzungMiniLOnlyZielSingleLit = TestCase $assertEqual
    "Translation Function should generate correct code from programs only consisting of ziel with single literal."
    ([push "a",call,backtrackQ])
    (uebersetzungMiniL (TP (Programm [] (Ziel [Literal True (LTNVar (NVLTerm "a" []))]))) [])
TODO -}
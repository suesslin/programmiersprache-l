module Main where

import AbstractMachine (codeGen)
import Parser
import Tokenizer (tokenize)

main :: IO ()
main = do
  -- Introduction to the project at each run
  putStrLn $
    "**************************************************\n"
      <> "Projekt: Programmiersprache L\n"
      <> "\nEntwicklungsteam (Gruppe 3):\n"
      <> "  • D'Amelio Marco\n"
      <> "  • Seilmaier Maximilian\n"
      <> "  • Süsslin Lukas\n"
      <> "\nEntwicklungszweck:\n"
      <> "  Implementierung von Programmiersprachen\n"
      <> "  ein Entwicklungspraktikum im Rahmen des Informatik-Bachelors\n"
      <> "  an der Ludwig-Maximilians-Universität München\n"
      <> "  im Sommersemester 2021\n"
      <> "\nBetreuer der Gruppen der Sprache L: "
      <> "Deckarm Oliver und Prokosch Thomas"
      <> "\n"
      <> "**************************************************\n\n"
  -- Actual interactive program

  putStrLn $
    "Es soll ein L-Programm gelesen werden.\n"
      <> "Dazu bitte nun den absoluten Pfad zu einem L-Programm eingeben.\n"

  sourceCode <- readFile =<< getLine

  putStrLn $
    "\nWas soll im Folgenden ausgeben werden?\n"
      <> "  (1) Tokenliste\n"
      <> "  (2) Geparstes Programm\n"
      <> "  (3) Übersetztes Programm nach ML\n"
      <> "\nBitte die passende Zahl eingeben\n"

  outputType <- (\x -> (pure . intToOutput $ read x :: IO OutputType)) =<< getLine

  putStrLn $
    "\nDie Ausgabe für das gegebene Programm als "
      ++ show outputType
      ++ " sieht wiefolgt aus:\n"

  case outputType of
    Tokens -> print $ tokenize sourceCode
    ParsedProgram -> print . parse $ tokenize sourceCode
    TranslatedProgram -> print . codeGen . parse $ tokenize sourceCode
    UnknownOutput -> error "Fehler: nicht aufgeführter Ausgabetyp eingefordert. "

data OutputType = Tokens | ParsedProgram | TranslatedProgram | UnknownOutput
  deriving (Show)

intToOutput :: Int -> OutputType
intToOutput n = case n of
  1 -> Tokens
  2 -> ParsedProgram
  3 -> TranslatedProgram
  _ -> UnknownOutput
{- |
Module      :  Civilisation
Description :  
Copyright   :  (c) Dimitri Lozeve
License     :  BSD3

Maintainer  :  Dimitri Lozeve <dimitri.lozeve@gmail.com>
Stability   :  unstable
Portability :  portable

-}

module Civilisation where

import Data.Maybe

import Sat


-- | Main entry point of the program.
main :: IO ()
main = do
  text <- readFile "test.cnf"
  let f = parseDIMACS text in
    case solveDPLL (f, []) of
      UNSAT -> putStrLn "UNSAT"
      SAT a -> putStrLn $ "SAT " ++ show a

-- | Parses a formula in the DIMACS CNF format.
parseDIMACS :: String -> CNF
parseDIMACS = mapMaybe parseClause . lines

-- | Parses a clause (a single line in the DIMACS file).
parseClause :: String -> Maybe Clause
parseClause "" = Nothing
parseClause ('c':_) = Nothing
parseClause ('p':_) = Nothing
parseClause ('%':_) = Nothing
parseClause ('0':_) = Nothing
parseClause s = (Just . map (litFromInt . read) . init . words) s

-- | Interprets an Int, such as -5, as a @Lit@, such as @Neg 5@.
litFromInt :: Int -> Lit
litFromInt n | n < 0 = Neg (-n)
             | otherwise = Pos n

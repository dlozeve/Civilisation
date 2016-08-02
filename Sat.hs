{- |
Module      :  Sat
Description :  Simple SAT solver
Copyright   :  (c) Dimitri Lozeve
License     :  BSD3

Maintainer  :  Dimitri Lozeve <dimitri.lozeve@gmail.com>
Stability   :  unstable
Portability :  portable

A simple SAT solver.
-}

module Sat where

import Data.List

-- Variables are represented by positive integers
type Var = Int

-- A literal is either a variable, or the negation of a variable
data Lit = Pos Var | Neg Var deriving (Eq, Show)

-- A clause is a disjunction of literals, represented by a list of
-- literals
type Clause = [Lit]

-- A formula, represented in its Conjunctive Normal Form (CNF), is a
-- conjunction of clauses, represented as a list
type CNF = [Clause]

-- An assignment is a list of literals. For instance, if an assignment
-- contains (Pos 5), it means that in this assignment, the variable 5
-- is assigned to True.
type Assignment = [Lit]

----------------------------------------------------------------------

-- General-purpose functions

-- Extracts a variable from a literal
fromLit :: Lit -> Var
fromLit (Pos x) = x
fromLit (Neg x) = x

-- Tests for positive/negative literals
isPos :: Lit -> Bool
isPos (Pos _) = True
isPos (Neg _) = False

isNeg :: Lit -> Bool
isNeg = not . isPos

----------------------------------------------------------------------

-- Literal Evaluation

-- Negates a literal
notLit :: Lit -> Lit
notLit (Pos x) = Neg x
notLit (Neg x) = Pos x

-- Evaluates a CNF by fixing the value of a given literal
evalLit :: Lit -> CNF -> CNF
evalLit _ [] = []
evalLit lit f = foldr g [] f
  where g c acc
          | lit `elem` c = acc
          | notLit lit `elem` c = (c \\ [notLit lit]):acc
          | otherwise = c:acc

-- Pure Literal rule

-- Tests whether a literal is pure, i.e. only appears as positive or
-- negative
testPureLit :: Lit -> CNF -> Bool
testPureLit _ [] = True
testPureLit (Pos x) (c:cs) = Neg x `notElem` c && testPureLit (Pos x) cs
testPureLit (Neg x) (c:cs) = Pos x `notElem` c && testPureLit (Neg x) cs

-- Tests whether a variable appears only as a pure literal
testPureVar :: Var -> CNF -> Bool
testPureVar x f = testPureLit (Pos x) f || testPureLit (Neg x) f



----------------------------------------------------------------------

-- Examples for testing purposes

test1 :: CNF
test1 = [[Neg 1, Pos 2], [Pos 3, Neg 2], [Pos 4, Neg 5], [Pos 5, Neg 4]]

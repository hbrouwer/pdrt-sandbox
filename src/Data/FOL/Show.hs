{- |
Module      :  Data.FOL.Show
Copyright   :  (c) Harm Brouwer and Noortje Venhuizen
License     :  Apache-2.0

Maintainer  :  me@hbrouwer.eu, n.j.venhuizen@rug.nl
Stability   :  provisional
Portability :  portable

FOL pretty printing
-}

module Data.FOL.Show
(
-- * FOL pretty printing
  showFOLForm
, printFOLForm
) where

import Data.FOL.Formula
import Data.List (intercalate)

-- | Existential quantifier symbol
opExists = "\x2203"
-- | Universal quantifier symbol
opForAll = "\x2200"
-- | Conjunction symbol
opAnd    = "\x2227"
-- | Disjunction symbol
opOr     = "\x2228"
-- | Implication symbol
opImp    = "\x2192"
-- | Negation symbol
opNeg    = "\x00AC"
-- | Top/true constant symbol
opTop    = "\x22A4"
-- | Bottom/false constant symbol
opBottom = "\x22A5"

-- | Derive an instance of the Show type class for FOLForm
instance Show FOLForm where
  show = showFOLForm

-- | Shows a FOL formula
showFOLForm :: FOLForm -> String
showFOLForm f = '\n' : showFormula f ++ "\n"
  where showFormula :: FOLForm -> String
        showFormula (Exists v f) = opExists ++ v ++ showFormula f
        showFormula (ForAll v f) = opForAll ++ v ++ showFormula f
        showFormula (And f1 f2)  = "(" ++ showFormula f1 ++ " "  ++ opAnd ++ " " ++ showFormula f2 ++ ")"
        showFormula (Or f1 f2)   = "(" ++ showFormula f1 ++ ") " ++ opOr  ++ " (" ++ showFormula f2 ++ ")"
        showFormula (Imp f1 f2)  = "(" ++ showFormula f1 ++ ") " ++ opImp ++ " (" ++ showFormula f2 ++ ")"
        showFormula (Neg f)      = opNeg ++ showFormula f
        showFormula (Rel r d)    = r ++ "(" ++ intercalate "," d ++ ")"
        showFormula (Top)        = opTop
        showFormula (Bottom)     = opBottom

-- | Prints a FOL formula
printFOLForm :: FOLForm -> IO ()
printFOLForm f = putStrLn $ '\n' : showFOLForm f

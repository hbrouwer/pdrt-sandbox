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

---------------------------------------------------------------------------
-- * Exported
---------------------------------------------------------------------------

---------------------------------------------------------------------------
-- | Derive an instance of the Show typeclass for 'FOLForm'.
---------------------------------------------------------------------------
instance Show FOLForm where
  show = showFOLForm

---------------------------------------------------------------------------
-- | Shows a 'FOLForm'.
---------------------------------------------------------------------------
showFOLForm :: FOLForm -> String
showFOLForm f = '\n' : showFormula f ++ "\n"
  where showFormula :: FOLForm -> String
        showFormula (Exists v f) = opExists ++ v ++ showFormula f
        showFormula (ForAll v f) = opForAll ++ v ++ showFormula f
        showFormula (And f1 f2)  = "(" ++ showFormula f1 ++ " "  ++ opAnd ++ " "  ++ showFormula f2 ++ ")"
        showFormula (Or f1 f2)   = "(" ++ showFormula f1 ++ ") " ++ opOr  ++ " (" ++ showFormula f2 ++ ")"
        showFormula (Imp f1 f2)  = "(" ++ showFormula f1 ++ ") " ++ opImp ++ " (" ++ showFormula f2 ++ ")"
        showFormula (Neg f)      = opNeg ++ showFormula f
        showFormula (Rel r d)    = r ++ "(" ++ intercalate "," d ++ ")"
        showFormula (Top)        = opTop
        showFormula (Bottom)     = opBottom

---------------------------------------------------------------------------
-- | Prints a 'FOLForm'.
---------------------------------------------------------------------------
printFOLForm :: FOLForm -> IO ()
printFOLForm f = putStrLn $ '\n' : showFOLForm f

---------------------------------------------------------------------------
-- * Private
---------------------------------------------------------------------------

-- | Existential quantifier symbol
opExists :: String 
opExists = "\x2203" 

-- | Universal quantifier symbol
opForAll :: String
opForAll = "\x2200"

-- | Conjunction symbol
opAnd :: String
opAnd    = "\x2227" 

-- | Disjunction symbol
opOr :: String
opOr     = "\x2228" 

-- | Implication symbol
opImp :: String
opImp    = "\x2192" 

-- | Negation symbol
opNeg :: String
opNeg    = "\x00AC" 

-- | Top/true constant symbol
opTop:: String
opTop    = "\x22A4" 

-- | Bottom/false constant symbol
opBottom :: String
opBottom = "\x22A5"

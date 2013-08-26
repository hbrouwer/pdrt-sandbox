-- Show.hs

{- |
  Show FOL
-}
module Data.FOL.Show
( 
  showFOLForm
, printFOLForm
) where

import Data.FOL.Formula
import Data.List (intercalate)

-- | Operator constants
opExists = "\x2203" -- Existential quantifier symbol
opForAll = "\x2200" -- Universal quantifier symbol
opAnd    = "\x2227" -- Conjunction symbol
opOr     = "\x2228" -- Disjunction symbol
opImp    = "\x2192" -- Implication symbol
opNeg    = "\x00AC" -- Negation symbol
opTop    = "\x22A4" -- Top/true constant symbol
opBottom = "\x22A5" -- Bottom/false constant symbol

-- | Derive an instance of the Show type class for FOLForm
instance Show FOLForm where
  show = showFOLForm

-- | Show FOL formula
showFOLForm :: FOLForm -> String
showFOLForm (Exists v f) = (opExists ++ v ++ (showFOLForm f))
showFOLForm (ForAll v f) = (opForAll ++ v ++ (showFOLForm f))
showFOLForm (And f1 f2)  = "(" ++ (showFOLForm f1) ++ " " ++ opAnd ++ " " ++ (showFOLForm f2) ++ ")"
showFOLForm (Or f1 f2)   = "(" ++ (showFOLForm f1) ++ ") " ++ opOr  ++ " (" ++ (showFOLForm f2) ++ ")"
showFOLForm (Imp f1 f2)  = "(" ++ (showFOLForm f1) ++ ") " ++ opImp ++ " (" ++ (showFOLForm f2) ++ ")"
showFOLForm (Neg f)      = opNeg ++ (showFOLForm f)
showFOLForm (Rel r d)    = r ++ "(" ++ (intercalate "," d) ++ ")"
showFOLForm (Top)        = opTop
showFOLForm (Bottom)     = opBottom

-- | Print FOL formula
printFOLForm :: FOLForm -> IO ()
printFOLForm f = putStrLn $ "\n" ++ showFOLForm f

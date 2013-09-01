{- |
Module      :  Data.DRS.Format.Latex
Copyright   :  (c) Harm Brouwer and Noortje Venhuizen
License     :  Apache-2.0

Maintainer  :  me@hbrouwer.eu
Stability   :  provisional
Portability :  portable

DRS to LaTeX
-}

-- NEW STUFF (needs cleaning)

module Data.DRS.Format.Latex
(
  drsToLatex
, drsToLatexFile
) where

import Data.DRS.Merge
import Data.DRS.Show
import Data.DRS.Structure
import Data.DRS.Variables

import Data.List (intercalate)

texCmdDRSBox = unlines
  [ "\\newcommand{\\drsBox}[2]{"
  , "\\begin{tabular}{c}"
  , "\\noalign{\\smallskip}"
  , "\\begin{tabular}{|l|}"
  , "\\hline"
  , "#1\\\\"
  , "\\hline"
  , "#2\\\\"
  , "\\hline"
  , "\\end{tabular}"
  , "\\smallskip"
  , "\\end{tabular}"
  , "}"
  ]

texCmdDRSLinear = unlines
  [ "\\newcommand{\\drsLinear}[2]{"
  , "[#1: #2]"
  , "}"
  ]

texCmdDRSSet = unlines
  [ "\\newcommand{\\drsSet}[2]{"
  , "$<$\\{#1\\},\\{#2\\}$>$"
  , "}"
  ]

drsToLatex :: DRSNotation DRS -> String
drsToLatex n =
  case n of
    (Boxes d)  -> texCmdDRSBox    ++ texDRSBox rd
      where rd = drsResolveMerges d
    (Linear d) -> texCmdDRSLinear ++ texDRSLinear rd
      where rd = drsResolveMerges d
    (Set d)    -> texCmdDRSSet    ++ texDRSSet rd
      where rd = drsResolveMerges d

drsToLatexFile :: DRSNotation DRS -> String -> IO ()
drsToLatexFile n fn = writeFile fn (drsToLatex n)

texOpNeg     = "$\\neg$"
texOpImp     = "$\\Rightarrow$"
texOpOr      = "$\\vee$"
texOpDiamond = "$\\Diamond$"
texOpBox     = "$\\Box$"
texOpLamdba  = "$\\lambda$"
texOpMerge   = "$+$"

texDRSBox :: DRS -> String
texDRSBox (LambdaDRS (v,_)) = v ++ "\\"
texDRSBox (Merge d1 d2)     = texDRSBox d1 ++ texOpMerge ++ texDRSBox d2
texDRSBox (DRS u c)         = "\\drsBox"
  ++ "{" ++ unwords (map drsRefToDRSVar u) ++ "}"
  ++ "{" ++ intercalate " \\\\ " (map showCon c) ++ "}"
  where showCon  :: DRSCon -> String
        showCon (Rel r d)    = r ++ "(" ++ intercalate "," (map drsRefToDRSVar d) ++ ")"
        showCon (Neg d1)     = texOpNeg ++ texDRSBox d1
        showCon (Imp d1 d2)  = texDRSBox d1 ++ texOpImp ++ texDRSBox d2
        showCon (Or d1 d2)   = texDRSBox d1 ++ texOpOr  ++ texDRSBox d2
        showCon (Prop r d1)  = drsRefToDRSVar r ++ ": " ++ texDRSBox d1
        showCon (Diamond d1) = texOpDiamond ++ texDRSBox d1
        showCon (Box d1)     = texOpBox ++ texDRSBox d1

texDRSLinear :: DRS -> String
texDRSLinear (LambdaDRS (v,_)) = v ++ "\\"
texDRSLinear (Merge d1 d2)     = texDRSLinear d1 ++ texOpMerge ++ texDRSLinear d2
texDRSLinear (DRS u c) = "\\drsLinear"
  ++ "{" ++ intercalate "," (map drsRefToDRSVar u) ++ "}"
  ++ "{" ++ intercalate "," (map showCon c) ++ "}"
  where showCon  :: DRSCon -> String
        showCon (Rel r d)    = r ++ "(" ++ intercalate "," (map drsRefToDRSVar d) ++ ")"
        showCon (Neg d1)     = texOpNeg ++ texDRSLinear d1
        showCon (Imp d1 d2)  = texDRSLinear d1 ++ texOpImp ++ texDRSLinear d2
        showCon (Or d1 d2)   = texDRSLinear d1 ++ texOpOr  ++ texDRSLinear d2
        showCon (Prop r d1)  = drsRefToDRSVar r ++ ": " ++ texDRSLinear d1
        showCon (Diamond d1) = texOpDiamond ++ texDRSLinear d1
        showCon (Box d1)     = texOpBox ++ texDRSLinear d1

texDRSSet :: DRS -> String
texDRSSet (LambdaDRS (v,_)) = v ++ "\\"
texDRSSet (Merge d1 d2)     = texDRSSet d1 ++ texOpMerge ++ texDRSSet d2
texDRSSet (DRS u c) = "\\drsSet"
  ++ "{" ++ intercalate "," (map drsRefToDRSVar u) ++ "}"
  ++ "{" ++ intercalate "," (map showCon c) ++ "}"
  where showCon  :: DRSCon -> String
        showCon (Rel r d)    = r ++ "(" ++ intercalate "," (map drsRefToDRSVar d) ++ ")"
        showCon (Neg d1)     = texOpNeg ++ texDRSSet d1
        showCon (Imp d1 d2)  = texDRSSet d1 ++ texOpImp ++ texDRSSet d2
        showCon (Or d1 d2)   = texDRSSet d1 ++ texOpOr  ++ texDRSSet d2
        showCon (Prop r d1)  = drsRefToDRSVar r ++ ": " ++ texDRSSet d1
        showCon (Diamond d1) = texOpDiamond ++ texDRSSet d1
        showCon (Box d1)     = texOpBox ++ texDRSSet d1

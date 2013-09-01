{- |
Module      :  Data.DRS.Format.Latex
Copyright   :  (c) Harm Brouwer and Noortje Venhuizen
License     :  Apache-2.0

Maintainer  :  me@hbrouwer.eu
Stability   :  provisional
Portability :  portable

DRS to LaTeX
-}

module Data.DRS.Format.Latex
(
  drsToLatex
, drsToLatexFile
) where

-- NEW STUFF

import Data.DRS.Merge
import Data.DRS.Show
import Data.DRS.Structure
import Data.DRS.Variables

import Data.List (intercalate)

texBoxCmd = unlines
  [ "\\newcommand{\\drs}[2]"
  , "{\\begin{tabular}{c}"
  , "\\noalign{\\smallskip}"
  , "\\begin{tabular}{|l|}"
  , "\\hline"
  , "#1\\\\"
  , "\\hline"
  , "#2\\\\"
  , "\\hline"
  , "\\end{tabular}"
  , "\\smallskip"
  , "\\end{tabular}}"
  ]

drsToLatex :: DRSNotation DRS -> String
drsToLatex n =
  case n of
    (Boxes d) -> texBoxCmd ++ texDRSBox rd
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
texDRSBox (DRS u c) = "\\drs"
  ++ "{" ++ intercalate " " (map drsRefToDRSVar u) ++ "}"
  ++ "{" ++ intercalate " \\\\ " (map showCon c) ++ "}"
  where showCon  :: DRSCon -> String
        showCon (Rel r d)    = r ++ "(" ++ intercalate "," (map drsRefToDRSVar d) ++ ")"
        showCon (Neg d1)     = texOpNeg ++ texDRSBox d1
        showCon (Imp d1 d2)  = texDRSBox d1 ++ texOpImp ++ texDRSBox d2
        showCon (Or d1 d2)   = texDRSBox d1 ++ texOpOr  ++ texDRSBox d2
        showCon (Prop r d1)  = drsRefToDRSVar r ++ ": " ++ texDRSBox d1
        showCon (Diamond d1) = texOpDiamond ++ texDRSBox d1
        showCon (Box d1)     = texOpBox ++ texDRSBox d1


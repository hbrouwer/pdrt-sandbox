{- |
Module      :  Data.PDRS.ProjectionGraph
Copyright   :  (c) Harm Brouwer and Noortje Venhuizen
License     :  Apache-2.0

Maintainer  :  me@hbrouwer.eu
Stability   :  provisional
Portability :  portable

PDRS projection table
-}

module Data.PDRS.ProjectionTable
(
  projectionTable
, showPTable
, printPTable
) where

import Data.DRS.Show
import Data.DRS.Structure (DRSRel, DRSVar)
import Data.DRS.Variables (drsRefToDRSVar)

import Data.PDRS.Structure (PCon (..), PDRS (..), pdrsLabel, PDRSRef (..), PRef (..), PVar)
import qualified Data.PDRS.Structure as PDRS
import Data.PDRS.Variables

import Data.List (intercalate)

instance Show PTable where
  show pt = '\n' : showPTable pt

data PTable = PTable [Item]
  deriving (Eq)

type Item = (Content,PVar,[PVar])

data Content =
  Ref PDRSRef
  | Rel DRSRel [PDRSRef]
  | Neg PVar
  | Imp PVar PVar
  | Or PVar PVar
  | Prop PDRSRef PVar
  | Diamond PVar
  | Box PVar
  deriving (Eq)

projectionTable :: PDRS -> PTable
projectionTable = PTable . pdrsToItems

pdrsToItems :: PDRS -> [Item]
pdrsToItems (LambdaPDRS _) = []
pdrsToItems (AMerge p1 p2) = pdrsToItems p1 ++ pdrsToItems p2
pdrsToItems (PMerge p1 p2) = pdrsToItems p1 ++ pdrsToItems p2
pdrsToItems (PDRS l _ u c) = universeToItems u l ++ pconsToItems c l

universeToItems :: [PRef] -> PVar -> [Item]
universeToItems [] _                         = []
universeToItems (PRef p r:prs) l = (Ref r,l,[p]) : universeToItems prs l

pconsToItems :: [PCon] -> PVar -> [Item]
pconsToItems [] _ = []
pconsToItems (PCon p (PDRS.Rel r d):pcs)    l = (Rel r d,l,[p])                : pconsToItems pcs l
pconsToItems (PCon p (PDRS.Neg p1):pcs)     l = (Neg     (pdrsLabel p1),l,[p]) : pdrsToItems p1     ++ pconsToItems pcs l
pconsToItems (PCon p (PDRS.Imp p1 p2):pcs)  l = (Imp     (pdrsLabel p1) (pdrsLabel p2),l,[p]) : pdrsToItems p1 ++ pdrsToItems p2 ++ pconsToItems pcs l
pconsToItems (PCon p (PDRS.Or p1 p2):pcs)   l = (Or      (pdrsLabel p1) (pdrsLabel p2),l,[p]) : pdrsToItems p1 ++ pdrsToItems p2 ++ pconsToItems pcs l
pconsToItems (PCon p (PDRS.Prop r p1):pcs)  l = (Prop r  (pdrsLabel p1),l,[p]) : pdrsToItems p1     ++ pconsToItems pcs l
pconsToItems (PCon p (PDRS.Diamond p1):pcs) l = (Diamond (pdrsLabel p1),l,[p]) : pdrsToItems p1     ++ pconsToItems pcs l
pconsToItems (PCon p (PDRS.Box p1):pcs)     l = (Box     (pdrsLabel p1),l,[p]) : pdrsToItems p1     ++ pconsToItems pcs l

showPTable :: PTable -> String
showPTable (PTable is) = "[Type]\t[Content]\t[Intro st]\t[Proj. st]\n" ++ concatMap showItem is

showItem :: Item -> String
showItem (c,is,ps) =
  case c of
    (Ref r)       -> "Ref" ++ "\t" ++ showRef r ++ "\t\t" ++ show is ++ "\t\t" ++ intercalate "," (map show ps) ++ "\n"
    (Rel r d)     -> "Con" ++ "\t" ++ r ++ "("  ++ intercalate "," (map showRef d) ++ ")" ++ "\t\t"  ++ show is ++ "\t\t" ++ intercalate "," (map show ps) ++ "\n"
    (Neg pv)      -> "Con" ++ "\t" ++ opNeg     ++ show pv ++ "\t\t" ++ show is ++ "\t\t" ++ intercalate "," (map show ps) ++ "\n"
    (Imp pv1 pv2) -> "Con" ++ "\t" ++ show pv1  ++ " " ++ opImp ++ " " ++ show pv2 ++ "\t\t" ++ show is ++ "\t\t" ++ intercalate "," (map show ps) ++ "\n"
    (Or pv1 pv2)  -> "Con" ++ "\t" ++ show pv1  ++ " " ++ opOr  ++ " " ++ show pv2 ++ "\t\t" ++ show is ++ "\t\t" ++ intercalate "," (map show ps) ++ "\n"
    (Prop r pv)   -> "Con" ++ "\t" ++ showRef r ++ ":" ++ show pv ++ "\t\t" ++ show is ++ "\t\t" ++ intercalate "," (map show ps) ++ "\n"
    (Diamond pv)  -> "Con" ++ "\t" ++ opDiamond ++ show pv ++ "\t\t" ++ show is ++ "\t\t" ++ intercalate "," (map show ps) ++ "\n"
    (Box pv)      -> "Con" ++ "\t" ++ opBox     ++ show pv ++ "\t\t" ++ show is ++ "\t\t" ++ intercalate "," (map show ps) ++ "\n"
  where showRef :: PDRSRef -> DRSVar
        showRef = drsRefToDRSVar . pdrsRefToDRSRef

printPTable :: PTable -> IO ()
printPTable pt = putStrLn $ '\n' : showPTable pt

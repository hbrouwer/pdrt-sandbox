{- |
Module      :  Data.PDRS.ProjectionGraph
Copyright   :  (c) Harm Brouwer and Noortje Venhuizen
License     :  Apache-2.0

Maintainer  :  me@hbrouwer.eu, n.j.venhuizen@rug.nl
Stability   :  provisional
Portability :  portable

PDRS projection table
-}

module Data.PDRS.ProjectionTable
(
  PTable
, projectionTable
, showPTable
, printPTable
) where

import Data.DRS.DataType (DRSVar)
import Data.DRS.Show
import Data.DRS.Variables (drsRefToDRSVar,drsRelToString)

import Data.PDRS.DataType (PCon (..), PDRS (..), PDRSRef (..), PDRSRel (..), PRef (..), PVar)
import qualified Data.PDRS.DataType as PDRS
import Data.PDRS.Structure
import Data.PDRS.Variables

import Data.List (intercalate)

---------------------------------------------------------------------------
-- * Exported
---------------------------------------------------------------------------

---------------------------------------------------------------------------
-- | Projection table
---------------------------------------------------------------------------
data PTable = PTable [Item]
  deriving (Eq)

-- | Derive and instance of the Show typeclass for 'PTable'.
instance Show PTable where
  show pt = '\n' : showPTable pt

---------------------------------------------------------------------------
-- | Derives the projection table of a 'PDRS'
---------------------------------------------------------------------------
projectionTable :: PDRS -> PTable
projectionTable = PTable . pdrsToItems

---------------------------------------------------------------------------
-- | Shows a projection table
---------------------------------------------------------------------------
showPTable :: PTable -> String
showPTable (PTable is) = "[Type]\t[Content]\t[Intro st]\t[Proj. st]\n" ++ concatMap showItem is

---------------------------------------------------------------------------
-- | Prints a projection table
---------------------------------------------------------------------------
printPTable :: PTable -> IO ()
printPTable pt = putStrLn $ '\n' : showPTable pt

---------------------------------------------------------------------------
-- * Private
---------------------------------------------------------------------------

---------------------------------------------------------------------------
-- | Rows of a 'PTable'
---------------------------------------------------------------------------
type Item = (Content,PVar,PVar)

-- | Shows an 'Item'
showItem :: Item -> String
showItem (c,is,ps) =
  case c of
    (Ref r)       -> "Ref" ++ "\t" ++ showRef r ++ tail
    (Rel r d)     -> "Con" ++ "\t" ++ drsRelToString (pdrsRelToDRSRel r) ++ "("  ++ intercalate "," (map showRef d) ++ ")" ++ tail
    (Neg pv)      -> "Con" ++ "\t" ++ opNeg     ++ " " ++ show pv ++ tail
    (Imp pv1 pv2) -> "Con" ++ "\t" ++ show pv1  ++ " " ++ opImp ++ " " ++ show pv2 ++ tail
    (Or pv1 pv2)  -> "Con" ++ "\t" ++ show pv1  ++ " " ++ opOr  ++ " " ++ show pv2 ++ tail
    (Prop r pv)   -> "Con" ++ "\t" ++ showRef r ++ ":" ++ show pv ++ tail
    (Diamond pv)  -> "Con" ++ "\t" ++ opDiamond ++ " " ++ show pv ++ tail
    (Box pv)      -> "Con" ++ "\t" ++ opBox     ++ " " ++ show pv ++ tail
  where tail = "\t\t" ++ show is ++ "\t\t" ++ show ps ++ "\n"
        showRef :: PDRSRef -> DRSVar
        showRef = drsRefToDRSVar . pdrsRefToDRSRef

---------------------------------------------------------------------------
-- | First column of a 'PTable'
---------------------------------------------------------------------------
data Content =
  Ref PDRSRef
  | Rel PDRSRel [PDRSRef]
  | Neg PVar
  | Imp PVar PVar
  | Or PVar PVar
  | Prop PDRSRef PVar
  | Diamond PVar
  | Box PVar
  deriving (Eq)

---------------------------------------------------------------------------
-- | Converts a 'PDRS' into a list of 'Item's
---------------------------------------------------------------------------
pdrsToItems :: PDRS -> [Item]
pdrsToItems (LambdaPDRS _) = []
pdrsToItems (AMerge p1 p2) = pdrsToItems p1 ++ pdrsToItems p2
pdrsToItems (PMerge p1 p2) = pdrsToItems p1 ++ pdrsToItems p2
pdrsToItems (PDRS l _ u c) = universeToItems u l ++ pconsToItems c l

---------------------------------------------------------------------------
-- | Converts the universe of a 'PDRS' into a list of 'Item's
---------------------------------------------------------------------------
universeToItems :: [PRef] -> PVar -> [Item]
universeToItems [] _                         = []
universeToItems (PRef p r:prs) l = (Ref r,l,p) : universeToItems prs l

---------------------------------------------------------------------------
-- | Converts a list of 'PCon's into a list of 'Item's
---------------------------------------------------------------------------
pconsToItems :: [PCon] -> PVar -> [Item]
pconsToItems [] _ = []
pconsToItems (PCon p (PDRS.Rel r d):pcs)    l = (Rel r d,l,p)                : pconsToItems pcs l
pconsToItems (PCon p (PDRS.Neg p1):pcs)     l = (Neg     (pdrsLabel p1),l,p) : pdrsToItems p1     ++ pconsToItems pcs l
pconsToItems (PCon p (PDRS.Imp p1 p2):pcs)  l = (Imp     (pdrsLabel p1) (pdrsLabel p2),l,p) : pdrsToItems p1 ++ pdrsToItems p2 ++ pconsToItems pcs l
pconsToItems (PCon p (PDRS.Or p1 p2):pcs)   l = (Or      (pdrsLabel p1) (pdrsLabel p2),l,p) : pdrsToItems p1 ++ pdrsToItems p2 ++ pconsToItems pcs l
pconsToItems (PCon p (PDRS.Prop r p1):pcs)  l = (Prop r  (pdrsLabel p1),l,p) : pdrsToItems p1     ++ pconsToItems pcs l
pconsToItems (PCon p (PDRS.Diamond p1):pcs) l = (Diamond (pdrsLabel p1),l,p) : pdrsToItems p1     ++ pconsToItems pcs l
pconsToItems (PCon p (PDRS.Box p1):pcs)     l = (Box     (pdrsLabel p1),l,p) : pdrsToItems p1     ++ pconsToItems pcs l


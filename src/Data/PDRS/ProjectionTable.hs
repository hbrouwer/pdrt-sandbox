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
  PTableItem
, PTableContent
, PTable
, showPTable
, printPTable
, pdrsToPTable
) where

import Data.DRS.Show

import Data.PDRS.DataType (PDRS(..), PVar, PRef(..), PDRSRef(..), PCon(..), PDRSRel(..))
import qualified Data.PDRS.DataType as PDRS
import Data.PDRS.Variables

import Data.List (intercalate)

---------------------------------------------------------------------------
-- * Exported
---------------------------------------------------------------------------

---------------------------------------------------------------------------
-- ** Defining a PTable
---------------------------------------------------------------------------

---------------------------------------------------------------------------
-- | Rows of a 'PTable'
---------------------------------------------------------------------------
type PTableItem = (PTableContent,PVar,PVar)

---------------------------------------------------------------------------
-- | First column of a 'PTable'
---------------------------------------------------------------------------
data PTableContent =
  MAP (PVar,PVar)
  | Ref PDRSRef
  | Rel PDRSRel [PDRSRef]
  | Neg PVar
  | Imp PVar PVar
  | Or PVar PVar
  | Prop PDRSRef PVar
  | Diamond PVar
  | Box PVar
  deriving (Eq)

---------------------------------------------------------------------------
-- | Projection table
---------------------------------------------------------------------------
data PTable = PTable [PTableItem]
  deriving (Eq)

-- | Derive and instance of the Show typeclass for 'PTable'.
instance Show PTable where
  show pt = '\n' : showPTable pt

---------------------------------------------------------------------------
-- | Shows a projection table
---------------------------------------------------------------------------
showPTable :: PTable -> String
showPTable (PTable is) = "[Type]\t[Content]\t[Intro st]\t[Proj. st]\n" ++ concatMap showPTableItem is

---------------------------------------------------------------------------
-- | Prints a projection table
---------------------------------------------------------------------------
printPTable :: PTable -> IO ()
printPTable pt = putStrLn $ '\n' : showPTable pt

---------------------------------------------------------------------------
-- | Derives the projection table of a 'PDRS'
---------------------------------------------------------------------------
pdrsToPTable :: PDRS -> PTable
pdrsToPTable = PTable . pdrsToItems

---------------------------------------------------------------------------
-- * Private
---------------------------------------------------------------------------

---------------------------------------------------------------------------
-- | Shows an 'PTableItem'
---------------------------------------------------------------------------
showPTableItem :: PTableItem -> String
showPTableItem (c,is,ps) =
  case c of
    (MAP m)       -> "MAP" ++ "\t" ++ show m            ++ tail'
    (Ref r)       -> "Ref" ++ "\t" ++ pdrsRefToDRSVar r ++ tail'
    (Rel r d)     -> "Con" ++ "\t" ++ pdrsRelToString r ++ "(" ++ intercalate "," (map pdrsRefToDRSVar d) ++ ")" ++ tail'
    (Neg pv)      -> "Con" ++ "\t" ++ opNeg             ++ " " ++ show pv ++ tail'
    (Imp pv1 pv2) -> "Con" ++ "\t" ++ show pv1          ++ " " ++ opImp   ++ " " ++ show pv2 ++ tail'
    (Or pv1 pv2)  -> "Con" ++ "\t" ++ show pv1          ++ " " ++ opOr    ++ " " ++ show pv2 ++ tail'
    (Prop r pv)   -> "Con" ++ "\t" ++ pdrsRefToDRSVar r ++ ":" ++ show pv ++ tail'
    (Diamond pv)  -> "Con" ++ "\t" ++ opDiamond         ++ " " ++ show pv ++ tail'
    (Box pv)      -> "Con" ++ "\t" ++ opBox             ++ " " ++ show pv ++ tail'
  where tail' = "\t\t" ++ show is ++ "\t\t" ++ show ps ++ "\n"

---------------------------------------------------------------------------
-- | Converts a 'PDRS' into a list of 'PTableItem's
---------------------------------------------------------------------------
pdrsToItems :: PDRS -> [PTableItem]
pdrsToItems (LambdaPDRS _) = []
pdrsToItems (AMerge p1 p2) = pdrsToItems p1 ++ pdrsToItems p2
pdrsToItems (PMerge p1 p2) = pdrsToItems p1 ++ pdrsToItems p2
pdrsToItems (PDRS l m u c) = (MAP (l,l),l,l) : map (\x -> (MAP x,l,l)) m ++ universeToItems u l ++ pconsToItems c l

---------------------------------------------------------------------------
-- | Converts the universe of a 'PDRS' into a list of 'PTableItem's
---------------------------------------------------------------------------
universeToItems :: [PRef] -> PVar -> [PTableItem]
universeToItems [] _                         = []
universeToItems (PRef p r:prs) l = (Ref r,l,p) : universeToItems prs l

---------------------------------------------------------------------------
-- | Converts a list of 'PCon's into a list of 'PTableItem's
---------------------------------------------------------------------------
pconsToItems :: [PCon] -> PVar -> [PTableItem]
pconsToItems [] _     = []
pconsToItems [c] l = case c of
  (PCon p (PDRS.Rel r d))    -> [(Rel r d,l,p)]
  (PCon p (PDRS.Neg p1))     -> (Neg     (pdrsLabel p1),l,p)                : pdrsToItems p1 
  (PCon p (PDRS.Imp p1 p2))  -> (Imp     (pdrsLabel p1) (pdrsLabel p2),l,p) : pdrsToItems p1 ++ pdrsToItems p2
  (PCon p (PDRS.Or p1 p2))   -> (Or      (pdrsLabel p1) (pdrsLabel p2),l,p) : pdrsToItems p1 ++ pdrsToItems p2
  (PCon p (PDRS.Prop r p1))  -> (Prop r  (pdrsLabel p1),l,p)                : pdrsToItems p1
  (PCon p (PDRS.Diamond p1)) -> (Diamond (pdrsLabel p1),l,p)                : pdrsToItems p1
  (PCon p (PDRS.Box p1))     -> (Box     (pdrsLabel p1),l,p)                : pdrsToItems p1
pconsToItems (c:cs) l = pconsToItems [c] l ++ pconsToItems cs l

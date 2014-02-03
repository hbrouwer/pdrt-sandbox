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
, showPTable
, printPTable
, pdrsToPTable
, pTableToPDRS
, pTableToDRS
) where

import Data.DRS.DataType (DRS,DRSVar)
import Data.DRS.Show
import Data.DRS.Variables (drsRefToDRSVar,drsRelToString)

import Data.PDRS.DataType (PDRS(..), PVar, PRef(..), PDRSRef(..), PCon(..), PDRSRel(..))
import qualified Data.PDRS.DataType as PDRS
import Data.PDRS.LambdaCalculus (pdrsPurify)
import Data.PDRS.Structure
import Data.PDRS.Translate (stripPVars)
import Data.PDRS.Variables

import Data.List ((\\), intercalate, nub, union)
import Data.Maybe (fromJust, isNothing)

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
-- | Derives the projection table of a 'PDRS'
---------------------------------------------------------------------------
pdrsToPTable :: PDRS -> PTable
pdrsToPTable = PTable . pdrsToItems

---------------------------------------------------------------------------
-- | Translates a 'PTable' into a 'PDRS'
---------------------------------------------------------------------------
pTableToPDRS :: PTable -> PDRS
pTableToPDRS pt@(PTable t) = insertItems t Introduction (PDRS (ptOuterLabel pt) [] [] [])

---------------------------------------------------------------------------
-- | Translates a 'PTable' into a 'DRS'
---------------------------------------------------------------------------
pTableToDRS :: PTable -> DRS
pTableToDRS pt = stripPVars $ insertItems t Projection (PDRS (ptOuterLabel pt) [] [] [])
  where PTable t = ptAccommodate pt

---------------------------------------------------------------------------
-- * Private
---------------------------------------------------------------------------

---------------------------------------------------------------------------
-- ** Defining a PTable
---------------------------------------------------------------------------

---------------------------------------------------------------------------
-- | Rows of a 'PTable'
---------------------------------------------------------------------------
type Item = (Content,PVar,PVar)

---------------------------------------------------------------------------
-- | First column of a 'PTable'
---------------------------------------------------------------------------
data Content =
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
-- | Data type for accommodation site
---------------------------------------------------------------------------
data Site = Introduction | Projection
  deriving(Eq)

---------------------------------------------------------------------------
-- | Shows an 'Item'
---------------------------------------------------------------------------
showItem :: Item -> String
showItem (c,is,ps) =
  case c of
    (MAP m)       -> "MAP" ++ "\t" ++ show m            ++ tail
    (Ref r)       -> "Ref" ++ "\t" ++ pdrsRefToDRSVar r ++ tail
    (Rel r d)     -> "Con" ++ "\t" ++ pdrsRelToString r ++ "(" ++ intercalate "," (map pdrsRefToDRSVar d) ++ ")" ++ tail
    (Neg pv)      -> "Con" ++ "\t" ++ opNeg             ++ " " ++ show pv ++ tail
    (Imp pv1 pv2) -> "Con" ++ "\t" ++ show pv1          ++ " " ++ opImp   ++ " " ++ show pv2 ++ tail
    (Or pv1 pv2)  -> "Con" ++ "\t" ++ show pv1          ++ " " ++ opOr    ++ " " ++ show pv2 ++ tail
    (Prop r pv)   -> "Con" ++ "\t" ++ pdrsRefToDRSVar r ++ ":" ++ show pv ++ tail
    (Diamond pv)  -> "Con" ++ "\t" ++ opDiamond         ++ " " ++ show pv ++ tail
    (Box pv)      -> "Con" ++ "\t" ++ opBox             ++ " " ++ show pv ++ tail
  where tail = "\t\t" ++ show is ++ "\t\t" ++ show ps ++ "\n"


---------------------------------------------------------------------------
-- | Converts a 'PDRS' into a list of 'Item's
---------------------------------------------------------------------------
pdrsToItems :: PDRS -> [Item]
pdrsToItems (LambdaPDRS _) = []
pdrsToItems (AMerge p1 p2) = pdrsToItems p1 ++ pdrsToItems p2
pdrsToItems (PMerge p1 p2) = pdrsToItems p1 ++ pdrsToItems p2
pdrsToItems (PDRS l m u c) = (MAP (l,l),l,l) : map (\x -> (MAP x,l,l)) m ++ universeToItems u l ++ pconsToItems c l

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
pconsToItems [] _     = []
pconsToItems (c:[]) l = case c of
  (PCon p (PDRS.Rel r d))    -> [(Rel r d,l,p)]
  (PCon p (PDRS.Neg p1))     -> (Neg     (pdrsLabel p1),l,p)                : pdrsToItems p1 
  (PCon p (PDRS.Imp p1 p2))  -> (Imp     (pdrsLabel p1) (pdrsLabel p2),l,p) : pdrsToItems p1 ++ pdrsToItems p2
  (PCon p (PDRS.Or p1 p2))   -> (Or      (pdrsLabel p1) (pdrsLabel p2),l,p) : pdrsToItems p1 ++ pdrsToItems p2
  (PCon p (PDRS.Prop r p1))  -> (Prop r  (pdrsLabel p1),l,p)                : pdrsToItems p1
  (PCon p (PDRS.Diamond p1)) -> (Diamond (pdrsLabel p1),l,p)                : pdrsToItems p1
  (PCon p (PDRS.Box p1))     -> (Box     (pdrsLabel p1),l,p)                : pdrsToItems p1
pconsToItems (c:cs) l = pconsToItems [c] l ++ pconsToItems cs l

---------------------------------------------------------------------------
-- ** Operations on 'PTable's
---------------------------------------------------------------------------

---------------------------------------------------------------------------
-- | Returns the outer label of a 'PTable'
---------------------------------------------------------------------------
ptOuterLabel :: PTable -> PVar
ptOuterLabel pt@(PTable t) = head $ filter (`notElem` ptSubPDRSs pt) (map (\(_,i,_) -> i) t)

---------------------------------------------------------------------------
-- | Returns the labels of the subPDRSs of a 'PTable'
---------------------------------------------------------------------------
ptSubPDRSs :: PTable -> [PVar]
ptSubPDRSs (PTable t) = concatMap sub t
  where sub :: Item -> [PVar]
        sub (MAP m,_,_)       = []
        sub (Ref r,_,_)       = []
        sub (Rel r d,_,_)     = []
        sub (Neg pv,_,_)      = [pv]
        sub (Imp pv1 pv2,_,_) = [pv1,pv2]
        sub (Or pv1 pv2,_,_)  = [pv1,pv2]
        sub (Prop r pv,_,_)   = [pv]
        sub (Diamond pv,_,_)  = [pv]
        sub (Box pv,_,_)      = [pv]

---------------------------------------------------------------------------
-- | Converts all free projection contexts in a 'PTable' into the
-- correct accommodation sites.
---------------------------------------------------------------------------
ptAccommodate :: PTable -> PTable
ptAccommodate pt@(PTable t)
  | null fps  = pt
  | otherwise = ptAccommodate (ptRenamePVar (head fps) (accSite (head fps)) pt)
  where fps = ptFreeContexts pt
        accSite :: PVar -> PVar
        accSite p
          | isNothing m = ptOuterLabel pt
          | otherwise   = fromJust m
          where m = lookup p (concatMap maps t)
                maps :: Item -> [PDRS.MAP]
                maps (c,_,_) = case c of
                  (MAP (p1,p2)) -> [(p1,p2)]
                  otherwise     -> []

---------------------------------------------------------------------------
-- | Returns the free projection contexts in a 'PTable'
---------------------------------------------------------------------------
ptFreeContexts :: PTable -> [PVar]
ptFreeContexts pt@(PTable t) = nub $ filter (`notElem` (ptOuterLabel pt:ptSubPDRSs pt)) (map (\(_,_,p) -> p) t)

---------------------------------------------------------------------------
-- | Renames projection variable $v$ into projection variable $v'$ in
-- 'PTable' $t$.
---------------------------------------------------------------------------
ptRenamePVar :: PVar -> PVar -> PTable -> PTable
ptRenamePVar v v' (PTable t) = PTable (map renameItem t)
  where renameItem :: Item -> Item
        renameItem (c,i,p) = case c of
          (MAP (p1,p2)) -> (MAP (rename p1,rename p2),i,rename p)
          otherwise     -> (c,i,rename p)
        rename :: PVar -> PVar
        rename pv
          | pv == v   = v'
          | otherwise = pv

---------------------------------------------------------------------------
-- | Inserts a list of 'Item's in a 'PDRS'
---------------------------------------------------------------------------
insertItems :: [Item] -> Site -> PDRS -> PDRS
insertItems [] _ p = p
insertItems ((c,i,a):is) s p
  | i `elem` pdrsLabels p = insertItems is s (insertItem (c,i,a) site p)
  | otherwise             = insertItems (is ++ [(c,i,a)]) s p
  where site = case s of
          Introduction -> i
          Projection   -> a
        insertItem :: Item -> PVar -> PDRS -> PDRS
        insertItem _ _ lp@(LambdaPDRS _) = lp
        insertItem it st (AMerge p1 p2)  = AMerge (insertItem it st p1) (insertItem it st p2)
        insertItem it st (PMerge p1 p2)  = PMerge (insertItem it st p1) (insertItem it st p2)
        insertItem it@(c',i',p') st pdrs@(PDRS l m u c)
          | st == l    = case c' of
              (MAP (p1,p2))
                | p1 == p2  -> pdrs
                | otherwise -> PDRS l (m `union` [(p1,p2)]) u c
              (Ref r)       -> PDRS l m (u `union` [PRef p' r]) c
              (Rel r d)     -> PDRS l m u (c `union` [PCon p' (PDRS.Rel r d)])
              (Neg pv)      -> PDRS l m u (c `union` [PCon p' (PDRS.Neg (PDRS pv [] [] []))])
              (Imp pv1 pv2) -> PDRS l m u (c `union` [PCon p' (PDRS.Imp (PDRS pv1 [] [] []) (PDRS pv2 [] [] []))])
              (Or pv1 pv2)  -> PDRS l m u (c `union` [PCon p' (PDRS.Or (PDRS pv1 [] [] []) (PDRS pv2 [] [] []))])
              (Prop r pv)   -> PDRS l m u (c `union` [PCon p' (PDRS.Prop r (PDRS pv [] [] []))])
              (Diamond pv)  -> PDRS l m u (c `union` [PCon p' (PDRS.Diamond (PDRS pv [] [] []))])
              (Box pv)      -> PDRS l m u (c `union` [PCon p' (PDRS.Box (PDRS pv [] [] []))])
          | otherwise = PDRS l m u (map (inCon (c',i',p') st) c)
          where inCon :: Item -> PVar -> PCon -> PCon
                inCon i s pc@(PCon _ (PDRS.Rel _ _)) = pc
                inCon i s (PCon p (PDRS.Neg p1))     = PCon p (PDRS.Neg     (insertItem i s p1))
                inCon i s (PCon p (PDRS.Imp p1 p2))  = PCon p (PDRS.Imp     (insertItem i s p1) (insertItem i s p2))
                inCon i s (PCon p (PDRS.Or p1 p2))   = PCon p (PDRS.Or      (insertItem i s p1) (insertItem i s p2))
                inCon i s (PCon p (PDRS.Prop r p1))  = PCon p (PDRS.Prop r  (insertItem i s p1))
                inCon i s (PCon p (PDRS.Diamond p1)) = PCon p (PDRS.Diamond (insertItem i s p1))
                inCon i s (PCon p (PDRS.Box p1))     = PCon p (PDRS.Box     (insertItem i s p1))

{- |
Module      :  Data.PDRS.Structure
Copyright   :  (c) Harm Brouwer and Noortje Venhuizen
License     :  Apache-2.0

Maintainer  :  me@hbrouwer.eu, n.j.venhuizen@rug.nl
Stability   :  provisional
Portability :  portable

Structural operations on PDRSs
-}

module Data.PDRS.Structure
(
  pdrsLabel
, pdrsLabels
, pdrsUniverse
, pdrsUniverses
, emptyPDRS
, isLambdaPDRS
, isMergePDRS
, isResolvedPDRS
, isSubPDRS
) where

import Data.List (union)
import Data.PDRS.DataType

---------------------------------------------------------------------------
-- * Exported
---------------------------------------------------------------------------

---------------------------------------------------------------------------
-- | Returns the label of a 'PDRS'.
---------------------------------------------------------------------------
pdrsLabel :: PDRS -> PVar
pdrsLabel (LambdaPDRS _) = 0
pdrsLabel (AMerge p1 p2)
  | isLambdaPDRS p2 = pdrsLabel p1
  | otherwise       = pdrsLabel p2
pdrsLabel (PMerge p1 p2)
  | isLambdaPDRS p2 = pdrsLabel p1
  | otherwise       = pdrsLabel p2
pdrsLabel (PDRS l _ _ _) = l

---------------------------------------------------------------------------
-- | Returns all the labels in a 'PDRS'.
---------------------------------------------------------------------------
pdrsLabels :: PDRS -> [PVar]
pdrsLabels (LambdaPDRS _) = []
pdrsLabels (AMerge p1 p2) = pdrsLabels p1 ++ pdrsLabels p2
pdrsLabels (PMerge p1 p2) = pdrsLabels p1 ++ pdrsLabels p2 
pdrsLabels (PDRS l _ _ c) = l:concatMap labels c
  where labels :: PCon -> [PVar]
        labels (PCon _ (Rel _ _ ))   = []
        labels (PCon _ (Neg p1))     = pdrsLabels p1
        labels (PCon _ (Imp p1 p2))  = pdrsLabels p1 ++ pdrsLabels p2
        labels (PCon _ (Or p1 p2))   = pdrsLabels p1 ++ pdrsLabels p2
        labels (PCon _ (Prop _ p1))  = pdrsLabels p1
        labels (PCon _ (Diamond p1)) = pdrsLabels p1
        labels (PCon _ (Box p1))     = pdrsLabels p1

---------------------------------------------------------------------------
-- | Returns the universe of a PDRS
---------------------------------------------------------------------------
pdrsUniverse :: PDRS -> [PRef]
pdrsUniverse (LambdaPDRS _)  = []
pdrsUniverse (AMerge p1 p2) = pdrsUniverse p1 ++ pdrsUniverse p2
pdrsUniverse (PMerge p1 p2) = pdrsUniverse p1 ++ pdrsUniverse p2
pdrsUniverse (PDRS _ _ u _) = u

---------------------------------------------------------------------------
-- | Returns the list of projected referents in all universes of a 'PDRS'.
---------------------------------------------------------------------------
pdrsUniverses :: PDRS -> [PRef]
pdrsUniverses (LambdaPDRS _) = []
pdrsUniverses (AMerge p1 p2) = pdrsUniverses p1 `union` pdrsUniverses p2
pdrsUniverses (PMerge p1 p2) = pdrsUniverses p1 `union` pdrsUniverses p2
pdrsUniverses (PDRS _ _ u c) = u `union` universes c
  where universes :: [PCon] -> [PRef]
        universes []                       = []
        universes (PCon _ (Rel _ _):cs)    = universes cs
        universes (PCon _ (Neg p1):cs)     = pdrsUniverses p1 `union` universes cs
        universes (PCon _ (Imp p1 p2):cs)  = pdrsUniverses p1 `union` pdrsUniverses p2 `union` universes cs
        universes (PCon _ (Or p1 p2):cs)   = pdrsUniverses p1 `union` pdrsUniverses p2 `union` universes cs
        universes (PCon _ (Prop _ p1):cs)  = pdrsUniverses p1 `union` universes cs
        universes (PCon _ (Diamond p1):cs) = pdrsUniverses p1 `union` universes cs
        universes (PCon _ (Box p1):cs)     = pdrsUniverses p1 `union` universes cs

---------------------------------------------------------------------------
-- | Returns an empty 'PDRS', if possible with the same label as 'PDRS' @p@.
---------------------------------------------------------------------------
emptyPDRS :: PDRS -> PDRS
emptyPDRS lp@(LambdaPDRS _) = lp
emptyPDRS (AMerge p1 p2)
  | isLambdaPDRS p2 = AMerge (emptyPDRS p1) p2
  | otherwise       = emptyPDRS p2
emptyPDRS (PMerge p1 p2)
  | isLambdaPDRS p2 = PMerge (emptyPDRS p1) p2
  | otherwise       = emptyPDRS p2
emptyPDRS (PDRS l _ _ _)    = PDRS l [] [] []

---------------------------------------------------------------------------
-- | Returns whether a PDRS is entirely a 'LambdaPDRS' (at its top-level)
---------------------------------------------------------------------------
isLambdaPDRS :: PDRS -> Bool
isLambdaPDRS (LambdaPDRS {}) = True
isLambdaPDRS (AMerge p1 p2)  = isLambdaPDRS p1 && isLambdaPDRS p2
isLambdaPDRS (PMerge p1 p2)  = isLambdaPDRS p1 && isLambdaPDRS p2
isLambdaPDRS (PDRS {})       = False

---------------------------------------------------------------------------
-- | Returns whether a 'PDRS' is an 'AMerge' or 'PMerge' (at its top-level)
---------------------------------------------------------------------------
isMergePDRS :: PDRS -> Bool
isMergePDRS (LambdaPDRS {}) = False
isMergePDRS (AMerge {})     = True
isMergePDRS (PMerge {})     = True
isMergePDRS (PDRS {})       = False

---------------------------------------------------------------------------
-- | Returns whether a 'PDRS' is resolved (containing no unresolved merges 
-- or lambdas)
---------------------------------------------------------------------------
isResolvedPDRS :: PDRS -> Bool
isResolvedPDRS (LambdaPDRS {}) = False
isResolvedPDRS (AMerge {})     = False
isResolvedPDRS (PMerge {})     = False
isResolvedPDRS (PDRS _ _ u c)  = all isResolvedRef (map (\(PRef _ r) -> r) u) && all isResolvedPCon c
  where isResolvedRef :: PDRSRef -> Bool
        isResolvedRef (LambdaPDRSRef _) = False
        isResolvedRef (PDRSRef _)       = True
        isResolvedPCon :: PCon -> Bool
        isResolvedPCon (PCon _ (Rel _ d))    = all isResolvedRef d
        isResolvedPCon (PCon _ (Neg p1))     = isResolvedPDRS p1
        isResolvedPCon (PCon _ (Imp p1 p2))  = isResolvedPDRS p1 && isResolvedPDRS p2
        isResolvedPCon (PCon _ (Or p1 p2))   = isResolvedPDRS p1 && isResolvedPDRS p2
        isResolvedPCon (PCon _ (Prop r p1))  = isResolvedRef r && isResolvedPDRS p1
        isResolvedPCon (PCon _ (Diamond p1)) = isResolvedPDRS p1
        isResolvedPCon (PCon _ (Box p1))     = isResolvedPDRS p1

---------------------------------------------------------------------------
-- | Returns whether 'PDRS' @p1@ is a direct or indirect sub-'PDRS' of
-- 'PDRS' @p2@.
---------------------------------------------------------------------------
isSubPDRS :: PDRS -> PDRS -> Bool
isSubPDRS _  (LambdaPDRS _)    = False
isSubPDRS p1 (AMerge p2 p3)    = isSubPDRS p1 p2 || isSubPDRS p1 p3
isSubPDRS p1 (PMerge p2 p3)    = isSubPDRS p1 p2 || isSubPDRS p1 p3
isSubPDRS p1 p2@(PDRS _ _ _ c) = p1 == p2 || any subPDRS c
  where subPDRS :: PCon -> Bool
        subPDRS (PCon _ (Rel _ _ ))   = False
        subPDRS (PCon _ (Neg p3))     = isSubPDRS p1 p3
        subPDRS (PCon _ (Imp p3 p4))  = isSubPDRS p1 p3 || isSubPDRS p1 p4
        subPDRS (PCon _ (Or p3 p4))   = isSubPDRS p1 p3 || isSubPDRS p1 p4
        subPDRS (PCon _ (Prop _ p3))  = isSubPDRS p1 p3
        subPDRS (PCon _ (Diamond p3)) = isSubPDRS p1 p3
        subPDRS (PCon _ (Box p3))     = isSubPDRS p1 p3

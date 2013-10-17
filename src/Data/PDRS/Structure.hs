{- |
Module      :  Data.PDRS.Structure
Copyright   :  (c) Harm Brouwer and Noortje Venhuizen
License     :  Apache-2.0

Maintainer  :  me@hbrouwer.eu
Stability   :  provisional
Portability :  portable

PDRS data structure
-}

module Data.PDRS.Structure
(
  PDRS (..)
, DRSVar
, PVar
, PRef (..)
, PDRSRef (..)
, PCon (..)
, PDRSCon (..)
, DRSRel
, pdrsLabel
, isSubPDRS
) where

import Data.DRS.Structure (DRSRel, DRSVar)

-- | Projective Discourse Representation Structure (PDRS)
data PDRS =
  LambdaPDRS (DRSVar,Int)                 -- ^ A lambda PDRS (with its argument position)
  | AMerge PDRS PDRS                      -- ^ An assertive merge between two PDRSs
  | PMerge PDRS PDRS                      -- ^ A projective merge between two PDRSs
  -- | A PDRS (a label, a list of minimally accessible PDRSs,
  -- a set of projected referents, and a set of projected conditions
  | PDRS PVar [(PVar,PVar)] [PRef] [PCon]
  deriving (Eq)

-- | Projection variable (a label or pointer)
type PVar = Int

-- | A projected referent (a projection pointer and a DRS referent)
data PRef = PRef PVar PDRSRef
  deriving (Eq)

-- | A PDRS referent
data PDRSRef =
  LambdaPDRSRef (DRSVar, Int) -- ^ A lambda PDRS referent (with its argument position)
  | PDRSRef DRSVar            -- ^ A PDRS referent
  deriving (Eq)

-- | A projected condition (a projection pointer and a PDRS condition)
data PCon = PCon PVar PDRSCon
  deriving (Eq)

-- | A PDRS Condition
data PDRSCon = 
  Rel DRSRel [PDRSRef] -- ^ A relation defined on a set of referents
  | Neg PDRS           -- ^ A negated PDRS
  | Imp PDRS PDRS      -- ^ An implication between two PDRSs
  | Or PDRS PDRS       -- ^ A disjunction between two PDRSs
  | Prop PDRSRef PDRS  -- ^ A proposition PDRS
  | Diamond PDRS       -- ^ A possible PDRS
  | Box PDRS           -- ^ A necessary PDRS
  deriving (Eq)

-- | Returns the label of a PDRS
pdrsLabel :: PDRS -> PVar
pdrsLabel (PDRS l _ _ _) = l

-- | Returns whether PDRS @p1@ is a direct or indirect sub-PDRS of PDRS @p2@
isSubPDRS :: PDRS -> PDRS -> Bool
isSubPDRS p1 (LambdaPDRS _)    = False
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

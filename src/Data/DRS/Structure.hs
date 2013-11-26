{- |
Module      :  Data.DRS.Structure
Copyright   :  (c) Harm Brouwer and Noortje Venhuizen
License     :  Apache-2.0

Maintainer  :  me@hbrouwer.eu, n.j.venhuizen@rug.nl
Stability   :  provisional
Portability :  portable

DRS data structure
-}

module Data.DRS.Structure
(
  DRS (..)
, DRSVar
, DRSRel
, DRSRef (..)
, DRSCon (..)
, drsUniverse
, isSubDRS
) where

import Data.List (union)

---------------------------------------------------------------------------
-- * Exported
---------------------------------------------------------------------------

---------------------------------------------------------------------------
-- ** DRS data type
---------------------------------------------------------------------------

---------------------------------------------------------------------------
-- | Discourse Representation Structure (DRS)
---------------------------------------------------------------------------
data DRS =
  LambdaDRS ((DRSVar,[DRSVar]),Int)  -- ^ A lambda DRS (with its argument position)
  | Merge DRS DRS         -- ^ A merge between two DRSs
  | DRS [DRSRef] [DRSCon] -- ^ A DRS (a set of referents and a set of conditions)
  deriving (Eq)

---------------------------------------------------------------------------
-- | DRS variable
---------------------------------------------------------------------------
type DRSVar = String

---------------------------------------------------------------------------
-- | DRS relation
---------------------------------------------------------------------------
type DRSRel = String

---------------------------------------------------------------------------
-- | DRS referent
---------------------------------------------------------------------------
data DRSRef =
  LambdaDRSRef ((DRSVar,[DRSVar]),Int) -- ^ A lambda DRS referent (with its argument position)
  | DRSRef DRSVar            -- ^ A DRS referent
  deriving (Eq)

---------------------------------------------------------------------------
-- | DRS condition
---------------------------------------------------------------------------
data DRSCon = 
  Rel DRSRel [DRSRef] -- ^ A relation defined on a set of referents
  | Neg DRS           -- ^ A negated DRS
  | Imp DRS DRS       -- ^ An implication between two DRSs
  | Or DRS DRS        -- ^ A disjunction between two DRSs
  | Prop DRSRef DRS   -- ^ A proposition DRS
  | Diamond DRS       -- ^ A possible DRS
  | Box DRS           -- ^ A necessary DRS
  deriving (Eq)

---------------------------------------------------------------------------
-- ** Basic functions on DRSs
---------------------------------------------------------------------------

---------------------------------------------------------------------------
-- | Returns the universe of a DRS
---------------------------------------------------------------------------
drsUniverse :: DRS -> [DRSRef]
drsUniverse (LambdaDRS _) = []
drsUniverse (Merge d1 d2) = drsUniverse d1 `union` drsUniverse d2
drsUniverse (DRS u _)     = u

---------------------------------------------------------------------------
-- | Returns whether DRS @d1@ is a direct or indirect sub-DRS of DRS @d2@
---------------------------------------------------------------------------
isSubDRS :: DRS -> DRS -> Bool
isSubDRS d1 (LambdaDRS _) = False
isSubDRS d1 (Merge d2 d3) = isSubDRS d1 d2 || isSubDRS d1 d3
isSubDRS d1 d2@(DRS _ c)  = d1 == d2 || any subDRS c
  where subDRS :: DRSCon -> Bool
        subDRS (Rel _ _)    = False
        subDRS (Neg d3)     = isSubDRS d1 d3
        subDRS (Imp d3 d4)  = isSubDRS d1 d3 || isSubDRS d1 d4
        subDRS (Or d3 d4)   = isSubDRS d1 d3 || isSubDRS d1 d4
        subDRS (Prop _ d3)  = isSubDRS d1 d3
        subDRS (Diamond d3) = isSubDRS d1 d3
        subDRS (Box d3)     = isSubDRS d1 d3

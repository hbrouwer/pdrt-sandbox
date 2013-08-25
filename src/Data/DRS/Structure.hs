-- Structure.hs

{- | 
  Discourse Representation Structure
-}
module Data.DRS.Structure
(
  DRS (..)
, DRSVar
, DRSRel
, DRSRef (..)
, DRSCon (..)
, isSubDRS
) where

-- | Discourse Representation Structure (DRS)
data DRS =
  LambdaDRS (DRSVar,Int)  -- ^ A lambda DRS (with its argument position)
  | Merge DRS DRS         -- ^ A merge between two DRSs
  | DRS [DRSRef] [DRSCon] -- ^ A DRS (a set of referents and a set of conditions)
  deriving (Eq)

-- | DRS variable
type DRSVar = String

-- | DRS relation
type DRSRel = String

-- | DRS referent
data DRSRef =
  LambdaDRSRef (DRSVar, Int) -- ^ A lambda DRS referent (with its argument position)
  | DRSRef DRSVar            -- ^ A DRS referent
  deriving (Eq)

-- | DRS condition
data DRSCon = 
  Rel DRSRel [DRSRef] -- ^ A relation defined on a set of referents
  | Neg DRS           -- ^ A negated DRS
  | Imp DRS DRS       -- ^ An implication between two DRSs
  | Or DRS DRS        -- ^ A disjunction between two DRSs
  | Prop DRSRef DRS   -- ^ A proposition DRS
  | Diamond DRS       -- ^ A possible DRS
  | Box DRS           -- ^ A necessary DRS
  deriving (Eq)

-- Returns whether DRS @d1@ is a direct sub-DRS of DRS @d2@
isSubDRS :: DRS -> DRS -> Bool
isSubDRS d1 (LambdaDRS _) = False
isSubDRS d1 (Merge d2 d3) = d2 == d1 || d3 == d1
isSubDRS d1 (DRS _ c)     = or $ map subDRS c
  where subDRS :: DRSCon -> Bool
        subDRS (Rel _ _)    = False
        subDRS (Neg d3)     = d3 == d1
        subDRS (Imp d3 d4)  = d3 == d1 || d4 == d1
        subDRS (Or d3 d4)   = d3 == d1 || d4 == d1
        subDRS (Prop _ d3)  = d3 == d1
        subDRS (Diamond d3) = d3 == d1
        subDRS (Box d3)     = d3 == d1
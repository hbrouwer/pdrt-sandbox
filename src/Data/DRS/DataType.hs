{- |
Module      :  Data.DRS.DataType
Copyright   :  (c) Harm Brouwer and Noortje Venhuizen
License     :  Apache-2.0

Maintainer  :  me@hbrouwer.eu, n.j.venhuizen@rug.nl
Stability   :  provisional
Portability :  portable

DRS data type
-}

module Data.DRS.DataType
(
  DRS (..)
, DRSVar
, DRSRel (..)
, DRSRef (..)
, DRSCon (..)
) where

---------------------------------------------------------------------------
-- * Exported
---------------------------------------------------------------------------

---------------------------------------------------------------------------
-- | Discourse Representation Structure (DRS)
---------------------------------------------------------------------------
data DRS =
  LambdaDRS ((DRSVar,[DRSVar]),Int)
  -- ^ A lambda DRS (a variable, the set of referents
  -- to be applied to the DRS, and its argument position)
  | Merge DRS DRS
  -- ^ A merge between two DRSs
  | DRS [DRSRef] [DRSCon]
  -- ^ A DRS (a set of referents and a set of conditions)
  deriving (Eq)

---------------------------------------------------------------------------
-- | DRS variable
---------------------------------------------------------------------------
type DRSVar = String

---------------------------------------------------------------------------
-- | DRS referent
---------------------------------------------------------------------------
data DRSRef =
  LambdaDRSRef ((DRSVar,[DRSVar]),Int)
  -- ^ A lambda DRS referent (a variable, the set of referents
  -- to be applied to the referent, and its argument position)
  | DRSRef DRSVar
  -- ^ A DRS referent
  deriving (Eq,Show)

---------------------------------------------------------------------------
-- | DRS relation
---------------------------------------------------------------------------
data DRSRel =
  LambdaDRSRel ((DRSVar,[DRSVar]),Int)
  | DRSRel String
  deriving (Eq,Show)

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

{- |
Module      :  Data.PDRS.DataType
Copyright   :  (c) Harm Brouwer and Noortje Venhuizen
License     :  Apache-2.0

Maintainer  :  me@hbrouwer.eu, n.j.venhuizen@rug.nl
Stability   :  provisional
Portability :  portable

PDRS data type
-}

module Data.PDRS.DataType
(
  PDRS (..)
, DRSVar
, PVar
, MAP
, PRef (..)
, PDRSRef (..)
, PDRSRel (..)
, PCon (..)
, PDRSCon (..)
, DRSRel
) where

import Data.DRS.DataType (DRSRel, DRSVar)

---------------------------------------------------------------------------
-- * Exported
---------------------------------------------------------------------------

---------------------------------------------------------------------------
-- | Projective Discourse Representation Structure.
---------------------------------------------------------------------------
data PDRS =
  LambdaPDRS ((DRSVar,[DRSVar]),Int)
  -- ^ A lambda 'PDRS' (a variable, the set of referents
  -- to be applied to the PDRS, and its argument position)
  | AMerge PDRS PDRS
  -- ^ An assertive merge between two 'PDRS's
  | PMerge PDRS PDRS
  -- ^ A projective merge between two 'PDRS's
  | PDRS PVar [MAP] [PRef] [PCon]
  -- ^ A 'PDRS', consisting of a 'PVar' (a label), 
  -- a set of 'MAP's, a set of 'PRef's, and a set of 'PCon's
  deriving (Eq,Read)

---------------------------------------------------------------------------
-- | Projection variable (a label or pointer).
---------------------------------------------------------------------------
type PVar = Int

---------------------------------------------------------------------------
-- | Minimally Accessible 'PDRS', represented as a tuple between a 'PVar'
-- and another 'PVar' that is /minimally accessible/ from the first 'PVar'.
---------------------------------------------------------------------------
type MAP = (PVar,PVar)

---------------------------------------------------------------------------
-- | A projected referent, consisting of a 'PVar' and a 'PDRSRef'.
---------------------------------------------------------------------------
data PRef = PRef PVar PDRSRef
  deriving (Eq,Read,Show)

---------------------------------------------------------------------------
-- | A 'PDRS' referent.
---------------------------------------------------------------------------
data PDRSRef =
  LambdaPDRSRef ((DRSVar,[DRSVar]),Int)
  -- ^ A lambda PDRS referent (a variable, the set of referents
  -- to be applied to the referent, and its argument position)
  | PDRSRef DRSVar
  -- ^ A PDRS referent
  deriving (Eq,Read,Show)

---------------------------------------------------------------------------
-- | PDRS relation
---------------------------------------------------------------------------
data PDRSRel =
  LambdaPDRSRel ((DRSVar,[DRSVar]),Int)
  | PDRSRel String
  deriving (Eq,Read,Show)

---------------------------------------------------------------------------
-- | A projected condition, consisting of a 'PVar' and a 'PDRSCon'.
---------------------------------------------------------------------------
data PCon = PCon PVar PDRSCon
  deriving (Eq,Read)

---------------------------------------------------------------------------
-- | A 'PDRS' condition.
---------------------------------------------------------------------------
data PDRSCon = 
  Rel PDRSRel [PDRSRef] -- ^ A relation defined on a set of referents
  | Neg PDRS            -- ^ A negated 'PDRS'
  | Imp PDRS PDRS       -- ^ An implication between two 'PDRS's
  | Or PDRS PDRS        -- ^ A disjunction between two 'PDRS's
  | Prop PDRSRef PDRS   -- ^ A proposition 'PDRS'
  | Diamond PDRS        -- ^ A possible 'PDRS'
  | Box PDRS            -- ^ A necessary 'PDRS'
  deriving (Eq,Read)

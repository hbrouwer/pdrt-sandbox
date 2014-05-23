{- |
Module      :  Data.DRS.Structure
Copyright   :  (c) Harm Brouwer and Noortje Venhuizen
License     :  Apache-2.0

Maintainer  :  me@hbrouwer.eu, n.j.venhuizen@rug.nl
Stability   :  provisional
Portability :  portable

Structural operations on DRSs
-}

module Data.DRS.Structure
(
  drsUniverse
, isLambdaDRS
, isMergeDRS
, isResolvedDRS
, isSubDRS
) where

import Data.DRS.DataType
import Data.List (union)

---------------------------------------------------------------------------
-- * Exported
---------------------------------------------------------------------------

---------------------------------------------------------------------------
-- | Returns the universe of a DRS
---------------------------------------------------------------------------
drsUniverse :: DRS -> [DRSRef]
drsUniverse (LambdaDRS _) = []
drsUniverse (Merge d1 d2) = drsUniverse d1 `union` drsUniverse d2
drsUniverse (DRS u _)     = u

---------------------------------------------------------------------------
-- | Returns whether a 'DRS' is entirely a 'LambdaDRS' (at its top-level).
---------------------------------------------------------------------------
isLambdaDRS :: DRS -> Bool
isLambdaDRS (LambdaDRS _) = True
isLambdaDRS (Merge d1 d2) = isLambdaDRS d1 && isLambdaDRS d2
isLambdaDRS (DRS _ _)     = False

---------------------------------------------------------------------------
-- | Returns whether a 'DRS' is entirely a 'Merge' (at its top-level).
---------------------------------------------------------------------------
isMergeDRS :: DRS -> Bool
isMergeDRS (LambdaDRS _) = False
isMergeDRS (Merge _ _)   = True
isMergeDRS (DRS _ _)     = False

---------------------------------------------------------------------------
-- | Returns whether a 'DRS' is resolved (containing no unresolved merges 
-- or lambdas)
---------------------------------------------------------------------------
isResolvedDRS :: DRS -> Bool
isResolvedDRS (LambdaDRS _) = False
isResolvedDRS (Merge _ _)   = False
isResolvedDRS (DRS u c)     = all isResolvedRef u && all isResolvedCon c
  where isResolvedRef :: DRSRef -> Bool
        isResolvedRef (LambdaDRSRef _) = False
        isResolvedRef (DRSRef _)       = True
        isResolvedCon :: DRSCon -> Bool
        isResolvedCon (Rel _ d)    = all isResolvedRef d
        isResolvedCon (Neg d1)     = isResolvedDRS d1
        isResolvedCon (Imp d1 d2)  = isResolvedDRS d1 && isResolvedDRS d2
        isResolvedCon (Or d1 d2)   = isResolvedDRS d1 && isResolvedDRS d2
        isResolvedCon (Prop r d1)  = isResolvedRef r  && isResolvedDRS d1
        isResolvedCon (Diamond d1) = isResolvedDRS d1
        isResolvedCon (Box d1)     = isResolvedDRS d1

---------------------------------------------------------------------------
-- | Returns whether DRS @d1@ is a direct or indirect sub-DRS of DRS @d2@
---------------------------------------------------------------------------
isSubDRS :: DRS -> DRS -> Bool
isSubDRS _  (LambdaDRS _) = False
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

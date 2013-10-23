{- |
Module      :  Data.DRS.Merge
Copyright   :  (c) Harm Brouwer and Noortje Venhuizen
License     :  Apache-2.0

Maintainer  :  me@hbrouwer.eu, n.j.venhuizen@rug.nl
Stability   :  provisional
Portability :  portable

DRS merge
-}

module Data.DRS.Merge 
(
  drsMerge
, (<<+>>)
, drsResolveMerges
) where

import Data.DRS.LambdaCalculus
import Data.DRS.Properties
import Data.DRS.Structure
import Data.DRS.Variables

import Data.List (intersect, union)

---------------------------------------------------------------------------
-- * Exported
---------------------------------------------------------------------------

---------------------------------------------------------------------------
-- | Applies merge to 'DRS' @d1@ and 'DRS' @d2@.
---------------------------------------------------------------------------
drsMerge :: DRS -> DRS -> DRS
drsMerge d1 d2 = merge rd1 (rename rd1 (drsVariables rd2))
  where rd1 = drsPurify $ drsResolveMerges d1
        rd2 = drsPurify $ drsResolveMerges d2
        merge :: DRS -> DRS -> DRS
        merge (DRS u1 c1) (DRS u2 c2) = DRS (u1 `union` u2) (c1 `union` c2)
        -- | Replace all occurrences of 'DRSRef's from @rs@ 
        -- in 'DRS' @d@ by new 'DRSRef's.
        rename :: DRS -> [DRSRef] -> DRS
        rename d rs = drsAlphaConvert d2 (zip ors nrs)
          where ors = drsVariables d `intersect` rs
                nrs = newDRSRefs ors (drsVariables d `union` rs)

-- | Infix notation for 'drsMerge'.
(<<+>>) :: DRS -> DRS ->DRS
d1 <<+>> d2 = d1 `drsMerge` d2

---------------------------------------------------------------------------
-- | Resolves all unresolved merges in a 'DRS'.
---------------------------------------------------------------------------
drsResolveMerges :: DRS -> DRS
drsResolveMerges ld@(LambdaDRS _) = ld
drsResolveMerges (Merge d1 d2)
  | isLambdaDRS d1 || isLambdaDRS d2 = Merge d1 d2
  | otherwise                        = d1 <<+>> d2
drsResolveMerges (DRS u c)        = DRS u (map resolve c)
  where resolve :: DRSCon -> DRSCon
        resolve r@(Rel _ _)  = r
        resolve (Neg d1)     = Neg     (drsResolveMerges d1)
        resolve (Imp d1 d2)  = Imp     (drsResolveMerges d1) (drsResolveMerges d2)
        resolve (Or d1 d2)   = Or      (drsResolveMerges d1) (drsResolveMerges d2)
        resolve (Prop r d1)  = Prop r  (drsResolveMerges d1)
        resolve (Diamond d1) = Diamond (drsResolveMerges d1)
        resolve (Box d1)     = Box     (drsResolveMerges d1)




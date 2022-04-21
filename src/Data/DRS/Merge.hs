{-# OPTIONS_GHC -Wno-incomplete-uni-patterns #-}
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
, drsCombine
, (<<&>>)
, drsResolveMerges
) where

import Data.DRS.DataType
import Data.DRS.LambdaCalculus
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
drsMerge d ld@(LambdaDRS _) = Merge d ld
drsMerge ld@(LambdaDRS _) d = Merge ld d
drsMerge d md@(Merge d1 d2)
  | isLambdaDRS d1 = Merge d1 (drsMerge d d2)                                 -- d + (ld1 + d2) = ld1 + (d + d2)
  | isLambdaDRS d2 = Merge (drsMerge d d1) d2                                 -- d + (d1 + ld2) = (d + d1) + ld2
  | otherwise      = drsMerge d (drsResolveMerges md)
drsMerge md@(Merge d1 d2) d
  | isLambdaDRS d1 = Merge d1 (drsMerge d2 d)                                 -- (ld1 + d2) + d = ld1 + (d2 + d)
  | isLambdaDRS d2 = Merge d2 (drsMerge d1 d)                                 -- (d1 + ld2) + d = ld2 + (d1 + d)
  | otherwise      = drsMerge (drsResolveMerges md) d
drsMerge d@(DRS _ _) d'@(DRS _ _) = DRS (u1 `union` u2) (c1 `union` c2)
  where d1@(DRS u1 c1) = drsPurify $ drsResolveMerges d
        (DRS u2 c2)    = drsAlphaConvert d'' (zip ors nrs)
        d'' = drsPurify $ drsResolveMerges d'
        ors = drsVariables d'' `intersect` drsVariables d1
        nrs = newDRSRefs ors (drsVariables d'' `union` drsVariables d1)

-- | Infix notation for 'drsMerge'.
(<<+>>) :: DRS -> DRS ->DRS
d1 <<+>> d2 = d1 `drsMerge` d2

---------------------------------------------------------------------------
-- | Combines an unresolved 'DRS' and a 'DRS' into a resolved 'DRS'.
---------------------------------------------------------------------------

drsCombine :: ((DRSRef -> DRS) -> DRS) -> DRS -> DRS
drsCombine ud d = drsResolveMerges (ud (const d))

-- | Infix notation for 'drsCombine'.
(<<&>>) ::  ((DRSRef -> DRS) -> DRS) -> DRS -> DRS
ud <<&>> d = ud `drsCombine` d

---------------------------------------------------------------------------
-- | Resolves all unresolved merges in a 'DRS'.
---------------------------------------------------------------------------
drsResolveMerges :: DRS -> DRS
drsResolveMerges ld@(LambdaDRS _) = ld
drsResolveMerges (Merge d1 d2)    = drsResolveMerges d1 <<+>> drsResolveMerges d2
drsResolveMerges (DRS u c)        = DRS u (map resolve c)
  where resolve :: DRSCon -> DRSCon
        resolve r@(Rel _ _)  = r
        resolve (Neg d1)     = Neg     (drsResolveMerges d1)
        resolve (Imp d1 d2)  = Imp     (drsResolveMerges d1) (drsResolveMerges d2)
        resolve (Or d1 d2)   = Or      (drsResolveMerges d1) (drsResolveMerges d2)
        resolve (Prop r d1)  = Prop r  (drsResolveMerges d1)
        resolve (Diamond d1) = Diamond (drsResolveMerges d1)
        resolve (Box d1)     = Box     (drsResolveMerges d1)

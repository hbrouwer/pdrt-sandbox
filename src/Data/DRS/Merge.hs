{- |
Module      :  Data.DRS.Merge
Copyright   :  (c) Harm Brouwer and Noortje Venhuizen
License     :  Apache-2.0

Maintainer  :  me@hbrouwer.eu
Stability   :  provisional
Portability :  portable

DRS merge
-}

module Data.DRS.Merge 
(
  drsMerge
, (<<+>>)
, drsResolveMerges
, newDRSRefs
) where

import Data.DRS.AlphaConversion
import Data.DRS.Properties
import Data.DRS.Structure
import Data.DRS.Variables

import Data.List (intersect, union)

-- | Merges DRS @d1@ with DRS @d2@
drsMerge :: DRS -> DRS -> DRS
drsMerge d1 d2 = merge rd1 (drsDisjoin rd1 rd2)
  where rd1 = drsResolveMerges d1
        rd2 = drsResolveMerges d2
        merge :: DRS -> DRS -> DRS
        merge (DRS u1 c1) (DRS u2 c2) = DRS (u1 `union` u2) (c1 `union` c2)

-- | Infix notation for 'drsMerge'
(<<+>>) :: DRS -> DRS ->DRS
d1 <<+>> d2 = d1 `drsMerge` d2

-- | Resolves all unresolved merges in a DRS
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

-- | Disjoins DRS @d2@ from DRS @d1@ by alpha converting overlapping bound 
-- referents to new referents
drsDisjoin :: DRS -> DRS -> DRS
drsDisjoin d1 d2 = drsAlphaConvert d2 (zip ors nrs)
  where ors = drsVariables d1 `intersect` drsReferents d2
        nrs = newDRSRefs ors (drsReferents d1 `union` drsReferents d2)

-- | Returns a list of new referents, based on a list of old referents and a 
-- list of existing referents
newDRSRefs :: [DRSRef] -> [DRSRef] -> [DRSRef]
newDRSRefs [] _        = []
newDRSRefs (r:rs) refs = nr : newDRSRefs rs (nr:refs)
  where nr = newRef 0
        newRef :: Int -> DRSRef
        newRef n
          | r' `elem` refs = newRef (n + 1)
          | otherwise      = r'
          where r' =
                  case r of
                   (LambdaDRSRef (dv,lp)) -> LambdaDRSRef (dv ++ show n, lp)
                   (DRSRef dv)            -> DRSRef       (dv ++ show n)

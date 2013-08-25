-- Merge.hs

{- |
  DRS Merge
-}
module Data.DRS.Merge 
(
  drsMerge
, (<<+>>)
, newDRSRefs
) where

import Data.DRS.AlphaConversion
import Data.DRS.Structure
import Data.DRS.Variables

import Data.List (intersect, union)

-- | Merges DRS @d1@ with DRS @d2@
drsMerge :: DRS -> DRS -> DRS
drsMerge d1 d2 = merge' d1 (drsDisjoin d1 d2)
  where merge' :: DRS -> DRS -> DRS
        merge' (DRS u1 c1) (DRS u2 c2) = DRS (u1 `union` u2) (c1 `union` c2)

-- | Infix notation for 'drsMerge'
(<<+>>) :: DRS -> DRS ->DRS
d1 <<+>> d2 = d1 `drsMerge` d2

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
  where nr = (newRef 0)
        newRef :: Int -> DRSRef
        newRef n
          | elem r' refs = newRef (n + 1)
          | otherwise    = r'
          where r' =
                  case r of
                   (LambdaDRSRef (dv,lp)) -> LambdaDRSRef (dv ++ show n, lp)
                   (DRSRef dv)            -> DRSRef       (dv ++ show n)

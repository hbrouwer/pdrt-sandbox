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
, drsDisjoin
, drsToCleanDRS
) where

import Data.DRS.LambdaCalculus
import Data.DRS.Properties
import Data.DRS.Structure
import Data.DRS.Variables

import Data.List (intersect, union)

-- | Merges DRS @d1@ with DRS @d2@
drsMerge :: DRS -> DRS -> DRS
drsMerge d1 d2 = merge rd1 (drsDisjoin rd1 rd2)
  where rd1 = drsToCleanDRS $ drsResolveMerges d1
        rd2 = drsToCleanDRS $ drsResolveMerges d2
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
  where ors = drsVariables d1 `intersect` drsUniverses d2
        nrs = newDRSRefs ors (drsUniverses d1 `union` drsUniverses d2)

drsToCleanDRS :: DRS -> DRS
drsToCleanDRS gdrs = fst $ cleanRefs (gdrs,[]) gdrs

cleanRefs :: (DRS,[DRSRef]) -> DRS -> (DRS,[DRSRef])
cleanRefs (ld@(LambdaDRS _),rs) _  = (ld,rs)
cleanRefs (Merge d1 d2,rs)      gd = (Merge cd1 cd2,rs2)
  where (cd1,rs1) = cleanRefs (d1,rs)  gd
        (cd2,rs2) = cleanRefs (d2,rs1) gd
cleanRefs (d@(DRS u _),rs)      gd = (DRS u1 c2,rs1)
  where (DRS u1 c1) = drsAlphaConvert d (zip ors (newDRSRefs ors (drsVariables gd)))
        (c2,rs1)    = clean (c1,rs ++ u1)
        ors         = u `intersect` rs
        clean :: ([DRSCon],[DRSRef]) -> ([DRSCon],[DRSRef])
        clean ([],rs)             = ([],rs)
        clean (c@(Rel _ d):cs,rs) = (c:ccs,rs1)
          where (ccs,rs1) = clean (cs,rs ++ d)
        clean (Neg d1:cs,rs)      = (Neg cd1:ccs,rs2)
          where (cd1,rs1) = cleanRefs (d1,rs) gd
                (ccs,rs2) = clean (cs,rs2)
        clean (Imp d1 d2:cs,rs)   = (Imp cd1 cd2:ccs,rs3)
          where (cd1,rs1) = cleanRefs (alphaConvertSubDRS d1 gd nrs,rs)  gd
                (cd2,rs2) = cleanRefs (alphaConvertSubDRS d2 gd nrs,rs1) gd
                (ccs,rs3) = clean (cs,rs2)
                nrs = zip ors (newDRSRefs ors (drsVariables gd `union` drsVariables d))
                ors = drsUniverse d1 `intersect` rs
        clean (Or d1 d2:cs,rs)    = (Or cd1 cd2:ccs,rs3)
          where (cd1,rs1) = cleanRefs (alphaConvertSubDRS d1 gd nrs,rs)  gd
                (cd2,rs2) = cleanRefs (alphaConvertSubDRS d2 gd nrs,rs1) gd
                (ccs,rs3) = clean (cs,rs2)
                nrs = zip ors (newDRSRefs ors (drsVariables gd `union` drsVariables d))
                ors = drsUniverse d1 `intersect` rs
        clean (Prop r d1:cs,rs)   = (Prop r cd1:ccs,rs2)
          where (cd1,rs1) = cleanRefs (d1,r:rs) gd
                (ccs,rs2) = clean (cs,rs2)
        clean (Diamond d1:cs,rs)  = (Diamond cd1:ccs,rs2)
          where (cd1,rs1) = cleanRefs (d1,rs) gd
                (ccs,rs2) = clean (cs,rs2)
        clean (Box d1:cs,rs)      = (Box cd1:ccs,rs2)
          where (cd1,rs1) = cleanRefs (d1,rs) gd
                (ccs,rs2) = clean (cs,rs2)

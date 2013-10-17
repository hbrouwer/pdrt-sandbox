{- |
Module      :  Data.DRS.Translate
Copyright   :  (c) Harm Brouwer and Noortje Venhuizen
License     :  Apache-2.0

Maintainer  :  me@hbrouwer.eu
Stability   :  provisional
Portability :  portable

DRS to FOL translation
-}

module Data.DRS.Translate
(
  drsToFOL
, drsToCleanDRS
) where

import Data.DRS.LambdaCalculus
import Data.DRS.Structure
import Data.DRS.Variables
import qualified Data.FOL as F

import Data.List (intersect, union)

-- | Constants
worldVar = "w"   -- World variable
worldRel = "Acc" -- Accessibility relation between worlds

-- | Converts a DRS @d@ to a FOL formula
drsToFOL :: DRS -> F.FOLForm
drsToFOL d = drsToMFOL d worldVar

-- | Converts a DRS to a modal FOL formula with world @w@
drsToMFOL :: DRS -> F.FOLVar -> F.FOLForm
drsToMFOL (DRS [] c) w     = drsConsToMFOL c w
drsToMFOL (DRS (r:rs) c) w = F.Exists (drsRefToDRSVar r) (drsToMFOL (DRS rs c) w)

-- | Converts a list of DRS conditions to a modal FOL formula with world @w@
drsConsToMFOL :: [DRSCon] -> F.FOLVar -> F.FOLForm
drsConsToMFOL [] _              = F.Top
drsConsToMFOL (Rel r d:[]) w    = F.Rel r (w : map drsRefToDRSVar d)
drsConsToMFOL (Neg d1:[]) w     = F.Neg (drsToMFOL d1 w)
drsConsToMFOL (Imp d1 d2:[]) w  = quantifyForAll d1
  where quantifyForAll :: DRS -> F.FOLForm
        quantifyForAll (DRS [] c)     = F.Imp    (drsConsToMFOL c w) (drsToMFOL d2 w)
        quantifyForAll (DRS (r:rs) c) = F.ForAll (drsRefToDRSVar r)  (quantifyForAll (DRS rs c))
drsConsToMFOL (Or d1 d2:[]) w   = F.Or (drsToMFOL d1 w) (drsToMFOL d2 w)
drsConsToMFOL (Prop r d1:[]) w  = F.And (F.Rel worldRel [w,drsRefToDRSVar r]) (drsToMFOL d1 (drsRefToDRSVar r))
drsConsToMFOL (Diamond d1:[]) w = F.Exists v (F.And (F.Rel worldRel [w,v]) (drsToMFOL d1 v))
  where v = w ++ "'"
drsConsToMFOL (Box d1:[]) w     = F.ForAll v (F.Imp (F.Rel worldRel [w,v]) (drsToMFOL d1 v))
  where v = w ++ "'"
drsConsToMFOL (c:cs) w          = F.And (drsConsToMFOL [c] w) (drsConsToMFOL cs w)

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

{-# LANGUAGE FlexibleInstances #-}
{- |
Module      :  Data.DRS.LambdaCalculus
Copyright   :  (c) Harm Brouwer and Noortje Venhuizen
License     :  Apache-2.0

Maintainer  :  me@hbrouwer.eu, n.j.venhuizen@rug.nl
Stability   :  provisional
Portability :  portable

DRS lambda calculus; alpha conversion, beta reduction,
and function composition
-}

module Data.DRS.LambdaCalculus
(
  drsAlphaConvert
, alphaConvertSubDRS
, alphaConvertVar
, drsBetaReduce
, (<<@>>)
, drsFunctionCompose
, (<<.>>)
, drsPurify
) where

import Data.DRS.Structure
import Data.DRS.Variables

import Data.List ((\\), intersect, union)

-- | Applies alpha conversion to a DRS on the basis of a conversion list
-- for DRS referents @rs@
drsAlphaConvert :: DRS -> [(DRSRef,DRSRef)] -> DRS
drsAlphaConvert d = alphaConvertSubDRS d d

-- | Applies alpha conversion to a DRS @sd@, which is a sub-DRS of the global
-- DRS @gd@, on the basis of a conversion list for DRS referents @rs@
alphaConvertSubDRS :: DRS -> DRS -> [(DRSRef,DRSRef)] -> DRS
alphaConvertSubDRS ld@(LambdaDRS _) _ _ = ld
alphaConvertSubDRS (Merge d1 d2) gd rs  = Merge d1' d2'
  where d1' = alphaConvertSubDRS d1 gd rs
        d2' = alphaConvertSubDRS d2 gd rs
alphaConvertSubDRS sd@(DRS u _) gd rs    = DRS u' c'
  where u' = alphaConvertRefs u rs
        c' = alphaConvertCons sd gd rs

-- | Applies alpha conversion to a list of DRS referents @u@, on the basis
-- of a conversion list @rs@
alphaConvertRefs :: [DRSRef] -> [(DRSRef,DRSRef)] -> [DRSRef]
alphaConvertRefs u rs = map (`alphaConvertVar` rs) u

-- | Applies alpha conversion to a variable @v@, iff @v@ occurs in
-- a variable conversion list. Otherwise, @v@ is returned unmodified
alphaConvertVar :: (Eq a) => a -> [(a,a)] -> a
alphaConvertVar v [] = v
alphaConvertVar v ((cv,cv'):cvs)
  | v == cv   = cv'
  | otherwise = alphaConvertVar v cvs

-- | Applies alpha conversion to the conditions in a DRS @sd@, which
-- is a sub-DRS of @gd@, on the basis of a conversion list for DRS
-- referents @rs@
alphaConvertCons :: DRS -> DRS -> [(DRSRef,DRSRef)] -> [DRSCon]
alphaConvertCons ld@(DRS _ c) gd rs = map convertCon c
  where convertCon :: DRSCon -> DRSCon
        convertCon (Rel r d)    = Rel r   (map convertRef d)
        convertCon (Neg d1)     = Neg     (alphaConvertSubDRS d1 gd rs)
        convertCon (Imp d1 d2)  = Imp     (alphaConvertSubDRS d1 gd rs) (alphaConvertSubDRS d2 gd rs)
        convertCon (Or d1 d2)   = Or      (alphaConvertSubDRS d1 gd rs) (alphaConvertSubDRS d2 gd rs)
        convertCon (Prop r d1)  = Prop    (convertRef r)                (alphaConvertSubDRS d1 gd rs)
        convertCon (Diamond d1) = Diamond (alphaConvertSubDRS d1 gd rs)
        convertCon (Box d1)     = Box     (alphaConvertSubDRS d1 gd rs)
        convertRef :: DRSRef -> DRSRef
        convertRef r
          | drsBoundRef r ld gd = alphaConvertVar r rs
          | otherwise           = r

-- | Type class for a DRSAtom, which is either a DRS or a DRSRef
class DRSAtom a
instance DRSAtom DRS
instance DRSAtom DRSRef

-- | Type class for an AbstractDRS, which is either a resolved DRS, or 
-- an unresolved DRS that takes a DRSAtom and yields an AbstractDRS
class AbstractDRS a
instance AbstractDRS DRS
instance (DRSAtom a, AbstractDRS b) => AbstractDRS (a -> b)

-- | Apply beta reduction on an AbstractDRS with a DRSAtom
drsBetaReduce :: (AbstractDRS a, DRSAtom b) => (b -> a) -> b -> a
drsBetaReduce a = a

-- | Infix notation for 'drsBetaReduce'
(<<@>>) :: (AbstractDRS a, DRSAtom b) => (b -> a) -> b -> a
ud <<@>> ad = ud `drsBetaReduce` ad

-- | Apply function composition to two unresolved DRSs, yielding
-- a new unresolved DRS
drsFunctionCompose :: (b -> c) -> (a -> b) -> a -> c
drsFunctionCompose = (.)

-- | Infix notation for 'drsFunctionCompose'
(<<.>>) :: (b -> c) -> (a -> b) -> a -> c
a1 <<.>> a2 = a1 `drsFunctionCompose` a2


drsPurify :: DRS -> DRS
drsPurify gdrs = fst $ purifyRefs (gdrs,drsFreeRefs gdrs gdrs) gdrs

purifyRefs :: (DRS,[DRSRef]) -> DRS -> (DRS,[DRSRef])
purifyRefs (ld@(LambdaDRS _),rs) _  = (ld,rs)
purifyRefs (Merge d1 d2,rs)      gd = (Merge cd1 cd2,rs2)
  where (cd1,rs1) = purifyRefs (d1,rs)  gd
        (cd2,rs2) = purifyRefs (d2,rs1) gd
purifyRefs (ld@(DRS u _),rs)      gd = (DRS u1 c2,rs1)
-- In case we do not want to rename ambiguous bindings:
-- purifyRefs (ld@(DRS u _),rs)      gd = (DRS u1 c2,u1 ++ rs1)
  where (DRS u1 c1) = drsAlphaConvert ld (zip ors (newDRSRefs ors (drsVariables gd `union` rs)))
        ors         = u `intersect` rs
        (c2,rs1)    = purify (c1,u1 ++ rs)
        -- In case we do not want to rename ambiguous bindings:
        --(c2,rs1)    = purify (c1,rs)
        purify :: ([DRSCon],[DRSRef]) -> ([DRSCon],[DRSRef])
        purify ([],rs)             = ([],rs)
        purify (c@(Rel _ d):cs,rs) = (c:ccs,rs1)
          where (ccs,rs1) = purify (cs,rs ++ d)        
        purify (Neg d1:cs,rs)      = (Neg cd1:ccs,rs2)
          where (cd1,rs1) = purifyRefs (d1,rs) gd
                (ccs,rs2) = purify (cs,rs1)
        purify (Imp d1 d2:cs,rs)   = (Imp cd1 cd2:ccs,rs3)
          where (cd1,rs1) = purifyRefs (alphaConvertSubDRS d1 gd nrs,rs)  gd
                (cd2,rs2) = purifyRefs (alphaConvertSubDRS d2 gd nrs,rs1) gd
                (ccs,rs3) = purify (cs,rs2)
                nrs = zip ors (newDRSRefs ors (drsVariables gd `union` rs))
                ors = drsUniverse d1 `intersect` rs
                -- In case we do not want to rename ambiguous bindings:
                -- ors = drsUniverses d2 \\ drsUniverse d1 `intersect` rs
        purify (Or d1 d2:cs,rs)    = (Or cd1 cd2:ccs,rs3)
          where (cd1,rs1) = purifyRefs (alphaConvertSubDRS d1 gd nrs,rs)  gd
                (cd2,rs2) = purifyRefs (alphaConvertSubDRS d2 gd nrs,rs1) gd
                (ccs,rs3) = purify (cs,rs2)
                nrs = zip ors (newDRSRefs ors (drsVariables gd `union` rs))
                ors = drsUniverse d1 `intersect` rs
                -- In case we do not want to rename ambiguous bindings:
                -- ors = drsUniverses d2 \\ drsUniverse d1 `intersect` rs
        purify (Prop r d1:cs,rs)   = (Prop r cd1:ccs,rs2)
          where (cd1,rs1) = purifyRefs (d1,r:rs) gd
                (ccs,rs2) = purify (cs,rs1)
        purify (Diamond d1:cs,rs)  = (Diamond cd1:ccs,rs2)
          where (cd1,rs1) = purifyRefs (d1,rs) gd
                (ccs,rs2) = purify (cs,rs1)
        purify (Box d1:cs,rs)      = (Box cd1:ccs,rs2)
          where (cd1,rs1) = purifyRefs (d1,rs) gd
                (ccs,rs2) = purify (cs,rs1)

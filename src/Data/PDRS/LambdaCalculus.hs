{- |
Module      :  Data.PDRS.LambdaCalculus
Copyright   :  (c) Harm Brouwer and Noortje Venhuizen
License     :  Apache-2.0

Maintainer  :  me@hbrouwer.eu
Stability   :  provisional
Portability :  portable

PDRS lambda calculus; alpha conversion, beta reduction,
and function composition
-}

module Data.PDRS.LambdaCalculus
(
  pdrsAlphaConvert
, pdrsBetaReduce
, (<<@>>)
, pdrsFunctionCompose
, (<<.>>)  
) where

import Data.DRS.LambdaCalculus (alphaConvertVar)
import Data.PDRS.Structure
import Data.PDRS.Variables

-- | Applies alpha conversion to a PDRS on the basis of conversion lists
-- for projection variables and PDRS referents
pdrsAlphaConvert :: PDRS -> [(PVar,PVar)] -> [(PDRSRef,PDRSRef)] -> PDRS
pdrsAlphaConvert p = alphaConvertSubPDRS p p

-- | Applies alpha conversion to a PDRS @sp@, which is a sub-PDRS of the
-- global PDRS @gp@, on the basis of conversion lists for projection
-- variables @ps@ and PDRS referents @rs@
alphaConvertSubPDRS :: PDRS -> PDRS -> [(PVar,PVar)] -> [(PDRSRef,PDRSRef)] -> PDRS
alphaConvertSubPDRS lp@(LambdaPDRS _) _ _ _ = lp
alphaConvertSubPDRS (AMerge p1 p2) gp ps rs = AMerge p1' p2'
  where p1' = alphaConvertSubPDRS p1 gp ps rs
        p2' = alphaConvertSubPDRS p2 gp ps rs
alphaConvertSubPDRS (PMerge p1 p2) gp ps rs = PMerge p1' p2'
  where p1' = alphaConvertSubPDRS p1 gp ps rs
        p2' = alphaConvertSubPDRS p2 gp ps rs
alphaConvertSubPDRS (PDRS l m u c) gp ps rs = PDRS l' m' u' c'
  where l' = alphaConvertVar l ps
        m' = alphaConvertMAPs m ps
        u' = alphaConvertPRefs u ps rs
        c' = alphaConvertPCons c gp ps rs

-- | Applies alpha conversion to a list of minimally accessible PDRSs @m@,
-- on the basis of a conversion list for projection variables @ps@
alphaConvertMAPs :: [(PVar,PVar)] -> [(PVar,PVar)] -> [(PVar,PVar)]
alphaConvertMAPs m ps = map (\(l1,l2) -> (alphaConvertVar l1 ps, alphaConvertVar l2 ps)) m

-- | Applies alpha conversion to a list of projected referents @u@, on the
-- basis of a conversion list for projection variables @ps@ and PDRS
-- referents @rs@
alphaConvertPRefs :: [PRef] -> [(PVar,PVar)] -> [(PDRSRef,PDRSRef)] -> [PRef]
alphaConvertPRefs u ps rs = map (\(PRef p r) -> PRef (alphaConvertVar p ps) (alphaConvertVar r rs)) u

-- | Applies alpha conversion to a list of projected conditions @c@ in
-- a global PDRS @gp@, on the basis of a conversion list for projection
-- variables @ps@ and PDRS referents @rs@
alphaConvertPCons :: [PCon] -> PDRS -> [(PVar,PVar)] -> [(PDRSRef,PDRSRef)] -> [PCon]
alphaConvertPCons c gp ps rs = map convertPCon c
  where convertPCon :: PCon -> PCon
        convertPCon (PCon p (Rel r d))    = PCon (alphaConvertVar p ps) (Rel     r (map (convertRef p) d))
        convertPCon (PCon p (Neg p1))     = PCon (alphaConvertVar p ps) (Neg     (alphaConvertSubPDRS p1 gp ps rs))
        convertPCon (PCon p (Imp p1 p2))  = PCon (alphaConvertVar p ps) (Imp     (alphaConvertSubPDRS p1 gp ps rs) (alphaConvertSubPDRS p2 gp ps rs))
        convertPCon (PCon p (Or p1 p2))   = PCon (alphaConvertVar p ps) (Or      (alphaConvertSubPDRS p1 gp ps rs) (alphaConvertSubPDRS p2 gp ps rs))
        convertPCon (PCon p (Prop r p1))  = PCon (alphaConvertVar p ps) (Prop    (convertRef p r)                  (alphaConvertSubPDRS p1 gp ps rs))
        convertPCon (PCon p (Diamond p1)) = PCon (alphaConvertVar p ps) (Diamond (alphaConvertSubPDRS p1 gp ps rs))
        convertPCon (PCon p (Box  p1))    = PCon (alphaConvertVar p ps) (Box     (alphaConvertSubPDRS p1 gp ps rs))
        convertRef :: PVar -> PDRSRef -> PDRSRef
        convertRef p r
          | pdrsBoundRef (PRef p r) gp = alphaConvertVar r rs
          | otherwise                  = r

-- | Type class for a PDRSAtom, which is either a PDRS or a PDRSRef
class PDRSAtom a
instance PDRSAtom PDRS
instance PDRSAtom PDRSRef

-- | Type class for an AbstractPDRS, which is either a resolved PDRS, or
-- an unresolved PDRS that takes a PDRSAtom and yields an AbstractPDRS
class AbstractPDRS a
instance AbstractPDRS PDRS
instance (PDRSAtom a, AbstractPDRS b) => AbstractPDRS (a -> b)

-- | Apply beta reduction on an AbstractPDRS with a PDRSAtom
pdrsBetaReduce :: (AbstractPDRS a, PDRSAtom b) => (b -> a) -> b -> a
pdrsBetaReduce a = a

-- | Infix notation for 'drsBetaReduce'
(<<@>>) :: (AbstractPDRS a, PDRSAtom b) => (b -> a) -> b -> a
up <<@>> ap = up `pdrsBetaReduce` ap

-- | Apply function composition to two unresolved PDRSs, yielding
-- a new unresolved PDRS
pdrsFunctionCompose :: (b -> c) -> (a -> b) -> a -> c
pdrsFunctionCompose = (.)

-- | Infix notation for 'pdrsFunctionCompose'
(<<.>>) :: (b -> c) -> (a -> b) -> a -> c
a1 <<.>> a2 = a1 `pdrsFunctionCompose` a2

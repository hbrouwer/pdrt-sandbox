{- |
Module      :  Data.PDRS.AlphaConversion
Copyright   :  (c) Harm Brouwer and Noortje Venhuizen
License     :  Apache-2.0

Maintainer  :  me@hbrouwer.eu
Stability   :  provisional
Portability :  portable

PDRS alpha conversion
-}

module Data.PDRS.AlphaConversion
(
  pdrsAlphaConvert
) where

import Data.DRS.AlphaConversion (alphaConvertVar)
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

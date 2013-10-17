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
, alphaConvertSubPDRS
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
alphaConvertSubPDRS lp@(LambdaPDRS _) _ _ _    = lp
alphaConvertSubPDRS (AMerge p1 p2) gp ps rs    = AMerge p1' p2'
  where p1' = alphaConvertSubPDRS p1 gp ps rs
        p2' = alphaConvertSubPDRS p2 gp ps rs
alphaConvertSubPDRS (PMerge p1 p2) gp ps rs    = PMerge p1' p2'
  where p1' = alphaConvertSubPDRS p1 gp ps rs
        p2' = alphaConvertSubPDRS p2 gp ps rs
alphaConvertSubPDRS lp@(PDRS l m u c) gp ps rs = PDRS l' m' u' c'
  where l' = alphaConvertVar l ps
        m' = alphaConvertMAPs m lp gp ps
        u' = alphaConvertPRefs u lp gp ps rs
        c' = alphaConvertPCons c lp gp ps rs

alphaConvertMAPs :: [(PVar,PVar)] -> PDRS -> PDRS -> [(PVar,PVar)] -> [(PVar,PVar)]
alphaConvertMAPs m lp gp ps = map (\(l1,l2) -> (convertPVar l1 lp gp ps, convertPVar l2 lp gp ps)) m

alphaConvertPRefs :: [PRef] -> PDRS -> PDRS -> [(PVar,PVar)] -> [(PDRSRef,PDRSRef)] -> [PRef]
alphaConvertPRefs u lp gp ps rs = map (\(PRef p r) -> PRef (convertPVar p lp gp ps) (alphaConvertVar r rs)) u

alphaConvertPCons :: [PCon] -> PDRS -> PDRS -> [(PVar,PVar)] -> [(PDRSRef,PDRSRef)] -> [PCon]
alphaConvertPCons c lp gp ps rs = map convertPCon c
  where convertPCon :: PCon -> PCon
        convertPCon (PCon p (Rel r d))    = PCon p'                       (Rel     r (map (flip (flip (flip (convertPDRSRef p') lp) gp) rs) d))
          where p' = convertPVar p lp gp ps
        convertPCon (PCon p (Neg p1))     = PCon (convertPVar p lp gp ps) (Neg     (alphaConvertSubPDRS p1 gp ps rs))
        convertPCon (PCon p (Imp p1 p2))  = PCon (convertPVar p lp gp ps) (Imp     (alphaConvertSubPDRS p1 gp ps rs) (alphaConvertSubPDRS p2 gp ps rs))
        convertPCon (PCon p (Or p1 p2))   = PCon (convertPVar p lp gp ps) (Or      (alphaConvertSubPDRS p1 gp ps rs) (alphaConvertSubPDRS p2 gp ps rs))
        convertPCon (PCon p (Prop r p1))  = PCon p'                       (Prop    (convertPDRSRef p' r lp gp rs)    (alphaConvertSubPDRS p1 gp ps rs))
          where p' = convertPVar p lp gp ps
        convertPCon (PCon p (Diamond p1)) = PCon (convertPVar p lp gp ps) (Diamond (alphaConvertSubPDRS p1 gp ps rs))
        convertPCon (PCon p (Box  p1))    = PCon (convertPVar p lp gp ps) (Box     (alphaConvertSubPDRS p1 gp ps rs))

convertPDRSRef :: PVar -> PDRSRef -> PDRS -> PDRS -> [(PDRSRef,PDRSRef)] -> PDRSRef
convertPDRSRef pv r lp gp rs
  | pdrsBoundPRef (PRef pv r) lp gp = alphaConvertVar r rs
  | otherwise                       = r

convertPVar :: PVar -> PDRS -> PDRS -> [(PVar,PVar)] -> PVar
convertPVar pv lp gp ps
  | pdrsBoundPVar pv lp gp = alphaConvertVar pv ps
  | otherwise              = pv

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

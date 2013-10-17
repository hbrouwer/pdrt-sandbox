{-# LANGUAGE FlexibleInstances #-}
{- |
Module      :  Data.DRS.LambdaCalculus
Copyright   :  (c) Harm Brouwer and Noortje Venhuizen
License     :  Apache-2.0

Maintainer  :  me@hbrouwer.eu
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
) where

import Data.DRS.Structure
import Data.DRS.Variables

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

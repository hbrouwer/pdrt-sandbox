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
  DRSAtom
, AbstractDRS
, drsAlphaConvert
, renameVar
, drsBetaReduce
, (<<@>>)
, drsFunctionCompose
, (<<.>>)
, drsPurify
) where

import Data.DRS.Binding
import Data.DRS.DataType
import Data.DRS.Variables

import Data.List (intersect, union)

---------------------------------------------------------------------------
-- * Exported
---------------------------------------------------------------------------

---------------------------------------------------------------------------
-- ** Type classes
---------------------------------------------------------------------------

---------------------------------------------------------------------------
-- | Type class for a 'DRSAtom', which is either a 'DRS' or a 'DRSRef'.
---------------------------------------------------------------------------
class DRSAtom a
instance DRSAtom DRS
instance DRSAtom DRSRef

---------------------------------------------------------------------------
-- | Type class for an 'AbstractDRS', which is either a resolved 'DRS', or 
-- an 'unresolved DRS' that takes a 'DRSAtom' and yields an 'AbstractDRS'.
---------------------------------------------------------------------------
class AbstractDRS a
instance AbstractDRS DRS
instance (DRSAtom a, AbstractDRS b) => AbstractDRS (a -> b)


---------------------------------------------------------------------------
-- ** Alpha Conversion
---------------------------------------------------------------------------

---------------------------------------------------------------------------
-- | Applies alpha conversion to a 'DRS' on the basis of a conversion list
-- for 'DRSRef's @rs@.
---------------------------------------------------------------------------
drsAlphaConvert :: DRS -> [(DRSRef,DRSRef)] -> DRS
drsAlphaConvert d = renameSubDRS d d

---------------------------------------------------------------------------
-- | Renames a variable @v@, iff @v@ occurs in a variable conversion list.
-- Otherwise, @v@ is returned unmodified
---------------------------------------------------------------------------
renameVar :: (Eq a) => a -> [(a,a)] -> a
renameVar v [] = v
renameVar v ((cv,cv'):cvs)
  | v == cv   = cv'
  | otherwise = renameVar v cvs

---------------------------------------------------------------------------
-- ** Beta Reduction
---------------------------------------------------------------------------

---------------------------------------------------------------------------
-- | Apply beta reduction on an 'AbstractDRS' with a 'DRSAtom'.
---------------------------------------------------------------------------
drsBetaReduce :: (AbstractDRS a, DRSAtom b) => (b -> a) -> b -> a
drsBetaReduce a = a

-- | Infix notation for 'drsBetaReduce'
(<<@>>) :: (AbstractDRS a, DRSAtom b) => (b -> a) -> b -> a
ud <<@>> ad = ud `drsBetaReduce` ad

---------------------------------------------------------------------------
-- ** Function Composition
---------------------------------------------------------------------------

---------------------------------------------------------------------------
-- | Apply function composition to two 'unresolved DRS's, yielding
-- a new 'unresolved DRS'
---------------------------------------------------------------------------
drsFunctionCompose :: (b -> c) -> (a -> b) -> a -> c
drsFunctionCompose = (.)

-- | Infix notation for 'drsFunctionCompose'
(<<.>>) :: (b -> c) -> (a -> b) -> a -> c
a1 <<.>> a2 = a1 `drsFunctionCompose` a2

---------------------------------------------------------------------------
-- ** DRS Purification
---------------------------------------------------------------------------

---------------------------------------------------------------------------
-- | Converts a 'DRS' into a /pure/ 'DRS' by purifying its 'DRSRef's, 
-- where:
--
-- [A 'DRS' is pure /iff/:]
--
-- * There are no occurrences of duplicate, unbound uses of the same
--   'DRSRef'.
---------------------------------------------------------------------------
drsPurify :: DRS -> DRS
drsPurify gdrs = fst $ purifyRefs (gdrs,drsFreeRefs gdrs gdrs) gdrs

---------------------------------------------------------------------------
-- * Private
---------------------------------------------------------------------------

---------------------------------------------------------------------------
-- ** DRS renaming
---------------------------------------------------------------------------

---------------------------------------------------------------------------
-- | Applies alpha conversion to a 'DRS' @sd@, which is a sub-'DRS' of the
-- global 'DRS' @gd@, on the basis of a conversion list for 'DRSRef's @rs@.
---------------------------------------------------------------------------
renameSubDRS :: DRS -> DRS -> [(DRSRef,DRSRef)] -> DRS
renameSubDRS ld@(LambdaDRS _) _ _ = ld
renameSubDRS (Merge d1 d2) gd rs  = Merge d1' d2'
  where d1' = renameSubDRS d1 gd rs
        d2' = renameSubDRS d2 gd rs
renameSubDRS sd@(DRS u _) gd rs    = DRS u' c'
  where u' = renameRefs u rs
        c' = renameCons sd gd rs

---------------------------------------------------------------------------
-- | Applies alpha conversion to a list of 'DRSRef's @u@, on the basis
-- of a conversion list @rs@
---------------------------------------------------------------------------
renameRefs :: [DRSRef] -> [(DRSRef,DRSRef)] -> [DRSRef]
renameRefs u rs = map (`renameVar` rs) u

---------------------------------------------------------------------------
-- | Applies alpha conversion to the conditions in a 'DRS' @sd@, which is
-- a sub-'DRS' of @gd@, on the basis of a conversion list for 'DRSRef's
-- @rs@.
---------------------------------------------------------------------------
renameCons :: DRS -> DRS -> [(DRSRef,DRSRef)] -> [DRSCon]
renameCons (LambdaDRS _) _ _  = []
renameCons (Merge _ _) _ _    = []
renameCons ld@(DRS _ c) gd rs = map convertCon c
  where convertCon :: DRSCon -> DRSCon
        convertCon (Rel r d)    = Rel r   (map convertRef d)
        convertCon (Neg d1)     = Neg     (renameSubDRS d1 gd rs)
        convertCon (Imp d1 d2)  = Imp     (renameSubDRS d1 gd rs) (renameSubDRS d2 gd rs)
        convertCon (Or d1 d2)   = Or      (renameSubDRS d1 gd rs) (renameSubDRS d2 gd rs)
        convertCon (Prop r d1)  = Prop    (convertRef r)          (renameSubDRS d1 gd rs)
        convertCon (Diamond d1) = Diamond (renameSubDRS d1 gd rs)
        convertCon (Box d1)     = Box     (renameSubDRS d1 gd rs)
        convertRef :: DRSRef -> DRSRef
        convertRef r
          | drsBoundRef r ld gd = renameVar r rs
          | otherwise           = r

---------------------------------------------------------------------------
-- ** Purifying DRSRefs
---------------------------------------------------------------------------

---------------------------------------------------------------------------
-- | Replaces duplicate uses of 'DRSRef's by new 'DRSRef's.
--
-- [This function implements the following algorithm:]
--
-- (1) start with the global 'DRS' @gd@ and add all free PVars in @gd@ to
-- the list of seen referents @rs@ (see 'drsPurify');
-- 
-- 2. check the universe @u@ of the first atomic 'DRS' @ld@ against @rs@
--    and, if necessary, alpha-convert @ld@ replacing duplicates for new
--    'DRSRef's in @u@;
-- 
-- 3. add the universe of @ld@ to the list of seen 'DRSRef's @rs@;
-- 
-- 4. go through all conditions of @ld@, while continually updating @rs@.
---------------------------------------------------------------------------
purifyRefs :: (DRS,[DRSRef]) -> DRS -> (DRS,[DRSRef])
purifyRefs (ld@(LambdaDRS _),ers) _  = (ld,ers)
purifyRefs (Merge d1 d2,ers)      gd = (Merge cd1 cd2,ers2)
  where (cd1,ers1) = purifyRefs (d1,ers)  gd
        (cd2,ers2) = purifyRefs (d2,ers1) gd
purifyRefs (ld@(DRS u _),ers)      gd = (DRS u1 c2,ers1)
-- In case we do not want to rename ambiguous bindings:
-- purifyRefs (ld@(DRS u _),ers)      gd = (DRS u1 c2,u1 ++ ers1)
  where ld'       = drsAlphaConvert ld (zip ors (newDRSRefs ors (drsVariables gd `union` ers)))
        u1        = drsUniverse ld'
        c1        = drsConditions ld'
        ors       = u `intersect` ers
        (c2,ers1) = purify (c1,u1 ++ ers)
        -- In case we do not want to rename ambiguous bindings:
        --(c2,ers1)    = purify (c1,ers)
        purify :: ([DRSCon],[DRSRef]) -> ([DRSCon],[DRSRef])
        purify ([],rs)             = ([],rs)
        purify (c@(Rel _ d):cs,rs) = (c:ccs,rs1)
          where (ccs,rs1) = purify (cs,rs ++ d)        
        purify (Neg d1:cs,rs)      = (Neg cd1:ccs,rs2)
          where (cd1,rs1) = purifyRefs (d1,rs) gd
                (ccs,rs2) = purify (cs,rs1)
        purify (Imp d1 d2:cs,rs)   = (Imp cd1 cd2:ccs,rs3)
          where (cd1,rs1) = purifyRefs (renameSubDRS d1 gd nrs,rs)  gd
                (cd2,rs2) = purifyRefs (renameSubDRS d2 gd nrs,rs1) gd
                (ccs,rs3) = purify (cs,rs2)
                nrs = zip ors' (newDRSRefs ors' (drsVariables gd `union` rs))
                ors' = drsUniverse d1 `intersect` rs
                -- In case we do not want to rename ambiguous bindings:
                -- ors = drsUniverses d2 \\ drsUniverse d1 `intersect` rs
        purify (Or d1 d2:cs,rs)    = (Or cd1 cd2:ccs,rs3)
          where (cd1,rs1) = purifyRefs (renameSubDRS d1 gd nrs,rs)  gd
                (cd2,rs2) = purifyRefs (renameSubDRS d2 gd nrs,rs1) gd
                (ccs,rs3) = purify (cs,rs2)
                nrs = zip ors' (newDRSRefs ors' (drsVariables gd `union` rs))
                ors' = drsUniverse d1 `intersect` rs
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

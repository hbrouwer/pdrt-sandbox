{-# OPTIONS_GHC -Wno-incomplete-uni-patterns #-}
{- |
Module      :  Data.PDRS.Merge
Copyright   :  (c) Harm Brouwer and Noortje Venhuizen
License     :  Apache-2.0

Maintainer  :  me@hbrouwer.eu, n.j.venhuizen@rug.nl
Stability   :  provisional
Portability :  portable

The module "Data.PDRS.Merge" contains functions required for merging 'PDRS's.
-}

module Data.PDRS.Merge (
  pdrsAMerge
, (<<+>>)
, pdrsPMerge
, (<<*>>)
, pdrsCombine
, (<<&>>)
, pdrsResolveMerges
, pdrsDisjoin
) where

import Data.PDRS.LambdaCalculus
import Data.PDRS.DataType
import Data.PDRS.Structure
import Data.PDRS.Variables

import Data.List (intersect, union)

---------------------------------------------------------------------------
-- * Exported
---------------------------------------------------------------------------

---------------------------------------------------------------------------
-- | Applies assertive merge to 'PDRS' @p1@ and 'PDRS' @p2@.
---------------------------------------------------------------------------
pdrsAMerge :: PDRS -> PDRS -> PDRS
pdrsAMerge p lp@(LambdaPDRS _) = AMerge p lp
pdrsAMerge lp@(LambdaPDRS _) p = AMerge lp p
pdrsAMerge p am@(AMerge k1 k2)
  | isLambdaPDRS k1 = AMerge k1 (pdrsAMerge p k2)                             -- p + (lk1 + k2) = lk1 + (p + k2)
  | isLambdaPDRS k2 = AMerge (pdrsAMerge p k1) k2                             -- p + (k1 + lk2) = (p + k1) + lk2
  | otherwise       = pdrsAMerge p (pdrsResolveMerges am)
pdrsAMerge am@(AMerge k1 k2) p
  | isLambdaPDRS k1 = AMerge k1 (pdrsAMerge k2 p)                             -- (lk1 + k2) + p = lk1 + (k2 + p)
  | isLambdaPDRS k2 = AMerge k2 (pdrsAMerge k1 p)                             -- (k1 + lk2) + p = lk2 + (k1 + p)
  | otherwise       = pdrsAMerge (pdrsResolveMerges am) p
pdrsAMerge p pm@(PMerge k1 k2)
  | isLambdaPDRS k1 = PMerge k1 (pdrsAMerge p k2)                             -- p + (lk1 * k2) = lk1 * (p + k2)
  | isLambdaPDRS k2 = AMerge (pdrsPMerge k1 p) k2                             -- p + (k1 * lk2) = (k1 * p) + lk2
  | otherwise       = pdrsAMerge p (pdrsResolveMerges pm)
pdrsAMerge pm@(PMerge k1 k2) p
  | isLambdaPDRS k1 = PMerge k1 (pdrsAMerge k2 p)                             -- (lk1 * k2) + p = lk1 * (k2 + p)
  | isLambdaPDRS k2 = AMerge k2 (pdrsPMerge k1 p)                             -- (k1 * lk2) + p = lk2 + (k1 * p)
  | otherwise       = pdrsAMerge (pdrsResolveMerges pm) p
pdrsAMerge p1@(PDRS{}) p2@(PDRS{}) = pdrsPurify $ amerge p1 (pdrsDisjoin p2' p1')
  where p1' = pdrsPurify $ pdrsResolveMerges p1
        p2' = pdrsPurify $ pdrsResolveMerges p2
        amerge :: PDRS -> PDRS -> PDRS
        -- | Make sure all asserted content in 'PDRS' @p@ remains
        -- asserted by renaming global label to @l@ before merging.
        amerge p@(PDRS l1 _ _ _) (PDRS l2 m2 u2 c2) = PDRS l2 (m1 `union` m2') (u1 `union` u2') (c1 `union` c2')
          where (PDRS _ m1 u1 c1)    = pdrsAlphaConvert p [(l1,l2)] []
                (PDRS _ m2' u2' c2') = pdrsAlphaConvert (PDRS l1 m2 u2 c2) [(l1,l2)] [] 
                -- ^ in order to make sure that projected variables can
                -- become bound by means of assertive merge
        amerge pdrs1 pdrs2                          = AMerge pdrs1 pdrs2

-- | Infix notation for 'pdrsAMerge'
(<<+>>) :: PDRS -> PDRS -> PDRS
p1 <<+>> p2 = p1 `pdrsAMerge` p2

---------------------------------------------------------------------------
-- | Applies projective merge to 'PDRS' @p1@ and 'PDRS' @p2@.
---------------------------------------------------------------------------
pdrsPMerge :: PDRS -> PDRS -> PDRS
pdrsPMerge p lp@(LambdaPDRS _) = PMerge p lp
pdrsPMerge lp@(LambdaPDRS _) p = PMerge lp p
pdrsPMerge p am@(AMerge k1 k2)
  | isLambdaPDRS k1 = AMerge k1 (pdrsPMerge p k2)                             -- p * (lk1 + k2) = lk1 + (p * k2)
  | isLambdaPDRS k2 = AMerge (pdrsPMerge p k1) k2                             -- p * (k1 + lk2) = (p * k1) + lk2
  | otherwise       = pdrsPMerge p (pdrsResolveMerges am)
pdrsPMerge am@(AMerge k1 k2) p
  | isLambdaPDRS k1 = PMerge (pdrsAMerge k1 (emptyPDRS k2)) (pdrsPMerge k2 p) -- (lk1 + k2) * p = (lk1 + ek2) * (l2 * p)
  | isLambdaPDRS k2 = PMerge (pdrsAMerge k2 (emptyPDRS k1)) (pdrsPMerge k1 p) -- (k1 + lk2) * p = (lk2 + ek1) * (k1 * p)
  | otherwise       = pdrsPMerge (pdrsResolveMerges am) p
pdrsPMerge p pm@(PMerge k1 k2)
  | isLambdaPDRS k1 = PMerge k1 (pdrsPMerge p k2)                             -- p * (lk1 * k2) = lk1 * (p * k2)
  | isLambdaPDRS k2 = PMerge (pdrsPMerge p k1) k2                             -- p * (k1 * lk2) = (p * k1) * lk2 
  | otherwise       = pdrsPMerge p (pdrsResolveMerges pm)
pdrsPMerge pm@(PMerge k1 k2) p
  | isLambdaPDRS k1 = PMerge k1 (pdrsPMerge k2 p)                             -- (lk1 * k2) * p = lk1 * (k2 * p)
  | isLambdaPDRS k2 = PMerge k2 (pdrsPMerge k1 p)                             -- (k1 * lk2) * p = lk2 * (k1 * p)
  | otherwise       = pdrsPMerge (pdrsResolveMerges pm) p
pdrsPMerge p1@(PDRS{}) p2@(PDRS{}) = pdrsPurify $ pmerge p1' (pdrsDisjoin p2' p1')
  where p1' = pdrsPurify $ pdrsResolveMerges p1
        p2' = pdrsPurify $ pdrsResolveMerges p2
        pmerge :: PDRS -> PDRS -> PDRS
        -- | Content of 'PDRS' @p@ is added to 'PDRS' @p'@ without
        -- replacing pointers, resulting in the content of @p@ becoming
        -- projected in the resulting 'PDRS'.
        pmerge (PDRS l m u c) (PDRS l' m' u' c') = PDRS l' ([(l',l)] `union` m `union` m') (u `union` u') (c `union` c')
        pmerge pdrs1 pdrs2                       = PMerge pdrs1 pdrs2

-- | Infix notation for 'pdrsPMerge'
(<<*>>) :: PDRS -> PDRS -> PDRS
p1 <<*>> p2 = p1 `pdrsPMerge` p2

---------------------------------------------------------------------------
-- | Combines an unresolved 'PDRS' and a 'PDRS' into a resolved 'PDRS'.
---------------------------------------------------------------------------
pdrsCombine :: ((PDRSRef -> PDRS) -> PDRS) -> PDRS -> PDRS
pdrsCombine up p = pdrsPurify $ pdrsResolveMerges (up (const p))

-- | Infix notation for 'pdrsCombine'
(<<&>>) :: ((PDRSRef -> PDRS) -> PDRS) -> PDRS -> PDRS
up <<&>> p = up `pdrsCombine` p

---------------------------------------------------------------------------
-- | Resolves all unresolved merges in a 'PDRS'.
---------------------------------------------------------------------------
pdrsResolveMerges :: PDRS -> PDRS
pdrsResolveMerges lp@(LambdaPDRS _) = lp
pdrsResolveMerges (AMerge p1 p2)    = pdrsResolveMerges p1 <<+>> pdrsResolveMerges p2
pdrsResolveMerges (PMerge p1 p2)    = pdrsResolveMerges p1 <<*>> pdrsResolveMerges p2
pdrsResolveMerges (PDRS l m u c)    = PDRS l m u (map resolve c)
  where resolve :: PCon -> PCon
        resolve pc@(PCon _ (Rel _ _)) = pc
        resolve (PCon p (Neg p1))     = PCon p (Neg     (pdrsResolveMerges p1))
        resolve (PCon p (Imp p1 p2))  = PCon p (Imp     (pdrsResolveMerges p1) (pdrsResolveMerges p2))
        resolve (PCon p (Or p1 p2))   = PCon p (Or      (pdrsResolveMerges p1) (pdrsResolveMerges p2))
        resolve (PCon p (Prop r p1))  = PCon p (Prop r  (pdrsResolveMerges p1))
        resolve (PCon p (Diamond p1)) = PCon p (Diamond (pdrsResolveMerges p1))
        resolve (PCon p (Box p1))     = PCon p (Box     (pdrsResolveMerges p1))

---------------------------------------------------------------------------
-- | Disjoins 'PDRS' @p1@ from 'PDRS' @p2@, where:
--
-- [@p1@ is disjoined from @p2@ /iff/]
--  
--  * All duplicate occurrences of 'PVar's and 'PDRSRef's from 'PDRS' @p2@
--    in 'PDRS' @p1@ are replaced by new variables.
---------------------------------------------------------------------------
pdrsDisjoin :: PDRS -> PDRS -> PDRS
pdrsDisjoin p p' = pdrsAlphaConvert p (zip ops nps) (zip ors nrs)
  where ops = pdrsPVars p `intersect` pdrsPVars p'
        nps = newPVars ops (pdrsPVars p `union` pdrsPVars p')
        ors = pdrsVariables p `intersect` pdrsVariables p'
        nrs = newPDRSRefs ors (pdrsVariables p `union` pdrsVariables p')

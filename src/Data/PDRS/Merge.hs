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
, emptyPDRS
, pdrsDisjoin
, notthesame

, pdrsUnresolve
) where

import Data.DRS.Variables (drsRefToDRSVar)
import Data.PDRS.LambdaCalculus
import Data.PDRS.Properties
import Data.PDRS.Structure
import Data.PDRS.Variables

import Data.List ((\\), intersect, union)

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
  | isLambdaPDRS k1 = AMerge k1 (pdrsAMerge p k2) -- p + (lk1 + k2) = lk1 + (p + k2)
  | isLambdaPDRS k2 = AMerge (pdrsAMerge p k1) k2 -- p + (k1 + lk2) = (p + k1) + lk2
  | otherwise       = pdrsAMerge p (pdrsResolveMerges am)
pdrsAMerge am@(AMerge k1 k2) p
  | isLambdaPDRS k1 = AMerge k1 (pdrsAMerge k2 p) -- (lk1 + k2) + p = lk1 + (k2 + p)
  | isLambdaPDRS k2 = AMerge k2 (pdrsAMerge k1 p) -- (k1 + lk2) + p = lk2 + (k1 + p)
  | otherwise       = pdrsAMerge (pdrsResolveMerges am) p
pdrsAMerge p pm@(PMerge k1 k2)
  | isLambdaPDRS k1 = PMerge k1 (pdrsAMerge p k2) -- p + (lk1 * k2) = lk1 * (p + k2)
  | isLambdaPDRS k2 = AMerge (pdrsPMerge k1 p) k2 -- p + (k1 * lk2) = (k1 * p) + lk2
  | otherwise       = pdrsAMerge p (pdrsResolveMerges pm)
pdrsAMerge pm@(PMerge k1 k2) p
  | isLambdaPDRS k1 = PMerge k1 (pdrsAMerge k2 p) -- (lk1 * k2) + p = lk1 * (k2 + p)
  | isLambdaPDRS k2 = AMerge k2 (pdrsPMerge k1 p) -- (k1 * lk2) + p = lk2 + (k1 * p)
  | otherwise       = pdrsAMerge (pdrsResolveMerges pm) p
pdrsAMerge p1@(PDRS{}) p2@(PDRS{}) = amerge p1 (pdrsDisjoin p2' p1')
  where p1' = pdrsPurify $ pdrsResolveMerges p1
        p2' = pdrsPurify $ pdrsResolveMerges p2
        amerge :: PDRS -> PDRS -> PDRS
        -- | Make sure all asserted content in 'PDRS' @p@ remains
        -- asserted by renaming global label to @l@ before merging.
        amerge p (PDRS l m u c) = PDRS l (m' `union` m) (u' `union` u) (c' `union` c)
          where (PDRS l' m' u' c') = pdrsAlphaConvert p [(pdrsLabel p,l)] []

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
  | isLambdaPDRS k1 = AMerge k1 (pdrsPMerge p k2) -- p * (lk1 + k2) = lk1 + (p * k2)
  | isLambdaPDRS k2 = AMerge (pdrsPMerge p k1) k2 -- p * (k1 + lk2) = (p * k1) + lk2
  | otherwise       = pdrsPMerge p (pdrsResolveMerges am)
pdrsPMerge am@(AMerge k1 k2) p
  | isLambdaPDRS k1 = PMerge (pdrsAMerge k1 (emptyPDRS k2)) (pdrsPMerge k2 p) 
  -- (lk1 + k2) * p = (lk1 + ek2) * (l2 * p)
  | isLambdaPDRS k2 = PMerge (pdrsAMerge k2 (emptyPDRS k1)) (pdrsPMerge k1 p)
  -- (k1 + lk2) * p = (lk2 + ek1) * (k1 * p)
  | otherwise       = pdrsPMerge (pdrsResolveMerges am) p
pdrsPMerge p pm@(PMerge k1 k2)
  | isLambdaPDRS k1 = PMerge k1 (pdrsPMerge p k2) -- p * (lk1 * k2) = lk1 * (p * k2)
  | isLambdaPDRS k2 = PMerge (pdrsPMerge p k1) k2 -- p * (k1 * lk2) = (p * k1) * lk2 
  | otherwise       = pdrsPMerge p (pdrsResolveMerges pm)
pdrsPMerge pm@(PMerge k1 k2) p
  | isLambdaPDRS k1 = PMerge k1 (pdrsPMerge k2 p) -- (lk1 * k2) * p = lk1 * (k2 * p)
  | isLambdaPDRS k2 = PMerge k2 (pdrsPMerge k1 p) -- (k1 * lk2) * p = lk2 * (k1 * p)
  | otherwise       = pdrsPMerge (pdrsResolveMerges pm) p
pdrsPMerge p1@(PDRS{}) p2@(PDRS{}) = pmerge p1' (pdrsDisjoin p2' p1')
  where p1' = pdrsPurify $ pdrsResolveMerges p1
        p2' = pdrsPurify $ pdrsResolveMerges p2
        pmerge :: PDRS -> PDRS -> PDRS
        -- | Content of 'PDRS' @p@ is added to 'PDRS' @p'@ without
        -- replacing pointers, resulting in the content of @p@ becoming
        -- projected in the resulting 'PDRS'.
        pmerge (PDRS l m u c) (PDRS l' m' u' c') = PDRS l' ((l',l):m `union` m') (u `union` u') (c `union` c')

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
-- | Returns an empty 'PDRS', if possible with the same label as 'PDRS' @p@.
---------------------------------------------------------------------------
emptyPDRS :: PDRS -> PDRS
emptyPDRS lp@(LambdaPDRS _) = lp
emptyPDRS (AMerge p1 p2)
  | isLambdaPDRS p1 = AMerge p1 (emptyPDRS p2)
  | isLambdaPDRS p2 = AMerge (emptyPDRS p1) p2
  | otherwise       = emptyPDRS (p1 <<+>> p2)
emptyPDRS (PMerge p1 p2)
  | isLambdaPDRS p1 = PMerge p1 (emptyPDRS p2)
  | isLambdaPDRS p2 = PMerge (emptyPDRS p1) p2
  | otherwise       = emptyPDRS (p1 <<*>> p2)
emptyPDRS (PDRS l _ _ _)    = PDRS l [] [] []

---------------------------------------------------------------------------
-- * Private
---------------------------------------------------------------------------

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

---------------------------------------------------------------------------
-- | Disjoins 'unresolved PDRS' @n1@ from 'unresolved PDRS' @n2@.
---------------------------------------------------------------------------
notthesame :: ((PDRSRef -> PDRS) -> PDRS) -> ((PDRSRef -> PDRS) -> PDRS) -> ((PDRSRef -> PDRS) -> PDRS)
notthesame n1 n2 = \k-> pdrsUnresolve (pdrsDisjoin n1' n2') i k
  where n1' = n1 (\x -> LambdaPDRS (("t",[(drsRefToDRSVar . pdrsRefToDRSRef) x]),i))
        n2' = n2 (\x -> LambdaPDRS (("t",[(drsRefToDRSVar . pdrsRefToDRSRef) x]),0))
        i   = maximum (map snd (lambdas (n1 (\x -> LambdaPDRS (("t",[]),0))))) + 1

---------------------------------------------------------------------------
-- | Converts a PDRS that contains a 'LambdaPDRS' whose argument position
-- @li@ equals some 'Int' @i@ into an 'unresolved PDRS'.
---------------------------------------------------------------------------
pdrsUnresolve :: PDRS -> Int -> (PDRSRef -> PDRS) -> PDRS
pdrsUnresolve lp@(LambdaPDRS ((_,r),li)) i k 
  | li == i   = k (PDRSRef $ head r)
  | otherwise = lp
pdrsUnresolve (AMerge p1 p2) i k = AMerge (pdrsUnresolve p1 i k) (pdrsUnresolve p2 i k)
pdrsUnresolve (PMerge p1 p2) i k = PMerge (pdrsUnresolve p1 i k) (pdrsUnresolve p2 i k)
pdrsUnresolve (PDRS l m u c) i k = (PDRS l m u (replaceLambda c k))
  where replaceLambda :: [PCon] -> (PDRSRef -> PDRS) -> [PCon]
        replaceLambda [] k                        = []
        replaceLambda (pc@(PCon _ (Rel{})):pcs) k = (pc:replaceLambda pcs k)
        replaceLambda (PCon p (Neg p1):pcs)     k = (PCon p (Neg     (pdrsUnresolve p1 i k)):replaceLambda pcs k)
        replaceLambda (PCon p (Imp p1 p2):pcs)  k = (PCon p (Imp     (pdrsUnresolve p1 i k) (pdrsUnresolve p2 i k)):replaceLambda pcs k)
        replaceLambda (PCon p (Or p1 p2):pcs)   k = (PCon p (Or      (pdrsUnresolve p1 i k) (pdrsUnresolve p2 i k)):replaceLambda pcs k)
        replaceLambda (PCon p (Prop r p1):pcs)  k = (PCon p (Prop r  (pdrsUnresolve p1 i k)):replaceLambda pcs k)
        replaceLambda (PCon p (Diamond p1):pcs) k = (PCon p (Diamond (pdrsUnresolve p1 i k)):replaceLambda pcs k)
        replaceLambda (PCon p (Box p1):pcs)     k = (PCon p (Box     (pdrsUnresolve p1 i k)):replaceLambda pcs k)

{- |
Module      :  Data.PDRS.Merge
Copyright   :  (c) Harm Brouwer and Noortje Venhuizen
License     :  Apache-2.0

Maintainer  :  me@hbrouwer.eu
Stability   :  provisional
Portability :  portable

PDRS merges
-}

module Data.PDRS.Merge (
  pdrsAMerge
, (<<+>>)
, pdrsPMerge
, (<<*>>)
, pdrsResolveMerges
, pdrsDisjoin
) where

import Data.PDRS.LambdaCalculus
import Data.PDRS.Properties
import Data.PDRS.Structure
import Data.PDRS.Variables

import Data.List (intersect, nub, union)

-- | Applies assertive merge to PDRS @p1@ and PDRS @p2@
pdrsAMerge :: PDRS -> PDRS -> PDRS
pdrsAMerge p1 p2 = amerge rp1 (pdrsDisjoin rp2 (pdrsPVars rp1) (pdrsVariables rp1))
  where rp1 = pdrsResolveMerges p1
        rp2 = pdrsResolveMerges p2
        amerge :: PDRS -> PDRS -> PDRS
        amerge p (PDRS l m u c) = PDRS l (m `union` m') (u `union` u') (c `union` c')
          where (PDRS l' m' u' c') = pdrsAlphaConvert p [(pdrsLabel p,l)] []
        
-- | Infix notation for 'pdrsAMerge'
(<<+>>) :: PDRS -> PDRS -> PDRS
p1 <<+>> p2 = p1 `pdrsAMerge` p2

-- | Applies projective merge to PDRS @p1@ and PDRS @p2@
pdrsPMerge :: PDRS -> PDRS -> PDRS
pdrsPMerge p1 p2 = pmerge rp1 (pdrsDisjoin rp2 (pdrsPVars rp1) (pdrsVariables rp1))
  where rp1 = pdrsResolveMerges p1
        rp2 = pdrsResolveMerges p2
        pmerge :: PDRS -> PDRS -> PDRS
        pmerge (PDRS l1 m1 u1 c1) (PDRS l2 m2 u2 c2) = PDRS l2 m u c
          where m = m1 `union` (m2 ++ [(l2,l1)])
                u = u1 `union` u2
                c = c1 `union` c2

-- | Infix notation for 'pdrsPMerge'
(<<*>>) :: PDRS -> PDRS -> PDRS
p1 <<*>> p2 = p1 `pdrsPMerge` p2

-- | Resolves all unresolved merges in a PDRS
pdrsResolveMerges :: PDRS -> PDRS
pdrsResolveMerges lp@(LambdaPDRS _) = lp
pdrsResolveMerges (AMerge p1 p2)
  | isLambdaPDRS p1 || isLambdaPDRS p2 = AMerge p1 p2
  | otherwise                          = p1 <<+>> p2
pdrsResolveMerges (PMerge p1 p2)
  | isLambdaPDRS p1 || isLambdaPDRS p2 = PMerge p1 p2
  | otherwise                          = p1 <<*>> p2
pdrsResolveMerges (PDRS l m u c) = PDRS l m u (map resolve c)
  where resolve :: PCon -> PCon
        resolve pc@(PCon _ (Rel _ _)) = pc
        resolve (PCon p (Neg p1))     = PCon p (Neg     (pdrsResolveMerges p1))
        resolve (PCon p (Imp p1 p2))  = PCon p (Imp     (pdrsResolveMerges p1) (pdrsResolveMerges p2))
        resolve (PCon p (Or p1 p2))   = PCon p (Or      (pdrsResolveMerges p1) (pdrsResolveMerges p2))
        resolve (PCon p (Prop r p1))  = PCon p (Prop r  (pdrsResolveMerges p1))
        resolve (PCon p (Diamond p1)) = PCon p (Diamond (pdrsResolveMerges p1))
        resolve (PCon p (Box p1))     = PCon p (Box     (pdrsResolveMerges p1))

pdrsDisjoin :: PDRS -> [PVar] -> [PDRSRef] -> PDRS
pdrsDisjoin p pvs prs = pdrsAlphaConvert p (zip ops nps) (zip ors nrs)
  where ops = pvs `intersect` pdrsPVars p
        nps = newPVars ops (pvs `union` pdrsPVars p)
        ors = prs `intersect` pdrsVariables p
        nrs = newPDRSRefs ors (prs `union` pdrsVariables p)

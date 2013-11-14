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
, pdrsResolveMerges
) where

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
pdrsAMerge p1 p2 = amerge rp1 (disjoin rp2 rp1)
  where -- | Merged 'PDRS's should be pure, with resolved merges.
        rp1 = pdrsPurify $ pdrsResolveMerges p1
        rp2 = pdrsPurify $ pdrsResolveMerges p2
        -- | Make sure all asserted content in 'PDRS' @p@ remains
        -- asserted by renaming global label to @l@ before merging.
        amerge :: PDRS -> PDRS -> PDRS
        amerge p (PDRS l m u c) = PDRS l (m `union` m') (u `union` u') (c `union` c')
          where (PDRS l' m' u' c') = pdrsAlphaConvert p [(pdrsLabel p,l)] []
        -- | Replace all (duplicate) occurrences of 'PVar's and 'PDRSRef's
        -- from PDRS @p'@ in 'PDRS' @p@ by new variables. Asserted referents
        -- in the universe of the antecedent PDRS do not count as duplicates
        -- because multiple bound declarations are allowed in PDRT.
        disjoin :: PDRS -> PDRS -> PDRS
        disjoin p p' = pdrsAlphaConvert p (zip ops nps) (zip ors nrs)
          where ops = pdrsPVars p `intersect` pdrsPVars p'
                nps = newPVars ops (pdrsPVars p `union` pdrsPVars p')
                ors = pdrsVariables p `intersect` filter (\r -> (PRef (pdrsLabel p') r) `notElem` pdrsUniverse p') (pdrsVariables p')
                nrs = newPDRSRefs ors (pdrsVariables p `union` pdrsVariables p')

-- | Infix notation for 'pdrsAMerge'
(<<+>>) :: PDRS -> PDRS -> PDRS
p1 <<+>> p2 = p1 `pdrsAMerge` p2

---------------------------------------------------------------------------
-- | Applies projective merge to 'PDRS' @p1@ and 'PDRS' @p2@.
---------------------------------------------------------------------------
pdrsPMerge :: PDRS -> PDRS -> PDRS
pdrsPMerge p1 p2 = pmerge rp1 (disjoin rp2 rp1)
  where -- | Merged 'PDRS's should be pure, with resolved merges.
        rp1 = pdrsPurify $ pdrsResolveMerges p1
        rp2 = pdrsPurify $ pdrsResolveMerges p2
        -- | Content of 'PDRS' @p@ is added to 'PDRS' @p'@ without
        -- replacing pointers, resulting in the content of @p@ becoming
        -- projected in the resulting 'PDRS'.
        pmerge :: PDRS -> PDRS -> PDRS
        pmerge (PDRS l m u c) (PDRS l' m' u' c') 
            = PDRS l' ((l',l):m `union` m') (u `union` u') (c `union` c')
        -- | Replace all (duplicate) occurrences of 'PVar's and 'PDRSRef's
        -- from PDRS @p'@ in 'PDRS' @p@ by new variables. Asserted referents
        -- in the universe of the antecedent PDRS do not count as duplicates
        -- because multiple bound declarations are allowed in PDRT.
        disjoin :: PDRS -> PDRS -> PDRS
        disjoin p p' = pdrsAlphaConvert p (zip ops nps) (zip ors nrs)
          where ops = pdrsPVars p `intersect` pdrsPVars p'
                nps = newPVars ops (pdrsPVars p `union` pdrsPVars p')
                ors = pdrsVariables p `intersect` filter (\r -> (PRef (pdrsLabel p') r) `notElem` pdrsUniverse p') (pdrsVariables p')
                nrs = newPDRSRefs ors (pdrsVariables p `union` pdrsVariables p')

-- | Infix notation for 'pdrsPMerge'
(<<*>>) :: PDRS -> PDRS -> PDRS
p1 <<*>> p2 = p1 `pdrsPMerge` p2

---------------------------------------------------------------------------
-- | Resolves all unresolved merges in a 'PDRS'.
---------------------------------------------------------------------------
pdrsResolveMerges :: PDRS -> PDRS
pdrsResolveMerges lp@(LambdaPDRS _)    = lp
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


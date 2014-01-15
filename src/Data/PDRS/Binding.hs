{- |
Module      :  Data.PDRS.Binding
Copyright   :  (c) Harm Brouwer and Noortje Venhuizen
License     :  Apache-2.0

Maintainer  :  me@hbrouwer.eu, n.j.venhuizen@rug.nl
Stability   :  provisional
Portability :  portable

PDRS binding
-}

module Data.PDRS.Binding
(
  pdrsBoundPRef
, pdrsBoundPVar
, pdrsPRefBoundByPRef
, pdrsIsFreePVar
, pdrsFreePRefs
, pdrsFreePVars
) where

import Data.PDRS.DataType
import Data.PDRS.ProjectionGraph
import Data.PDRS.Structure
import Data.PDRS.Variables
import Data.List (partition, union)

---------------------------------------------------------------------------
-- * Exported
---------------------------------------------------------------------------

---------------------------------------------------------------------------
-- | Returns whether 'PRef' @pr@ in context $lp$ is bound in the 'PDRS'
-- @gp@, where:
--
-- [@pdrsBoundRef pr lp gp@ /iff/]
--
-- There exists a context @pv@, such that
--
--  (1) @pv@ is accessible from the introduction site of @pr@ (@lp@); and
--  
--  2. @pv@ is accessible from the interpretation site of @pr@ (@p@); and
--  
--  3. together with the 'PDRSRef' of @pr@ (@r@), @pv@ forms a 'PRef' 
--     that is introduced in some universe in @gp@.
---------------------------------------------------------------------------
pdrsBoundPRef :: PRef -> PDRS -> PDRS -> Bool
pdrsBoundPRef (PRef p r) lp gp
  | (pdrsLabel lp) `elem` vs && p `elem` vs = bound vs
  | otherwise                               = False
  where pg = projectionGraph gp
        vs = vertices pg
        bound :: [PVar] -> Bool
        bound [] = False
        bound (pv:pvs)
          | path pg (pdrsLabel lp) pv && path pg p pv = PRef pv r `elem` pdrsUniverses gp || bound pvs
          | otherwise                                 = bound pvs

---------------------------------------------------------------------------
-- | Returns whether PRef @pr1@ introduced in local PDRS @lp@ is bound by
-- projected referent @pr2@ in PDRS @pdrs@, where:
--
-- [@boundByPRef pr1 lp1 pr2 pdrs@ /iff/]
--
--  (1) @pr1@ and @pr2@ share the same referent; and
--  
--  2. @pr2@ is part of some universe in @pdrs@ (i.e., can bind referents); and
--  
--  3. The interpretation site of @pr2@ is accessible from both the
--    introduction and interpretation site of @pr1@.
---------------------------------------------------------------------------
pdrsPRefBoundByPRef :: PRef -> PDRS -> PRef -> PDRS -> Bool
pdrsPRefBoundByPRef (PRef p1 r1) lp pr2@(PRef p2 r2) pdrs =
  r1 == r2
  && pr2 `elem` pdrsUniverses pdrs
  && pdrsIsAccessibleContext p1 p2 pdrs
  && pdrsIsAccessibleContext (pdrsLabel lp) p2 pdrs

---------------------------------------------------------------------------
-- | Returns whether @pv@ is a free projection variable in PDRS @p@, where:
--
-- [@pdrsIsFreePVar pv p@ /iff/]
--
-- * context @pv@ is accessible from the global context, or
-- 
-- * there is no context @v@ that is accessible from @pv@ and also
--   from the global context.
---------------------------------------------------------------------------
pdrsIsFreePVar :: PVar -> PDRS -> Bool
pdrsIsFreePVar pv p
  | pv == pdrsLabel p = False
  | otherwise         = path pg (pdrsLabel p) pv || not(any pathBack (vertices pg))
  where pg = projectionGraph p
        pathBack :: PVar -> Bool
        pathBack v = path pg pv v && path pg (pdrsLabel p) v

---------------------------------------------------------------------------
-- | Returns whether a pointer @p@ in local PDRS @lp@ is bound by a 
-- label in the global PDRS @gp@, where:
-- 
-- [@pdrsBoundPVar p lp gp@ /iff/]
--
-- * @p@ is equal to the label of either @lp@ or @gp@; or
-- 
-- * there exists a PDRS @p@ with label @pv@, such that @p@ is a subPDRS
--   of @gp@ and @p@ is accessible from @lp@.
--
--Note the correspondence to drsBoundRef.
---------------------------------------------------------------------------
pdrsBoundPVar :: PVar -> PDRS -> PDRS -> Bool
pdrsBoundPVar _ _ (LambdaPDRS _)      = False
pdrsBoundPVar pv lp (AMerge p1 p2)    = pdrsBoundPVar pv lp p1 || pdrsBoundPVar pv lp p2
pdrsBoundPVar pv lp (PMerge p1 p2)    = pdrsBoundPVar pv lp p1 || pdrsBoundPVar pv lp p2
pdrsBoundPVar pv lp gp@(PDRS l _ _ c) = pv == pdrsLabel lp || pv == l || any bound c
  where bound :: PCon -> Bool
        bound (PCon _ (Rel _ _))    = False
        bound (PCon _ (Neg p1))     = isSubPDRS lp p1 && pdrsBoundPVar pv lp p1
        bound (PCon _ (Imp p1 p2))  = pv == pdrsLabel p1 && isSubPDRS lp p2
          ||  isSubPDRS lp p1 && pdrsBoundPVar pv lp p1
          ||  isSubPDRS lp p2 && pdrsBoundPVar pv lp p2
        bound (PCon _ (Or p1 p2))   = pv == pdrsLabel p1 && isSubPDRS lp p2
          ||  isSubPDRS lp p1 && pdrsBoundPVar pv lp p1
          ||  isSubPDRS lp p2 && pdrsBoundPVar pv lp p2
        bound (PCon _ (Prop _ p1))  = isSubPDRS lp p1 && pdrsBoundPVar pv lp p1
        bound (PCon _ (Diamond p1)) = isSubPDRS lp p1 && pdrsBoundPVar pv lp p1
        bound (PCon _ (Box p1))     = isSubPDRS lp p1 && pdrsBoundPVar pv lp p1

---------------------------------------------------------------------------
-- | Returns the list of all free 'PRef's in a 'PDRS'
---------------------------------------------------------------------------
pdrsFreePRefs :: PDRS -> PDRS -> [PRef]
pdrsFreePRefs (LambdaPDRS _) _     = []
pdrsFreePRefs (AMerge p1 p2) gp    = pdrsFreePRefs p1 gp `union` pdrsFreePRefs p2 gp
pdrsFreePRefs (PMerge p1 p2) gp    = pdrsFreePRefs p1 gp `union` pdrsFreePRefs p2 gp
pdrsFreePRefs lp@(PDRS _ _ u c) gp = free c
  where freePRefs :: [PRef] -> [PRef]
        freePRefs prs = snd (partition (flip (`pdrsBoundPRef` lp) gp) prs)
        free :: [PCon] -> [PRef]
        free []                       = []
        free (PCon p (Rel _ d):cs)    = freePRefs (map (PRef p) d)                       `union` free cs
        free (PCon _ (Neg p1):cs)     = pdrsFreePRefs p1 gp                              `union` free cs
        free (PCon _ (Imp p1 p2):cs)  = pdrsFreePRefs p1 gp  `union` pdrsFreePRefs p2 gp `union` free cs
        free (PCon _ (Or p1 p2):cs)   = pdrsFreePRefs p1 gp  `union` pdrsFreePRefs p2 gp `union` free cs
        free (PCon p (Prop r p1):cs)  = freePRefs [PRef p r] `union` pdrsFreePRefs p1 gp `union` free cs
        free (PCon _ (Diamond p1):cs) = pdrsFreePRefs p1 gp                              `union` free cs
        free (PCon _ (Box p1):cs)     = pdrsFreePRefs p1 gp                              `union` free cs

---------------------------------------------------------------------------
-- | Returns the list of all free 'PVar's in a 'PDRS' @lp@, which is a
-- sub'PDRS' of global 'PDRS' @gp@
---------------------------------------------------------------------------
pdrsFreePVars :: PDRS -> PDRS-> [PVar]
pdrsFreePVars (LambdaPDRS _) _     = []
pdrsFreePVars (AMerge p1 p2) gp    = pdrsFreePVars p1 gp `union` pdrsFreePVars p2 gp
pdrsFreePVars (PMerge p1 p2) gp    = pdrsFreePVars p1 gp `union` pdrsFreePVars p2 gp
pdrsFreePVars lp@(PDRS _ m u c) gp = freePVars (concatMap (\(x,y) -> [x,y]) m) `union` freePVars (map (\(PRef p _) -> p) u) `union` free c
  where freePVars :: [PVar] -> [PVar]
        freePVars ps = snd (partition (flip (`pdrsBoundPVar` lp) gp) ps)
        free :: [PCon] -> [PVar]
        free [] = []
        free (PCon p (Rel _ _):cs)    = freePVars [p] `union` free cs
        free (PCon p (Neg p1):cs)     = freePVars [p] `union` pdrsFreePVars p1 gp `union` free cs
        free (PCon p (Imp p1 p2):cs)  = freePVars [p] `union` pdrsFreePVars p1 gp `union` pdrsFreePVars p2 gp `union` free cs
        free (PCon p (Or p1 p2):cs)   = freePVars [p] `union` pdrsFreePVars p1 gp `union` pdrsFreePVars p2 gp `union` free cs
        free (PCon p (Prop _ p1):cs)  = freePVars [p] `union` pdrsFreePVars p1 gp `union` free cs
        free (PCon p (Diamond p1):cs) = freePVars [p] `union` pdrsFreePVars p1 gp `union` free cs
        free (PCon p (Box p1):cs)     = freePVars [p] `union` pdrsFreePVars p1 gp `union` free cs


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
, pdrsPBoundPRef
, pdrsIsFreePVar
, pdrsFreePRefs
, pdrsFreePRefs2
, pdrsFreePVars
) where

import Data.PDRS.DataType
import Data.PDRS.ProjectionGraph
import Data.PDRS.Structure
import Data.PDRS.Variables
import Data.List ((\\), delete, partition, union)

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
  | pdrsLabel lp `elem` vs && p `elem` vs = bound vs
  | otherwise                             = False
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

-- | Returns whether a referent is bound by some other referent
-- than itself.
pdrsPBoundPRef :: PRef -> PDRS -> PDRS -> Bool
pdrsPBoundPRef pr lp gp = any (flip (pdrsPRefBoundByPRef pr lp) gp) (delete pr (pdrsUniverses gp))

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
  | pv == pdrsLabel p        = False
  | pv `notElem` vertices pg = True
  | otherwise                = path pg (pdrsLabel p) pv || not(any pathBack (vertices pg))
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
        bound (PCon _ (Or p1 p2))   = isSubPDRS lp p1 && pdrsBoundPVar pv lp p1
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

---------------------------------------------------------------------------
-- | XXX Playing around
---------------------------------------------------------------------------
pdrsFreePRefs2 :: PDRS -> [PRef]
pdrsFreePRefs2 p = filter (`notElem` posBound [] [] p) (posFree p)
  where posFree :: PDRS -> [PRef]
        posFree (LambdaPDRS _)    = []
        posFree (AMerge p1 p2)    = posFree p1 `union` posFree p2
        posFree (PMerge p1 p2)    = posFree p1 `union` posFree p2
        posFree lp@(PDRS _ _ _ c) = concatMap free c
          where free :: PCon -> [PRef]
                free (PCon p (Rel _ d))    = (map (PRef p) d)
                free (PCon _ (Neg p1))     = posFree p1
                free (PCon _ (Imp p1 p2))  = posFree p1 `union` posFree p2
                free (PCon _ (Or p1 p2))   = posFree p1 `union` posFree p2
                free (PCon p (Prop r p1))  = [PRef p r] `union` posFree p1
                free (PCon _ (Diamond p1)) = posFree p1
                free (PCon _ (Box p1))     = posFree p1
        posBound :: [PRef] -> [MAP]-> PDRS -> [PRef]
        posBound prs _ (LambdaPDRS _)   = prs
        posBound prs mps (AMerge p1 p2) = posBound prs mps p1 `union` posBound prs mps p2
        posBound prs mps (PMerge p1 p2) = posBound prs mps p1 `union` posBound prs mps p2
        posBound prs mps (PDRS l m u c) = prs' `union` lprs `union` concatMap (boundm prs') mps' `union` cprs
          where prs' = prs `union` u
                mps' = mps `union` m
                lprs = map (\(PRef _ r) ->  (PRef l r)) prs'
                boundm :: [PRef] -> MAP -> [PRef]
                boundm [] m   = []
                boundm (PRef p r:rs) m'@(p1,p2)
                  | p == p2   = (PRef p1 r):boundm rs m'
                  | otherwise = boundm rs m'
                cprs = concatMap (boundc prs' mps') (fst accs) `union` concatMap (boundc [] mps') (snd accs)
                accs = partition (\(PCon p _) -> p == l || acc p l mps') c
                  where acc :: PVar -> PVar -> [MAP] -> Bool
                        acc p p' t = any ((==p') . snd) pts || any (\p'' -> acc p'' p' t) (map snd pts)
                          where pts = (filter ((==p) . fst) t)
                boundc :: [PRef] -> [MAP] -> PCon -> [PRef]
                boundc _  _  (PCon _ (Rel _ _))    = []
                boundc rs ms (PCon _ (Neg p1))     = posBound rs ms p1
                boundc rs ms (PCon _ (Imp p1 p2))  = posBound (posBound rs ms p1) (ms `union` getMAPs p1) p2
                boundc rs ms (PCon _ (Or p1 p2))   = posBound rs ms p1 `union` posBound rs ms p2
                boundc rs ms (PCon _ (Prop _ p1))  = posBound rs ms p1
                boundc rs ms (PCon _ (Diamond p1)) = posBound rs ms p1
                boundc rs ms (PCon _ (Box p1))     = posBound rs ms p1

-- move to variables?
getMAPs :: PDRS -> [MAP]
getMAPs (LambdaPDRS _) = []
getMAPs (AMerge p1 p2) = getMAPs p1 `union` getMAPs p2
getMAPs (PMerge p1 p2) = getMAPs p1 `union` getMAPs p2
getMAPs (PDRS _ m _ c) = m `union` concatMap maps c
  where maps :: PCon -> [MAP]
        maps (PCon _ (Rel _ _))    = []
        maps (PCon _ (Neg p1))     = getMAPs p1
        maps (PCon _ (Imp p1 p2))  = getMAPs p1 `union` getMAPs p2
        maps (PCon _ (Or p1 p2))   = getMAPs p1 `union` getMAPs p2
        maps (PCon _ (Prop _ p1))  = getMAPs p1
        maps (PCon _ (Diamond p1)) = getMAPs p1
        maps (PCon _ (Box p1))     = getMAPs p1


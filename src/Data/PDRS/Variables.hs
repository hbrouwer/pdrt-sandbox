{- |
Module      :  Data.PDRS.Variables
Copyright   :  (c) Harm Brouwer and Noortje Venhuizen
License     :  Apache-2.0

Maintainer  :  me@hbrouwer.eu, n.j.venhuizen@rug.nl
Stability   :  provisional
Portability :  portable

PDRS variables
-}

module Data.PDRS.Variables
(
-- * Conversion
  pdrsRefToDRSRef
, drsRefToPDRSRef
, pdrsRefToPRef
, prefToPDRSRef
, prefToPVar
-- * Binding
, pdrsBoundPRef
, pdrsBoundPVar
, pdrsPRefBoundByPRef
, pdrsIsAccessibleContext
, pdrsIsFreePVar
-- * Variable Collections
, pdrsUniverses
, pdrsVariables
, pdrsFreePRefs
, pdrsPVars
, pdrsFreePVars
, pdrsLambdas
-- * New Variables
, newPVars
, newPDRSRefs
, newPRefs
) where

import Data.DRS.Structure (DRSRef (..))
import Data.DRS.Variables (newDRSRefs)
import Data.PDRS.ProjectionGraph
import Data.PDRS.Structure

import Data.List (partition, sortBy, union)
import Data.Ord (comparing)

---------------------------------------------------------------------------
-- * Exported
---------------------------------------------------------------------------

---------------------------------------------------------------------------
-- ** Conversion
---------------------------------------------------------------------------

---------------------------------------------------------------------------
-- | Converts a 'PDRSRef' into a 'DRSRef'
---------------------------------------------------------------------------
pdrsRefToDRSRef :: PDRSRef -> DRSRef
pdrsRefToDRSRef (LambdaPDRSRef lt) = LambdaDRSRef lt
pdrsRefToDRSRef (PDRSRef r)        = DRSRef r

---------------------------------------------------------------------------
-- | Converts a 'DRSRef' to a 'PDRSRef'
---------------------------------------------------------------------------
drsRefToPDRSRef :: DRSRef -> PDRSRef
drsRefToPDRSRef (LambdaDRSRef lt) = LambdaPDRSRef lt
drsRefToPDRSRef (DRSRef r)        = PDRSRef r

---------------------------------------------------------------------------
-- | Converts a 'PDRSRef' with a 'PVar' into a 'PRef'
---------------------------------------------------------------------------
pdrsRefToPRef :: PDRSRef -> PVar -> PRef
pdrsRefToPRef pr pv = PRef pv pr

---------------------------------------------------------------------------
-- | Converts a 'PRef' into a 'PDRSRef'
---------------------------------------------------------------------------
prefToPDRSRef :: PRef -> PDRSRef 
prefToPDRSRef (PRef _ pr) = pr

---------------------------------------------------------------------------
-- | Converts a 'PRef' into a 'PVar'
---------------------------------------------------------------------------
prefToPVar :: PRef -> PVar
prefToPVar (PRef pv _) = pv

---------------------------------------------------------------------------
-- ** Binding
---------------------------------------------------------------------------

---------------------------------------------------------------------------
-- | Returns whether 'PRef' @pr@ in context $lp$ is bound in the 'PDRS'
-- @gp@, where:
--
-- [@pdrsBoundRef2 pr lp gp@ /iff/]
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
  | p `elem` vs = bound vs
  | otherwise   = False
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
-- [@boundByPRef pr lp pr' pdrs@ /iff/]
--
--  (1) @pr1@ and @pr2@ share the same referent; and
--  
--  2. @pr2@ is part of some universe in @pdrs@ (i.e., can bind referents); and
--  
--  3. The interpretation site of @pr2@ is accessible from both the
--    introduction and interpretation site of @pr1@.
---------------------------------------------------------------------------
pdrsPRefBoundByPRef :: PRef -> PDRS -> PRef -> PDRS -> Bool
pdrsPRefBoundByPRef (PRef p1 r1) lp1 pr2@(PRef p2 r2) lp2 =
  r1 == r2
  && pr2 `elem` pdrsUniverses lp2
  && pdrsIsAccessibleContext p1 p2 lp2
  && pdrsIsAccessibleContext (pdrsLabel lp1) p2 lp2

---------------------------------------------------------------------------
-- | Returns whether 'PDRS' context @p2@ is accessible from 'PDRS' 
-- context @p1@ in PDRS @p@
---------------------------------------------------------------------------
pdrsIsAccessibleContext :: PVar -> PVar -> PDRS -> Bool
pdrsIsAccessibleContext p1 p2 p 
  | p1 `notElem` vs || p2 `notElem` vs = False
  | path pg p1 p2                      = True
  | otherwise                          = False
  where pg = projectionGraph p
        vs = vertices pg

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
-- label in the global PDRS $gp$, where:
-- 
-- [@pdrsBoundPVar p lp gp@ /iff/]
--
-- * @p@ is equal to the label of either @lp@ or @gp@; or
-- 
-- * there exists a PDRS @p@ with label @pv@, such that @p@ is a subPDRS
--   of @gp@ and @lp@ is a subPDRS of @p@.
--
--Note the correspondence to drsBoundRef.
---------------------------------------------------------------------------
pdrsBoundPVar :: PVar -> PDRS -> PDRS -> Bool
pdrsBoundPVar _ _ (LambdaPDRS _) = False
pdrsBoundPVar pv lp (AMerge p1 p2) = pdrsBoundPVar pv lp p1 || pdrsBoundPVar pv lp p2
pdrsBoundPVar pv lp (PMerge p1 p2) = pdrsBoundPVar pv lp p1 || pdrsBoundPVar pv lp p2
pdrsBoundPVar pv lp gp@(PDRS l _ _ c)
  | pv == pdrsLabel lp     = True
  | pv == l                = True
  | isBoundByLabel pv lp c = True
  | otherwise              = False
  where isBoundByLabel :: PVar -> PDRS -> [PCon] -> Bool
        isBoundByLabel pv lp = any bound
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
-- ** Variable Collections
---------------------------------------------------------------------------

---------------------------------------------------------------------------
-- | Returns the list of projected referents in all universes of a 'PDRS'.
---------------------------------------------------------------------------
pdrsUniverses :: PDRS -> [PRef]
pdrsUniverses (LambdaPDRS _) = []
pdrsUniverses (AMerge p1 p2) = pdrsUniverses p1 `union` pdrsUniverses p2
pdrsUniverses (PMerge p1 p2) = pdrsUniverses p1 `union` pdrsUniverses p2
pdrsUniverses (PDRS _ _ u c) = u `union` universes c
  where universes :: [PCon] -> [PRef]
        universes []                       = []
        universes (PCon _ (Rel _ _):cs)    = universes cs
        universes (PCon _ (Neg p1):cs)     = pdrsUniverses p1 `union` universes cs
        universes (PCon _ (Imp p1 p2):cs)  = pdrsUniverses p1 `union` pdrsUniverses p2 `union` universes cs
        universes (PCon _ (Or p1 p2):cs)   = pdrsUniverses p1 `union` pdrsUniverses p2 `union` universes cs
        universes (PCon _ (Prop _ p1):cs)  = pdrsUniverses p1 `union` universes cs
        universes (PCon _ (Diamond p1):cs) = pdrsUniverses p1 `union` universes cs
        universes (PCon _ (Box p1):cs)     = pdrsUniverses p1 `union` universes cs

---------------------------------------------------------------------------
-- | Returns the list of all variables in a 'PDRS'
---------------------------------------------------------------------------
pdrsVariables :: PDRS -> [PDRSRef]
pdrsVariables (LambdaPDRS _) = []
pdrsVariables (AMerge p1 p2) = pdrsVariables p1         `union` pdrsVariables p2
pdrsVariables (PMerge p1 p2) = pdrsVariables p1         `union` pdrsVariables p2
pdrsVariables (PDRS _ _ u c) = map (\(PRef _ r) -> r) u `union` variables c
  where variables :: [PCon] -> [PDRSRef]
        variables []                       = []
        variables (PCon _ (Rel _ d):cs)    = d `union` variables cs
        variables (PCon _ (Neg p1):cs)     = pdrsVariables p1 `union` variables cs
        variables (PCon _ (Imp p1 p2):cs)  = pdrsVariables p1 `union` pdrsVariables p2 `union` variables cs
        variables (PCon _ (Or p1 p2):cs)   = pdrsVariables p1 `union` pdrsVariables p2 `union` variables cs
        variables (PCon _ (Prop r p1):cs)  = [r]              `union` pdrsVariables p1 `union` variables cs
        variables (PCon _ (Diamond p1):cs) = pdrsVariables p1 `union` variables cs
        variables (PCon _ (Box p1):cs)     = pdrsVariables p1 `union` variables cs

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
        free (PCon p (Rel _ d):cs)    = freePRefs (map (`pdrsRefToPRef` p) d)            `union` free cs
        free (PCon _ (Neg p1):cs)     = pdrsFreePRefs p1 gp                              `union` free cs
        free (PCon _ (Imp p1 p2):cs)  = pdrsFreePRefs p1 gp  `union` pdrsFreePRefs p2 gp `union` free cs
        free (PCon _ (Or p1 p2):cs)   = pdrsFreePRefs p1 gp  `union` pdrsFreePRefs p2 gp `union` free cs
        free (PCon p (Prop r p1):cs)  = freePRefs [PRef p r] `union` pdrsFreePRefs p1 gp `union` free cs
        free (PCon _ (Diamond p1):cs) = pdrsFreePRefs p1 gp                              `union` free cs
        free (PCon _ (Box p1):cs)     = pdrsFreePRefs p1 gp                              `union` free cs

---------------------------------------------------------------------------
-- | Returns the list of all 'PVar's in a 'PDRS'
---------------------------------------------------------------------------
pdrsPVars :: PDRS -> [PVar]
pdrsPVars p = vertices (projectionGraph p)

---------------------------------------------------------------------------
-- | Returns the list of all free 'PVar's in a 'PDRS' @lp@, which is a
-- sub'PDRS' of global 'PDRS' @gp@
---------------------------------------------------------------------------
pdrsFreePVars :: PDRS -> PDRS-> [PVar]
pdrsFreePVars (LambdaPDRS _) _     = []
pdrsFreePVars (AMerge p1 p2) gp    = pdrsFreePVars p1 gp `union` pdrsFreePVars p2 gp
pdrsFreePVars (PMerge p1 p2) gp    = pdrsFreePVars p1 gp `union` pdrsFreePVars p2 gp
pdrsFreePVars lp@(PDRS _ m u c) gp = freePVars (concatMap (\(x,y) -> [x,y]) m) `union` freePVars (map prefToPVar u) `union` free c
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
-- | Returns the list of all lambda variables in a 'PDRS'
---------------------------------------------------------------------------
pdrsLambdas :: PDRS -> [DRSVar]
pdrsLambdas p = map fst (sortBy (comparing snd) (lambdas p))

---------------------------------------------------------------------------
-- ** New Variables
---------------------------------------------------------------------------

---------------------------------------------------------------------------
-- | Returns a list of new projection variables for a list of old
-- 'PVar's @opvs@, based on a list of existing 'PVar's @epvs@.
---------------------------------------------------------------------------
newPVars :: [PVar] -> [PVar] -> [PVar]
newPVars opvs []   = opvs
newPVars opvs epvs = take (length opvs) [(maximum epvs + 1)..]

---------------------------------------------------------------------------
-- | Returns a list of new referents for a list of old 'PDRSRef's @ors@,
-- based on a list of existing 'PDRSRef's @ers@.
---------------------------------------------------------------------------
newPDRSRefs :: [PDRSRef] -> [PDRSRef] -> [PDRSRef]
newPDRSRefs ors []  = ors
newPDRSRefs ors ers = map drsRefToPDRSRef (newDRSRefs (map pdrsRefToDRSRef ors) (map pdrsRefToDRSRef ers))

---------------------------------------------------------------------------
-- | Returns a list of new projected referents for a list of old 'PRef's,
-- based on a list of existing 'PVar's @eps@ and existing 'PDRSRef's @ers@.
---------------------------------------------------------------------------
newPRefs :: [PRef] -> [PDRSRef] -> [PRef]
newPRefs prs ers = packPRefs ps (newPDRSRefs rs ers)
  where (ps,rs) = unpackPRefs prs ([],[])
        unpackPRefs :: [PRef] -> ([PVar],[PDRSRef]) -> ([PVar],[PDRSRef])
        unpackPRefs [] uprs                 = uprs
        unpackPRefs (PRef p r:prs) (pvs,rs) = unpackPRefs prs (pvs ++ [p],rs ++ [r])
        packPRefs :: [PVar] -> [PDRSRef] -> [PRef]
        packPRefs [] []           = []
        packPRefs (pv:pvs) (r:rs) = PRef pv r : packPRefs pvs rs

---------------------------------------------------------------------------
-- * Private
---------------------------------------------------------------------------

---------------------------------------------------------------------------
-- | Returns the list of all lambda tuples in a 'PDRS'
---------------------------------------------------------------------------
lambdas :: PDRS -> [(DRSVar,Int)]
lambdas (LambdaPDRS lt) = [lt]
lambdas (AMerge p1 p2)  = lambdas p1     `union` lambdas p2
lambdas (PMerge p1 p2)  = lambdas p1     `union` lambdas p2
lambdas (PDRS _ _ u c)  = lambdasPRefs u `union` lambdasPCons c

---------------------------------------------------------------------------
-- | Returns the list of all lamba tuples in a 'PDRS' universe
---------------------------------------------------------------------------
lambdasPRefs :: [PRef] -> [(DRSVar,Int)]
lambdasPRefs ps = lambdasRefs (map (\(PRef _ r) -> r) ps)

---------------------------------------------------------------------------
-- | Returns the list of all lambda tuples in a list of 'PDRSRef's
---------------------------------------------------------------------------
lambdasRefs :: [PDRSRef] -> [(DRSVar,Int)]
lambdasRefs []                    = []
lambdasRefs (LambdaPDRSRef lt:ps) = lt : lambdasRefs ps
lambdasRefs (PDRSRef{}:ps)        = lambdasRefs ps

---------------------------------------------------------------------------
-- | Returns the list of all lambda tuples in a list of 'PDRSCon's
---------------------------------------------------------------------------
lambdasPCons :: [PCon] -> [(DRSVar,Int)]
lambdasPCons []                       = []
lambdasPCons (PCon _ (Rel _ d):cs)    = lambdasRefs d   `union` lambdasPCons cs
lambdasPCons (PCon _ (Neg p1):cs)     = lambdas p1      `union` lambdasPCons cs
lambdasPCons (PCon _ (Imp p1 p2):cs)  = lambdas p1      `union` lambdas p2 `union` lambdasPCons cs
lambdasPCons (PCon _ (Or p1 p2):cs)   = lambdas p1      `union` lambdas p2 `union` lambdasPCons cs
lambdasPCons (PCon p (Prop r p1):cs)  = lambdasRefs [r] `union` lambdas p1 `union` lambdasPCons cs
lambdasPCons (PCon _ (Diamond p1):cs) = lambdas p1      `union` lambdasPCons cs
lambdasPCons (PCon _ (Box p1):cs)     = lambdas p1      `union` lambdasPCons cs


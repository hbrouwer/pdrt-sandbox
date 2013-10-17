{- |
Module      :  Data.PDRS.Variables
Copyright   :  (c) Harm Brouwer and Noortje Venhuizen
License     :  Apache-2.0

Maintainer  :  me@hbrouwer.eu
Stability   :  provisional
Portability :  portable

PDRS variables
-}

module Data.PDRS.Variables
(
  pdrsRefToDRSRef
, drsRefToPDRSRef
, pdrsRefToPRef
, prefToPDRSRef
, prefToPVar
, pdrsUniverse
, pdrsUniverses
, pdrsVariables
, pdrsPVars
, pdrsLambdas
, pdrsBoundPRef
, pdrsBoundPVar
, pdrsPRefBoundByPRef
, pdrsIsAccessibleContext
, pdrsIsFreePVar
, newPVars
, newPDRSRefs
, newPRefs
) where

import Data.DRS.Structure (DRSRef (..))
import Data.DRS.Variables (newDRSRefs)
import Data.PDRS.ProjectionGraph
import Data.PDRS.Structure

import Data.List (sortBy, union)
import Data.Ord (comparing)

-- | Converts a PDRS referent to a DRS referent
pdrsRefToDRSRef :: PDRSRef -> DRSRef
pdrsRefToDRSRef (LambdaPDRSRef lt) = LambdaDRSRef lt
pdrsRefToDRSRef (PDRSRef r)        = DRSRef r

-- | Converts a DRS referent to a PDRS referent
drsRefToPDRSRef :: DRSRef -> PDRSRef
drsRefToPDRSRef (LambdaDRSRef lt) = LambdaPDRSRef lt
drsRefToPDRSRef (DRSRef r)        = PDRSRef r

pdrsRefToPRef :: PDRSRef -> PVar -> PRef
pdrsRefToPRef pr pv = PRef pv pr

prefToPDRSRef :: PRef -> PDRSRef 
prefToPDRSRef (PRef _ pr) = pr

prefToPVar :: PRef -> PVar
prefToPVar (PRef pv _) = pv

-- | Returns the universe of a PDRS
pdrsUniverse :: PDRS -> [PRef]
pdrsUniverse (LambdaPDRS _) = []
pdrsUniverse (AMerge p1 p2) = pdrsUniverse p1 `union` pdrsUniverse p2
pdrsUniverse (PMerge p1 p2) = pdrsUniverse p1 `union` pdrsUniverse p2
pdrsUniverse (PDRS _ _ u _) = u

-- | Returns the list of all projected universes in a PDRS
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

-- | Returns the list of all variables in a PDRS
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

-- | Returns the list of all projection variables in a PDRS
pdrsPVars :: PDRS -> [PVar]
pdrsPVars p = vertices (projectionGraph p)

-- | Returns the list of all lambda variables in a PDRS
pdrsLambdas :: PDRS -> [DRSVar]
pdrsLambdas p = map fst (sortBy (comparing snd) (lambdas p))

-- | Returns the list of all lambda tuples in a PDRS
lambdas :: PDRS -> [(DRSVar,Int)]
lambdas (LambdaPDRS lt) = [lt]
lambdas (AMerge p1 p2)  = lambdas p1     `union` lambdas p2
lambdas (PMerge p1 p2)  = lambdas p1     `union` lambdas p2
lambdas (PDRS _ _ u c)  = lambdasPRefs u `union` lambdasPCons c

-- | Returns the list of all lamba tuples in a PDRS universe
lambdasPRefs :: [PRef] -> [(DRSVar,Int)]
lambdasPRefs ps = lambdasRefs (map (\(PRef _ r) -> r) ps)

-- | Returns the list of all lambda tuples in a list of PDRS referents
lambdasRefs :: [PDRSRef] -> [(DRSVar,Int)]
lambdasRefs []                    = []
lambdasRefs (LambdaPDRSRef lt:ps) = lt : lambdasRefs ps
lambdasRefs (PDRSRef{}:ps)        = lambdasRefs ps

-- | Returns the list of all lambda tuples in a list of PDRS conditions
lambdasPCons :: [PCon] -> [(DRSVar,Int)]
lambdasPCons []                       = []
lambdasPCons (PCon _ (Rel _ d):cs)    = lambdasRefs d   `union` lambdasPCons cs
lambdasPCons (PCon _ (Neg p1):cs)     = lambdas p1      `union` lambdasPCons cs
lambdasPCons (PCon _ (Imp p1 p2):cs)  = lambdas p1      `union` lambdas p2 `union` lambdasPCons cs
lambdasPCons (PCon _ (Or p1 p2):cs)   = lambdas p1      `union` lambdas p2 `union` lambdasPCons cs
lambdasPCons (PCon p (Prop r p1):cs)  = lambdasRefs [r] `union` lambdas p1 `union` lambdasPCons cs
lambdasPCons (PCon _ (Diamond p1):cs) = lambdas p1      `union` lambdasPCons cs
lambdasPCons (PCon _ (Box p1):cs)     = lambdas p1      `union` lambdasPCons cs

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

pdrsPRefBoundByPRef :: PRef -> PDRS -> PRef -> PDRS -> Bool
pdrsPRefBoundByPRef (PRef p1 r1) lp1 pr2@(PRef p2 r2) lp2 =
  r1 == r2
  && pr2 `elem` pdrsUniverses lp2
  && pdrsIsAccessibleContext p1 p2 lp2
  && pdrsIsAccessibleContext (pdrsLabel lp1) p2 lp2

-- | Returns whether PDRS context @p2@ is accessible from PDRS context @p1@
-- in PDRS @p@
pdrsIsAccessibleContext :: PVar -> PVar -> PDRS -> Bool
pdrsIsAccessibleContext p1 p2 p 
  | p1 `notElem` vs || p2 `notElem` vs = False
  | path pg p1 p2                      = True
  | otherwise                          = False
  where pg = projectionGraph p
        vs = vertices pg

pdrsIsFreePVar :: PVar -> PDRS -> Bool
pdrsIsFreePVar pv p
  | pv == pdrsLabel p = False
  | otherwise         = path pg (pdrsLabel p) pv || not(any pathBack (vertices pg))
  where pg = projectionGraph p
        pathBack :: PVar -> Bool
        pathBack v = path pg pv v && path pg (pdrsLabel p) v
 
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

newPVars :: [PVar] -> [PVar] -> [PVar]
newPVars opvs []   = opvs
newPVars opvs epvs = take (length opvs) [(maximum epvs + 1)..]

newPDRSRefs :: [PDRSRef] -> [PDRSRef] -> [PDRSRef]
newPDRSRefs ors []  = ors
newPDRSRefs ors ers = map drsRefToPDRSRef (newDRSRefs (map pdrsRefToDRSRef ors) (map pdrsRefToDRSRef ers))

newPRefs :: [PRef] -> [PDRSRef] -> [PRef]
newPRefs prs ers = packPRefs ps (newPDRSRefs rs ers)
  where (ps,rs) = unpackPRefs prs ([],[])
        unpackPRefs :: [PRef] -> ([PVar],[PDRSRef]) -> ([PVar],[PDRSRef])
        unpackPRefs [] uprs                 = uprs
        unpackPRefs (PRef p r:prs) (pvs,rs) = unpackPRefs prs (pvs ++ [p],rs ++ [r])
        packPRefs :: [PVar] -> [PDRSRef] -> [PRef]
        packPRefs [] []           = []
        packPRefs (pv:pvs) (r:rs) = PRef pv r : packPRefs pvs rs

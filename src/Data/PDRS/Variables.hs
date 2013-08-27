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
, pdrsUniverse
, pdrsPReferents
, pdrsVariables
, pdrsPVars
, pdrsAssertedPVars
, pdrsAssertedPDRSRefs
, pdrsLambdas
, pdrsBoundRef
, pdrsIsAccessibleContext
, pdrsIsFreePVar
) where

import Data.DRS.Structure (DRSRef (..))
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

-- | Returns the universe of a PDRS
pdrsUniverse :: PDRS -> [PRef]
pdrsUniverse (LambdaPDRS _) = []
pdrsUniverse (AMerge p1 p2) = pdrsUniverse p1 `union` pdrsUniverse p2
pdrsUniverse (PMerge p1 p2) = pdrsUniverse p1 `union` pdrsUniverse p2
pdrsUniverse (PDRS _ _ u _) = u

-- | Returns the list of all projected referents in a PDRS
pdrsPReferents :: PDRS -> [PRef]
pdrsPReferents (LambdaPDRS _) = []
pdrsPReferents (AMerge p1 p2) = pdrsPReferents p1 `union` pdrsPReferents p2
pdrsPReferents (PMerge p1 p2) = pdrsPReferents p1 `union` pdrsPReferents p2
pdrsPReferents (PDRS _ _ u c) = u `union` preferents c
  where preferents :: [PCon] -> [PRef]
        preferents []                       = []
        preferents (PCon _ (Rel _ _):cs)    = preferents cs
        preferents (PCon _ (Neg p1):cs)     = pdrsPReferents p1 `union` preferents cs
        preferents (PCon _ (Imp p1 p2):cs)  = pdrsPReferents p1 `union` pdrsPReferents p2 `union` preferents cs
        preferents (PCon _ (Or p1 p2):cs)   = pdrsPReferents p1 `union` pdrsPReferents p2 `union` preferents cs
        preferents (PCon _ (Prop _ p1):cs)  = pdrsPReferents p1 `union` preferents cs
        preferents (PCon _ (Diamond p1):cs) = pdrsPReferents p1 `union` preferents cs
        preferents (PCon _ (Box p1):cs)     = pdrsPReferents p1 `union` preferents cs

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

-- | Returns the list of all asserted projection variables in a PDRS
pdrsAssertedPVars :: PDRS -> [PVar]
pdrsAssertedPVars p = assertedPVars p (pdrsPVars p)
  where assertedPVars :: PDRS -> [PVar] -> [PVar]
        assertedPVars _ []               = []
        assertedPVars (LambdaPDRS _) _   = []
        assertedPVars (AMerge p1 p2) pvs = assertedPVars p1 pvs `union` assertedPVars p2 pvs
        assertedPVars (PMerge _  p2) pvs = assertedPVars p2 pvs
        assertedPVars (PDRS l _ _ _) (pv:pvs)
          | isAsserted = pv : assertedPVars p pvs
          | otherwise  = assertedPVars p pvs
          where isAsserted = l == pv || (pdrsIsAccessibleContext pv l p && not(pdrsIsAccessibleContext l pv p))

-- | Returns the list of all asserted PDRS referents in a PDRS
pdrsAssertedPDRSRefs :: PDRS -> [PDRSRef]
pdrsAssertedPDRSRefs p = assertedPDRSRefs p (pdrsAssertedPVars p)
  where assertedPDRSRefs :: PDRS -> [PVar] -> [PDRSRef]
        assertedPDRSRefs (LambdaPDRS _) _   = []
        assertedPDRSRefs (AMerge p1 p2) pvs = assertedPDRSRefs p1 pvs `union` assertedPDRSRefs p2 pvs
        assertedPDRSRefs (PMerge _  p2) pvs = assertedPDRSRefs p2 pvs
        assertedPDRSRefs (PDRS _ _ u c) pvs = arefs u          `union` arefsInCons c
          where arefs :: [PRef] -> [PDRSRef]
                arefs u = map (\(PRef _ r) -> r) (filter (\(PRef p _) -> p `elem` pvs) u)
                arefsInCons :: [PCon] -> [PDRSRef]
                arefsInCons []                       = []
                arefsInCons (PCon _ (Rel _ _):cs)    = arefsInCons cs
                arefsInCons (PCon _ (Neg p1):cs)     = assertedPDRSRefs p1 pvs `union` arefsInCons cs
                arefsInCons (PCon _ (Imp p1 p2):cs)  = assertedPDRSRefs p1 pvs `union` assertedPDRSRefs p2 pvs `union` arefsInCons cs
                arefsInCons (PCon _ (Or p1 p2):cs)   = assertedPDRSRefs p1 pvs `union` assertedPDRSRefs p2 pvs `union` arefsInCons cs
                arefsInCons (PCon _ (Prop _ p1):cs)  = assertedPDRSRefs p1 pvs `union` arefsInCons cs
                arefsInCons (PCon _ (Diamond p1):cs) = assertedPDRSRefs p1 pvs `union` arefsInCons cs
                arefsInCons (PCon _ (Box p1):cs)     = assertedPDRSRefs p1 pvs `union` arefsInCons cs

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

-- | Returns whether project referent @r@ is bound in the PDRS @p@
pdrsBoundRef :: PRef -> PDRS -> Bool
pdrsBoundRef (PRef p r) p1
  | p `elem` vs = bound vs
  | otherwise   = False
  where pg = projectionGraph p1
        vs = vertices pg
        bound :: [PVar] -> Bool
        bound [] = False
        bound (pv:pvs)
          | path pg p pv = PRef pv r `elem` pdrsPReferents p1 || bound pvs
          | otherwise    = bound pvs

-- | Returns whether PDRS context @p2@ is accessible from PDRS context @p1@
-- in PDRS @p@
pdrsIsAccessibleContext :: PVar -> PVar -> PDRS -> Bool
pdrsIsAccessibleContext p1 p2 p = path (projectionGraph p) p1 p2

-- | Returns whether @pv@ is a free projection variable in PDRS @p@
pdrsIsFreePVar :: PVar -> PDRS -> Bool
pdrsIsFreePVar pv p = path pg (pdrsLabel p) pv || not(any pathBack (vertices pg))
  where pg = projectionGraph p
        pathBack :: PVar -> Bool
        pathBack v
          | path pg pv v && path pg (pdrsLabel p) v = True
          | otherwise                               = False

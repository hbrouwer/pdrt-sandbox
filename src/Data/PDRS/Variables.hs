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
, pdrsRefToDRSVar
, drsRefToPDRSRef
, pdrsRelToDRSRel
, pdrsRelToString
-- * New Variables
, newPVars
, newPDRSRefs
, newPRefs
-- * Variable Collections
, pdrsVariables
, pdrsPVars
, pdrsLambdas
, pdrsLambdaVars
) where

import Data.DRS.DataType (DRSRef (..), DRSRel (..), DRSVar)
import Data.DRS.Variables (drsRefToDRSVar,drsRelToString,newDRSRefs)
import Data.PDRS.DataType
import Data.PDRS.Structure

import Data.List (sortBy, union)
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

-- | Directly converts a 'PDRSRef' into a 'DRSVar'
pdrsRefToDRSVar :: PDRSRef -> DRSVar
pdrsRefToDRSVar = drsRefToDRSVar . pdrsRefToDRSRef

---------------------------------------------------------------------------
-- | Converts a 'DRSRef' to a 'PDRSRef'
---------------------------------------------------------------------------
drsRefToPDRSRef :: DRSRef -> PDRSRef
drsRefToPDRSRef (LambdaDRSRef lt) = LambdaPDRSRef lt
drsRefToPDRSRef (DRSRef r)        = PDRSRef r

---------------------------------------------------------------------------
-- | Converts a 'PDRSRel' into a 'DRSRel'
---------------------------------------------------------------------------
pdrsRelToDRSRel :: PDRSRel -> DRSRel
pdrsRelToDRSRel (LambdaPDRSRel lr) = LambdaDRSRel lr
pdrsRelToDRSRel (PDRSRel r)        = DRSRel r

-- | Directly converts a 'PDRSRel' into a 'String'
pdrsRelToString :: PDRSRel -> String
pdrsRelToString = drsRelToString . pdrsRelToDRSRel

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
-- ** Variable Collections
---------------------------------------------------------------------------

---------------------------------------------------------------------------
-- | Returns the list of all variables in a 'PDRS'
---------------------------------------------------------------------------
pdrsVariables :: PDRS -> [PDRSRef]
pdrsVariables (LambdaPDRS ((_,d),_)) = map PDRSRef d
pdrsVariables (AMerge p1 p2)         = pdrsVariables p1         `union` pdrsVariables p2
pdrsVariables (PMerge p1 p2)         = pdrsVariables p1         `union` pdrsVariables p2
pdrsVariables (PDRS _ _ u c)         = map (\(PRef _ r) -> r) u `union` variables c
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
-- | Returns the list of all 'PVar's in a 'PDRS'
---------------------------------------------------------------------------
pdrsPVars :: PDRS -> [PVar]
pdrsPVars (LambdaPDRS _) = []
pdrsPVars (AMerge p1 p2) = pdrsPVars p1               `union` pdrsPVars p2
pdrsPVars (PMerge p1 p2) = pdrsPVars p1               `union` pdrsPVars p2
pdrsPVars (PDRS l m u c) = l : concatMap (\(x,y) -> [x,y]) m `union` map (\(PRef p _) -> p) u `union` pvars c
  where pvars :: [PCon] -> [PVar]
        pvars []                       = []
        pvars (PCon p (Rel _ _):cs)    = p:pvars cs
        pvars (PCon p (Neg p1):cs)     = p:pdrsPVars p1 `union` pvars cs
        pvars (PCon p (Imp p1 p2):cs)  = p:pdrsPVars p1 `union` pdrsPVars p2 `union` pvars cs
        pvars (PCon p (Or p1 p2):cs)   = p:pdrsPVars p1 `union` pdrsPVars p2 `union` pvars cs
        pvars (PCon p (Prop _ p1):cs)  = p:pdrsPVars p1 `union` pvars cs
        pvars (PCon p (Diamond p1):cs) = p:pdrsPVars p1 `union` pvars cs
        pvars (PCon p (Box p1):cs)     = p:pdrsPVars p1 `union` pvars cs

---------------------------------------------------------------------------
-- | Returns the list of all lambda tuples in a 'PDRS'
---------------------------------------------------------------------------
pdrsLambdas :: PDRS -> [((DRSVar,[DRSVar]),Int)]
pdrsLambdas (LambdaPDRS lt) = [lt]
pdrsLambdas (AMerge p1 p2)  = pdrsLambdas p1 `union` pdrsLambdas p2
pdrsLambdas (PMerge p1 p2)  = pdrsLambdas p1 `union` pdrsLambdas p2
pdrsLambdas (PDRS _ _ u c)  = lamRefs (map (\(PRef _ r) -> r) u) `union` lamPCons c
  where lamRefs :: [PDRSRef] -> [((DRSVar,[DRSVar]),Int)]
        lamRefs []                    = []
        lamRefs (LambdaPDRSRef lt:ps) = lt : lamRefs ps
        lamRefs (PDRSRef{}:ps)        = lamRefs ps
        lamPCons :: [PCon] -> [((DRSVar,[DRSVar]),Int)]
        lamPCons []                       = []
        lamPCons (PCon _ (Rel r d):cs)    = lamRel r       `union` lamRefs d      `union` lamPCons cs
        lamPCons (PCon _ (Neg p1):cs)     = pdrsLambdas p1                        `union` lamPCons cs
        lamPCons (PCon _ (Imp p1 p2):cs)  = pdrsLambdas p1 `union` pdrsLambdas p2 `union` lamPCons cs
        lamPCons (PCon _ (Or p1 p2):cs)   = pdrsLambdas p1 `union` pdrsLambdas p2 `union` lamPCons cs
        lamPCons (PCon p (Prop r p1):cs)  = lamRefs [r]    `union` pdrsLambdas p1 `union` lamPCons cs
        lamPCons (PCon _ (Diamond p1):cs) = pdrsLambdas p1                        `union` lamPCons cs
        lamPCons (PCon _ (Box p1):cs)     = pdrsLambdas p1                        `union` lamPCons cs
        lamRel :: PDRSRel -> [((DRSVar,[DRSVar]),Int)]
        lamRel (LambdaPDRSRel lt) = [lt]
        lamRel (PDRSRel _)        = []

---------------------------------------------------------------------------
-- | Returns the list of all lambda variables in a 'PDRS'
---------------------------------------------------------------------------
pdrsLambdaVars :: PDRS -> [(DRSVar,[DRSVar])]
pdrsLambdaVars p = map fst (sortBy (comparing snd) (pdrsLambdas p))


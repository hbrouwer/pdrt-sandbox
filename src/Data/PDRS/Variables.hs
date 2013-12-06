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
, pdrsRelToDRSRel
-- * New Variables
, newPVars
, newPDRSRefs
, newPRefs
-- * Variable Collections
, pdrsUniverses
, pdrsVariables
, pdrsPVars
, pdrsLambdas
, lambdas --change name!
) where

import Data.DRS.DataType (DRSRef (..), DRSRel (..))
import Data.DRS.Variables (newDRSRefs)
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
-- | Converts a 'PDRSRel' into a 'DRSRel'
---------------------------------------------------------------------------
pdrsRelToDRSRel :: PDRSRel -> DRSRel
pdrsRelToDRSRel (LambdaPDRSRel lr) = LambdaDRSRel lr
pdrsRelToDRSRel (PDRSRel r)        = DRSRel r

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
-- | Returns the list of all 'PVar's in a 'PDRS'
---------------------------------------------------------------------------
pdrsPVars :: PDRS -> [PVar]
pdrsPVars (LambdaPDRS _) = []
pdrsPVars (AMerge p1 p2) = pdrsPVars p1               `union` pdrsPVars p2
pdrsPVars (PMerge p1 p2) = pdrsPVars p1               `union` pdrsPVars p2
pdrsPVars (PDRS l m u c) = l : concatMap (\(x,y) -> [x,y]) m `union` map prefToPVar u `union` pvars c
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
-- | Returns the list of all lambda variables in a 'PDRS'
---------------------------------------------------------------------------
pdrsLambdas :: PDRS -> [(DRSVar,[DRSVar])]
pdrsLambdas p = map fst (sortBy (comparing snd) (lambdas p))

---------------------------------------------------------------------------
-- | Returns the list of all lambda tuples in a 'PDRS'
---------------------------------------------------------------------------
lambdas :: PDRS -> [((DRSVar,[DRSVar]),Int)]
lambdas (LambdaPDRS lt) = [lt]
lambdas (AMerge p1 p2)  = lambdas p1     `union` lambdas p2
lambdas (PMerge p1 p2)  = lambdas p1     `union` lambdas p2
lambdas (PDRS _ _ u c)  = lamRefs (map prefToPDRSRef u) `union` lamPCons c
  where lamRefs :: [PDRSRef] -> [((DRSVar,[DRSVar]),Int)]
        lamRefs []                    = []
        lamRefs (LambdaPDRSRef lt:ps) = lt : lamRefs ps
        lamRefs (PDRSRef{}:ps)        = lamRefs ps
        lamPCons :: [PCon] -> [((DRSVar,[DRSVar]),Int)]
        lamPCons []                       = []
        lamPCons (PCon _ (Rel r d):cs)    = lamRel r    `union` lamRefs d  `union` lamPCons cs
        lamPCons (PCon _ (Neg p1):cs)     = lambdas p1  `union` lamPCons cs
        lamPCons (PCon _ (Imp p1 p2):cs)  = lambdas p1  `union` lambdas p2 `union` lamPCons cs
        lamPCons (PCon _ (Or p1 p2):cs)   = lambdas p1  `union` lambdas p2 `union` lamPCons cs
        lamPCons (PCon p (Prop r p1):cs)  = lamRefs [r] `union` lambdas p1 `union` lamPCons cs
        lamPCons (PCon _ (Diamond p1):cs) = lambdas p1  `union` lamPCons cs
        lamPCons (PCon _ (Box p1):cs)     = lambdas p1  `union` lamPCons cs
        lamRel :: PDRSRel -> [((DRSVar,[DRSVar]),Int)]
        lamRel (LambdaPDRSRel lt) = [lt]
        lamRel (PDRSRel _)        = []


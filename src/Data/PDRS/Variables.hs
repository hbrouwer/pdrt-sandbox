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
, pdrsLabel
, pdrsLabels
, pdrsMAP
, pdrsUniverse
, pdrsConditions
, pdrsUniverses
, pdrsMAPs
, pdrsVariables
, pdrsPVars
, pdrsLambdas
, pdrsLambdaVars
) where

import Data.DRS.DataType (DRSRef (..), DRSRel (..))
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
-- based on a list of existing 'PVar's @prs@ and existing 'PDRSRef's @ers@.
---------------------------------------------------------------------------
newPRefs :: [PRef] -> [PDRSRef] -> [PRef]
newPRefs prs ers = packPRefs ps (newPDRSRefs rs ers)
  where (ps,rs) = unpackPRefs prs ([],[])
        unpackPRefs :: [PRef] -> ([PVar],[PDRSRef]) -> ([PVar],[PDRSRef])
        unpackPRefs [] uprs                   = uprs
        unpackPRefs (PRef p r:prs') (pvs,rs') = unpackPRefs prs' (pvs ++ [p],rs' ++ [r])
        packPRefs :: [PVar] -> [PDRSRef] -> [PRef]
        packPRefs _ []             = []
        packPRefs [] _             = []
        packPRefs (pv:pvs) (r:rs') = PRef pv r : packPRefs pvs rs'

---------------------------------------------------------------------------
-- ** Variable Collections
---------------------------------------------------------------------------

---------------------------------------------------------------------------
-- | Returns the label of a 'PDRS'.
---------------------------------------------------------------------------
pdrsLabel :: PDRS -> PVar
pdrsLabel (LambdaPDRS _) = 0
pdrsLabel (AMerge p1 p2)
  | isLambdaPDRS p2 = pdrsLabel p1
  | otherwise       = pdrsLabel p2
pdrsLabel (PMerge p1 p2)
  | isLambdaPDRS p2 = pdrsLabel p1
  | otherwise       = pdrsLabel p2
pdrsLabel (PDRS l _ _ _) = l

---------------------------------------------------------------------------
-- | Returns all the labels in a 'PDRS'.
---------------------------------------------------------------------------
pdrsLabels :: PDRS -> [PVar]
pdrsLabels (LambdaPDRS _) = []
pdrsLabels (AMerge p1 p2) = pdrsLabels p1 ++ pdrsLabels p2
pdrsLabels (PMerge p1 p2) = pdrsLabels p1 ++ pdrsLabels p2
pdrsLabels (PDRS l _ _ c) = l:concatMap labels c
  where labels :: PCon -> [PVar]
        labels (PCon _ (Rel _ _ ))   = []
        labels (PCon _ (Neg p1))     = pdrsLabels p1
        labels (PCon _ (Imp p1 p2))  = pdrsLabels p1 ++ pdrsLabels p2
        labels (PCon _ (Or p1 p2))   = pdrsLabels p1 ++ pdrsLabels p2
        labels (PCon _ (Prop _ p1))  = pdrsLabels p1
        labels (PCon _ (Diamond p1)) = pdrsLabels p1
        labels (PCon _ (Box p1))     = pdrsLabels p1

---------------------------------------------------------------------------
-- | Returns the top-level 'MAP's of a 'PDRS'.
---------------------------------------------------------------------------
pdrsMAP :: PDRS -> [MAP]
pdrsMAP (LambdaPDRS _) = []
pdrsMAP (AMerge p1 p2) = pdrsMAP p1 ++ pdrsMAP p2
pdrsMAP (PMerge p1 p2) = pdrsMAP p1 ++ pdrsMAP p2
pdrsMAP (PDRS _ m _ _) = m

---------------------------------------------------------------------------
-- | Returns the universe of a 'PDRS'.
---------------------------------------------------------------------------
pdrsUniverse :: PDRS -> [PRef]
pdrsUniverse (LambdaPDRS _) = []
pdrsUniverse (AMerge p1 p2) = pdrsUniverse p1 ++ pdrsUniverse p2
pdrsUniverse (PMerge p1 p2) = pdrsUniverse p1 ++ pdrsUniverse p2
pdrsUniverse (PDRS _ _ u _) = u

---------------------------------------------------------------------------
-- | Returns the conditions of a 'PDRS'.
---------------------------------------------------------------------------
pdrsConditions :: PDRS -> [PCon]
pdrsConditions (LambdaPDRS _) = []
pdrsConditions (AMerge p1 p2) = pdrsConditions p1 ++ pdrsConditions p2
pdrsConditions (PMerge p1 p2) = pdrsConditions p1 ++ pdrsConditions p2
pdrsConditions (PDRS _ _ _ c) = c

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
-- | Returns the list of all 'MAP's of a 'PDRS'.
---------------------------------------------------------------------------
pdrsMAPs :: PDRS -> [MAP]
pdrsMAPs (LambdaPDRS _) = []
pdrsMAPs (AMerge p1 p2) = pdrsMAPs p1 `union` pdrsMAPs p2
pdrsMAPs (PMerge p1 p2) = pdrsMAPs p1 `union` pdrsMAPs p2
pdrsMAPs (PDRS _ m _ c) = m `union` maps c
  where maps :: [PCon] -> [MAP]
        maps []                       = []
        maps (PCon _ (Rel _ _):cs)    = maps cs
        maps (PCon _ (Neg p1):cs)     = pdrsMAPs p1 `union` maps cs
        maps (PCon _ (Imp p1 p2):cs)  = pdrsMAPs p1 `union` pdrsMAPs p2 `union` maps cs
        maps (PCon _ (Or p1 p2):cs)   = pdrsMAPs p1 `union` pdrsMAPs p2 `union` maps cs
        maps (PCon _ (Prop _ p1):cs)  = pdrsMAPs p1 `union` maps cs
        maps (PCon _ (Diamond p1):cs) = pdrsMAPs p1 `union` maps cs
        maps (PCon _ (Box p1):cs)     = pdrsMAPs p1 `union` maps cs

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
        lamPCons (PCon _ (Prop r p1):cs)  = lamRefs [r]    `union` pdrsLambdas p1 `union` lamPCons cs
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

-- Variables.hs

{- |
  DRS variables
-}
module Data.DRS.Variables
(
  drsRefToDRSVar
, drsUniverse
, drsReferents
, drsVariables
, drsLambdas
, drsBoundRef
) where

import Data.DRS.Structure
import Data.List (union, sortBy)
import Data.Ord (comparing)

-- | Converts a DRS referent @r@ to a DRS variable
drsRefToDRSVar :: DRSRef -> DRSVar
drsRefToDRSVar (LambdaDRSRef (r,_)) = r
drsRefToDRSVar (DRSRef r)           = r

-- | Returns the universe of a DRS
drsUniverse :: DRS -> [DRSRef]
drsUniverse (LambdaDRS _) = []
drsUniverse (Merge d1 d2) = drsUniverse d1 `union` drsUniverse d2
drsUniverse (DRS u _)     = u

-- | Returns the list of all referents in a DRS
drsReferents :: DRS -> [DRSRef]
drsReferents (LambdaDRS _) = []
drsReferents (Merge d1 d2) = drsReferents d1 `union` drsReferents d2
drsReferents (DRS u c)     = u `union` referents c
  where referents :: [DRSCon] -> [DRSRef]
        referents []                = []
        referents ((Rel _ _):cs)    = referents cs
        referents ((Neg d1):cs)     = drsReferents d1 `union` referents cs
        referents ((Imp d1 d2):cs)  = drsReferents d1 `union` drsReferents d2 `union` referents cs
        referents ((Or d1 d2):cs)   = drsReferents d1 `union` drsReferents d2 `union` referents cs
        referents ((Prop _ d1):cs)  = drsReferents d1 `union` referents cs
        referents ((Diamond d1):cs) = drsReferents d1 `union` referents cs
        referents ((Box d1):cs)     = drsReferents d1 `union` referents cs

-- | Returns the list of all variables in a DRS
drsVariables :: DRS -> [DRSRef]
drsVariables (LambdaDRS _) = []
drsVariables (Merge d1 d2) = drsVariables d1 `union` drsVariables d2
drsVariables (DRS u c)     = u `union` variables c
  where variables :: [DRSCon] -> [DRSRef]
        variables []                = []
        variables ((Rel _ d):cs)    = d `union` variables cs
        variables ((Neg d1):cs)     = drsVariables d1 `union` variables cs
        variables ((Imp d1 d2):cs)  = drsVariables d1 `union` drsVariables d2 `union` variables cs
        variables ((Or d1 d2):cs)   = drsVariables d1 `union` drsVariables d2 `union` variables cs
        variables ((Prop r d1):cs)  = [r]             `union` drsVariables d1 `union` variables cs
        variables ((Diamond d1):cs) = drsVariables d1 `union` variables cs
        variables ((Box d1):cs)     = drsVariables d1 `union` variables cs

-- | Returns the ordered list of all lambda variables in a DRS
drsLambdas :: DRS -> [DRSVar]
drsLambdas d = map fst (sortBy (comparing snd) (lambdas d))

-- | Returns the list of all lambda tuples in a DRS
lambdas :: DRS -> [(DRSVar,Int)]
lambdas (LambdaDRS lt) = [lt]
lambdas (Merge d1 d2)  = lambdas d1    `union` lambdas d2
lambdas (DRS u c)      = lambdasRefs u `union` lambdasCons c

-- | Returns the list of all lambda tuples in a DRS universe
lambdasRefs :: [DRSRef] -> [(DRSVar,Int)] 
lambdasRefs []                     = []
lambdasRefs ((DRSRef _):ds)        = lambdasRefs ds
lambdasRefs ((LambdaDRSRef lt):ds) = [lt] ++ lambdasRefs ds

-- | Returns the list of all lambda tuples in a list of DRS conditions
lambdasCons :: [DRSCon] -> [(DRSVar,Int)]
lambdasCons []                = []
lambdasCons ((Rel _ d):cs)    = lambdasRefs d   `union` lambdasCons cs
lambdasCons ((Neg d1):cs)     = lambdas d1      `union` lambdasCons cs
lambdasCons ((Imp d1 d2):cs)  = lambdas d1      `union` lambdas d2 `union` lambdasCons cs
lambdasCons ((Or d1 d2):cs)   = lambdas d1      `union` lambdas d2 `union` lambdasCons cs
lambdasCons ((Prop r d1):cs)  = lambdasRefs [r] `union` lambdas d1 `union` lambdasCons cs
lambdasCons ((Diamond d1):cs) = lambdas d1      `union` lambdasCons cs
lambdasCons ((Box d1):cs)     = lambdas d1      `union` lambdasCons cs

-- | Returns whether DRS referent @d@ in local DRS @ld@ is bound in the
-- global DRS @gd@
drsBoundRef :: DRSRef -> DRS -> DRS -> Bool
drsBoundRef _ (LambdaDRS _) _  = False
drsBoundRef r (Merge d1 d2) gd = drsBoundRef r d1 gd || drsBoundRef r d2 gd
drsBoundRef r ld@(DRS lu _) gd@(DRS gu gc)
  | r `elem` lu           = True
  | r `elem` gu           = True
  | hasAntecedent r ld gc = True
  | otherwise             = False

-- | Returns wehther DRS referent @d@ in local DRS @ld@ is bound by an
-- antecedent in the DRS conditions @gc@
hasAntecedent :: DRSRef -> DRS -> [DRSCon] -> Bool
hasAntecedent r ld gc = or $ map antecedent gc
  where antecedent :: DRSCon -> Bool
        antecedent (Rel _ _)     = False
        antecedent (Neg d1)      = isSubDRS ld d1 && drsBoundRef r ld d1
        antecedent (Imp d1 d2)   = (r `elem` drsUniverse d1 && d2 == ld)
          || (isSubDRS ld d1 && drsBoundRef r ld d1)
          || (isSubDRS ld d2 && drsBoundRef r ld d2)
        antecedent (Or d1 d2)    = (r `elem` drsUniverse d1 && d2 == ld)
          || (isSubDRS ld d1 && drsBoundRef r ld d1)
          || (isSubDRS ld d2 && drsBoundRef r ld d2)
        antecedent (Prop _ d1)   = isSubDRS ld d1 && drsBoundRef r ld d1
        antecedent (Diamond d1)  = isSubDRS ld d1 && drsBoundRef r ld d1
        antecedent (Box d1)      = isSubDRS ld d1 && drsBoundRef r ld d1

{- |
Module      :  Data.DRS.Variables
Copyright   :  (c) Harm Brouwer and Noortje Venhuizen
License     :  Apache-2.0

Maintainer  :  me@hbrouwer.eu, n.j.venhuizen@rug.nl
Stability   :  provisional
Portability :  portable

DRS variables
-}

module Data.DRS.Variables
(
-- * Conversion
  drsRefToDRSVar
-- * Binding
, drsBoundRef
-- * Variable Collections
, drsUniverses
, drsVariables
, drsFreeRefs
, drsLambdas
-- * New Variables
, newDRSRefs
) where

import Data.DRS.Structure
import Data.List (partition, sortBy, union)
import Data.Ord (comparing)

---------------------------------------------------------------------------
-- * Exported
---------------------------------------------------------------------------

---------------------------------------------------------------------------
-- ** Conversion
---------------------------------------------------------------------------

---------------------------------------------------------------------------
-- | Converts a 'DRSRef' @r@ into a 'DRSVar'.
---------------------------------------------------------------------------
drsRefToDRSVar :: DRSRef -> DRSVar
drsRefToDRSVar (LambdaDRSRef (r,_)) = r
drsRefToDRSVar (DRSRef r)           = r

---------------------------------------------------------------------------
-- ** Binding
---------------------------------------------------------------------------

---------------------------------------------------------------------------
-- | Returns whether 'DRSRef' @d@ in local 'DRS' @ld@ is bound in the
-- global 'DRS' @gd@.
---------------------------------------------------------------------------
drsBoundRef :: DRSRef -> DRS -> DRS -> Bool
drsBoundRef _ _ (LambdaDRS _)  = False
drsBoundRef r ld (Merge d1 d2) = drsBoundRef r ld d1 || drsBoundRef r ld d2
drsBoundRef r ld@(DRS lu _) gd@(DRS gu gc)
  | r `elem` lu           = True
  | r `elem` gu           = True
  | hasAntecedent r ld gc = True
  | otherwise             = False
  where hasAntecedent :: DRSRef -> DRS -> [DRSCon] -> Bool
        hasAntecedent r ld = any antecedent
          where antecedent :: DRSCon -> Bool
                antecedent (Rel _ _)     = False
                antecedent (Neg d1)      = isSubDRS ld d1 && drsBoundRef r ld d1
                antecedent (Imp d1 d2)   = (r `elem` drsUniverse d1 && isSubDRS ld d2)
                  || (isSubDRS ld d1 && drsBoundRef r ld d1)
                  || (isSubDRS ld d2 && drsBoundRef r ld d2)
                antecedent (Or d1 d2)    = (r `elem` drsUniverse d1 && isSubDRS ld d2)
                  || (isSubDRS ld d1 && drsBoundRef r ld d1)
                  || (isSubDRS ld d2 && drsBoundRef r ld d2)
                antecedent (Prop _ d1)   = isSubDRS ld d1 && drsBoundRef r ld d1
                antecedent (Diamond d1)  = isSubDRS ld d1 && drsBoundRef r ld d1
                antecedent (Box d1)      = isSubDRS ld d1 && drsBoundRef r ld d1

---------------------------------------------------------------------------
-- ** Variable Collections
---------------------------------------------------------------------------

---------------------------------------------------------------------------
-- | Returns the list of 'DRSRef's from all universes in a 'DRS'.
---------------------------------------------------------------------------
drsUniverses :: DRS -> [DRSRef]
drsUniverses (LambdaDRS _) = []
drsUniverses (Merge d1 d2) = drsUniverses d1 ++ drsUniverses d2
drsUniverses (DRS u c)     = u ++ universes c
  where universes :: [DRSCon] -> [DRSRef]
        universes []              = []
        universes (Rel _ _:cs)    = universes cs
        universes (Neg d1:cs)     = drsUniverses d1 ++ universes cs
        universes (Imp d1 d2:cs)  = drsUniverses d1 ++ drsUniverses d2 ++ universes cs
        universes (Or d1 d2:cs)   = drsUniverses d1 ++ drsUniverses d2 ++ universes cs
        universes (Prop _ d1:cs)  = drsUniverses d1 ++ universes cs
        universes (Diamond d1:cs) = drsUniverses d1 ++ universes cs
        universes (Box d1:cs)     = drsUniverses d1 ++ universes cs

---------------------------------------------------------------------------
-- | Returns the list of all 'DRSRef's in a 'DRS' (equals 'drsUniverses'
-- ++ 'drsFreeRefs').
---------------------------------------------------------------------------
drsVariables :: DRS -> [DRSRef]
drsVariables (LambdaDRS _) = []
drsVariables (Merge d1 d2) = drsVariables d1 `union` drsVariables d2
drsVariables (DRS u c)     = u `union` variables c
  where variables :: [DRSCon] -> [DRSRef]
        variables []              = []
        variables (Rel _ d:cs)    = d `union` variables cs
        variables (Neg d1:cs)     = drsVariables d1 `union` variables cs
        variables (Imp d1 d2:cs)  = drsVariables d1 `union` drsVariables d2 `union` variables cs
        variables (Or d1 d2:cs)   = drsVariables d1 `union` drsVariables d2 `union` variables cs
        variables (Prop r d1:cs)  = [r]             `union` drsVariables d1 `union` variables cs
        variables (Diamond d1:cs) = drsVariables d1 `union` variables cs
        variables (Box d1:cs)     = drsVariables d1 `union` variables cs

---------------------------------------------------------------------------
-- | Returns the list of all free 'DRSRef's in a 'DRS'.
---------------------------------------------------------------------------
drsFreeRefs :: DRS -> DRS -> [DRSRef]
drsFreeRefs (LambdaDRS _) _  = []
drsFreeRefs (Merge d1 d2) gd = drsFreeRefs d1 gd `union` drsFreeRefs d2 gd
drsFreeRefs ld@(DRS _ c)  gd = free c
  where free :: [DRSCon] -> [DRSRef]
        free []              = []
        free (Rel _ d:cs)    = snd (partition (flip (`drsBoundRef` ld) gd) d) `union` free cs
        free (Neg d1:cs)     = drsFreeRefs d1 gd `union` free cs
        free (Imp d1 d2:cs)  = drsFreeRefs d1 gd `union` drsFreeRefs d2 gd `union` free cs
        free (Or d1 d2:cs)   = drsFreeRefs d1 gd `union` drsFreeRefs d2 gd `union` free cs
        free (Prop r d1:cs)  = snd (partition (flip (`drsBoundRef` ld) gd) [r]) `union` drsFreeRefs d1 gd `union` free cs
        free (Diamond d1:cs) = drsFreeRefs d1 gd `union` free cs
        free (Box d1:cs)     = drsFreeRefs d1 gd `union` free cs

---------------------------------------------------------------------------
-- | Returns the ordered list of all lambda variables in a 'DRS'.
---------------------------------------------------------------------------
drsLambdas :: DRS -> [DRSVar]
drsLambdas d = map fst (sortBy (comparing snd) (lambdas d))

---------------------------------------------------------------------------
-- ** New Variables
---------------------------------------------------------------------------

---------------------------------------------------------------------------
-- | Returns a list of new 'DRSRef's, based on a list of old 'DRSRef's and
-- a list of existing 'DRSRef's.
---------------------------------------------------------------------------
newDRSRefs :: [DRSRef] -> [DRSRef] -> [DRSRef]
newDRSRefs [] _        = []
newDRSRefs (r:rs) refs = nr : newDRSRefs rs (nr:refs)
  where nr = newRef 0
        newRef :: Int -> DRSRef
        newRef n
          | r' `elem` refs = newRef (n + 1)
          | otherwise      = r'
          where r' =
                  case r of
                   (LambdaDRSRef (dv,lp)) -> LambdaDRSRef (dv ++ show n, lp)
                   (DRSRef dv)            -> DRSRef       (dv ++ show n)

---------------------------------------------------------------------------
-- * Private
---------------------------------------------------------------------------

---------------------------------------------------------------------------
-- | Returns the list of all lambda tuples in a 'DRS'.
---------------------------------------------------------------------------
lambdas :: DRS -> [(DRSVar,Int)]
lambdas (LambdaDRS lt) = [lt]
lambdas (Merge d1 d2)  = lambdas d1    `union` lambdas d2
lambdas (DRS u c)      = lambdasRefs u `union` lambdasCons c

---------------------------------------------------------------------------
-- | Returns the list of all lambda tuples in a 'DRS' universe.
---------------------------------------------------------------------------
lambdasRefs :: [DRSRef] -> [(DRSVar,Int)] 
lambdasRefs []                   = []
lambdasRefs (DRSRef _:ds)        = lambdasRefs ds
lambdasRefs (LambdaDRSRef lt:ds) = lt : lambdasRefs ds

---------------------------------------------------------------------------
-- | Returns the list of all lambda tuples in a list of 'DRS' conditions
---------------------------------------------------------------------------
lambdasCons :: [DRSCon] -> [(DRSVar,Int)]
lambdasCons []              = []
lambdasCons (Rel _ d:cs)    = lambdasRefs d   `union` lambdasCons cs
lambdasCons (Neg d1:cs)     = lambdas d1      `union` lambdasCons cs
lambdasCons (Imp d1 d2:cs)  = lambdas d1      `union` lambdas d2 `union` lambdasCons cs
lambdasCons (Or d1 d2:cs)   = lambdas d1      `union` lambdas d2 `union` lambdasCons cs
lambdasCons (Prop r d1:cs)  = lambdasRefs [r] `union` lambdas d1 `union` lambdasCons cs
lambdasCons (Diamond d1:cs) = lambdas d1      `union` lambdasCons cs
lambdasCons (Box d1:cs)     = lambdas d1      `union` lambdasCons cs


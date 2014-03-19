{- |
Module      :  Data.DRS.Binding
Copyright   :  (c) Harm Brouwer and Noortje Venhuizen
License     :  Apache-2.0

Maintainer  :  me@hbrouwer.eu, n.j.venhuizen@rug.nl
Stability   :  provisional
Portability :  portable

DRS binding
-}

module Data.DRS.Binding
(
  drsBoundRef
, drsFreeRefs
) where

import Data.DRS.DataType
import Data.DRS.Structure
import Data.DRS.Variables
import Data.List (partition, union)

---------------------------------------------------------------------------
-- * Exported
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
                antecedent (Or d1 d2)    = (isSubDRS ld d1 && drsBoundRef r ld d1)
                  || (isSubDRS ld d2 && drsBoundRef r ld d2)
                antecedent (Prop _ d1)   = isSubDRS ld d1 && drsBoundRef r ld d1
                antecedent (Diamond d1)  = isSubDRS ld d1 && drsBoundRef r ld d1
                antecedent (Box d1)      = isSubDRS ld d1 && drsBoundRef r ld d1

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

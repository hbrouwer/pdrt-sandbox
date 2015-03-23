{- |
Module      :  Data.DRS.Translate
Copyright   :  (c) Harm Brouwer and Noortje Venhuizen
License     :  Apache-2.0

Maintainer  :  me@hbrouwer.eu, n.j.venhuizen@rug.nl
Stability   :  provisional
Portability :  portable

DRS to FOL translation
-}

module Data.DRS.Translate
(
  drsToFOL
) where

import Data.DRS.DataType
import Data.DRS.Variables
import qualified Data.FOL as F

---------------------------------------------------------------------------
-- * Exported
---------------------------------------------------------------------------

---------------------------------------------------------------------------
-- | Converts a 'DRS' @d@ to a 'F.FOLForm'
---------------------------------------------------------------------------
drsToFOL :: DRS -> F.FOLForm
drsToFOL d = drsToMFOL d worldVar

---------------------------------------------------------------------------
-- * Private
---------------------------------------------------------------------------

---------------------------------------------------------------------------
-- **  Constants
---------------------------------------------------------------------------

-- | Symbol for world variable
worldVar :: String
worldVar = "w"

-- | Symbol for accessibility relation between worlds
worldRel :: String
worldRel = "Acc"

---------------------------------------------------------------------------
-- **  Conversion to modal FOL
---------------------------------------------------------------------------

---------------------------------------------------------------------------
-- | Converts a DRS to a modal FOL formula with world @w@
---------------------------------------------------------------------------
drsToMFOL :: DRS -> F.FOLVar -> F.FOLForm
drsToMFOL (LambdaDRS _)  _ = error "infelicitous FOL formula"
drsToMFOL (Merge _ _)    _ = error "infelicitous FOL formula"
drsToMFOL (DRS [] c)     w = drsConsToMFOL c w
drsToMFOL (DRS (r:rs) c) w = F.Exists (drsRefToDRSVar r) (drsToMFOL (DRS rs c) w)

-- | Converts a list of DRS conditions to a modal FOL formula with world @w@
drsConsToMFOL :: [DRSCon] -> F.FOLVar -> F.FOLForm
drsConsToMFOL [] _           = F.Top
drsConsToMFOL [Rel r d] w    = F.Rel (drsRelToString r) (w : map drsRefToDRSVar d)
drsConsToMFOL [Neg d1] w     = F.Neg (drsToMFOL d1 w)
drsConsToMFOL [Imp d1 d2] w  = quantifyForAll d1
  where quantifyForAll :: DRS -> F.FOLForm
        quantifyForAll (LambdaDRS _)  = error "infelicitous FOL formula"
        quantifyForAll (Merge _ _)    = error "infelicitous FOL formula"
        quantifyForAll (DRS [] c)     = F.Imp    (drsConsToMFOL c w) (drsToMFOL d2 w)
        quantifyForAll (DRS (r:rs) c) = F.ForAll (drsRefToDRSVar r)  (quantifyForAll (DRS rs c))
drsConsToMFOL [Or d1 d2] w   = F.Or (drsToMFOL d1 w) (drsToMFOL d2 w)
drsConsToMFOL [Prop r d1] w  = F.And (F.Rel worldRel [w,drsRefToDRSVar r]) (drsToMFOL d1 (drsRefToDRSVar r))
drsConsToMFOL [Diamond d1] w = F.Exists v (F.And (F.Rel worldRel [w,v]) (drsToMFOL d1 v))
  where v = w ++ "'"
drsConsToMFOL [Box d1] w     = F.ForAll v (F.Imp (F.Rel worldRel [w,v]) (drsToMFOL d1 v))
  where v = w ++ "'"
drsConsToMFOL (c:cs) w       = F.And (drsConsToMFOL [c] w) (drsConsToMFOL cs w)

-- Translate.hs

{- |
  DRS to FOL translation
-}
module Data.DRS.Translate
(
  drsToFOL
) where

import Data.DRS.Structure
import Data.DRS.Variables
import qualified Data.FOL as F

-- | Constants
worldVar = "w"   -- ^ World variable
worldRel = "Acc" -- ^ Accessibility relation between worlds

-- | Converts a DRS @d@ to a FOL formula
drsToFOL :: DRS -> F.FOLForm
drsToFOL d = drsToMFOL d worldVar

-- | Converts a DRS to a modal FOL formula with world @w@
drsToMFOL :: DRS -> F.FOLVar -> F.FOLForm
drsToMFOL (DRS [] c) w     = drsConsToMFOL c w
drsToMFOL (DRS (r:rs) c) w = F.Exists (drsRefToDRSVar r) (drsToMFOL (DRS rs c) w)

-- | Converts a list of DRS conditions to a modal FOL formula with world @w@
drsConsToMFOL :: [DRSCon] -> F.FOLVar -> F.FOLForm
drsConsToMFOL [] _                = F.Top
drsConsToMFOL ((Rel r d):[]) w    = F.Rel r (w:(map drsRefToDRSVar d))
drsConsToMFOL ((Neg d1):[]) w     = F.Neg (drsToMFOL d1 w)
drsConsToMFOL ((Imp d1 d2):[]) w  = quantifyForAll d1
  where quantifyForAll :: DRS -> F.FOLForm
        quantifyForAll (DRS [] c)     = F.Imp    (drsConsToMFOL c w) (drsToMFOL d2 w)
        quantifyForAll (DRS (r:rs) c) = F.ForAll (drsRefToDRSVar r)  (quantifyForAll (DRS rs c))
drsConsToMFOL ((Or d1 d2):[]) w   = F.Or (drsToMFOL d1 w) (drsToMFOL d2 w)
drsConsToMFOL ((Prop r d1):[]) w  = F.And (F.Rel worldRel [w,v]) (drsToMFOL d1 v)
  where v = drsRefToDRSVar r
drsConsToMFOL ((Diamond d1):[]) w = F.Exists v (F.And (F.Rel worldRel [w,v]) (drsToMFOL d1 v))
  where v = w ++ "'"
drsConsToMFOL ((Box d1):[]) w     = F.ForAll v (F.Imp (F.Rel worldRel [w,v]) (drsToMFOL d1 v))
  where v = w ++ "'"
drsConsToMFOL (c:cs) w            = F.And (drsConsToMFOL [c] w) (drsConsToMFOL cs w)
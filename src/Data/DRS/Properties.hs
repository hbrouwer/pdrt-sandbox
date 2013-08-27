{- |
Module      :  Data.DRS.Properties
Copyright   :  (c) Harm Brouwer and Noortje Venhuizen
License     :  Apache-2.0

Maintainer  :  me@hbrouwer.eu
Stability   :  provisional
Portability :  portable

DRS properties
-}

module Data.DRS.Properties 
( 
  isProperDRS
, isPureDRS
, isResolvedDRS
, isFOLDRS
, isMergeDRS
, isLambdaDRS
) where

import Data.DRS.Structure
import Data.DRS.Variables

-- | Returns whether DRS @d@ is a *proper DRS*, where a *proper DRS* is
-- defined as a DRS without any free variables
isProperDRS :: DRS -> Bool
isProperDRS d = isProperSubDRS d d

-- | Returns whether DRS @sd@, which is a sub-DRS of DRS @gd@ is a 
-- proper DRS
isProperSubDRS :: DRS -> DRS -> Bool
isProperSubDRS (LambdaDRS _) _  = True
isProperSubDRS (Merge d1 d2) gd = isProperSubDRS d1 gd && isProperSubDRS d2 gd
isProperSubDRS sd@(DRS _ cs) gd = all properCon cs
  where properCon :: DRSCon -> Bool
        properCon (Rel _ d)    = all (flip (`drsBoundRef` sd) gd) d
        properCon (Neg d1)     = isProperSubDRS d1 gd
        properCon (Imp d1 d2)  = isProperSubDRS d1 gd && isProperSubDRS d2 gd
        properCon (Or d1 d2)   = isProperSubDRS d1 gd && isProperSubDRS d2 gd
        properCon (Prop r d1)  = drsBoundRef r sd gd  && isProperSubDRS d1 gd
        properCon (Diamond d1) = isProperSubDRS d1 gd
        properCon (Box d1)     = isProperSubDRS d1 gd

-- | Returns whether DRS @d@ is a *pure DRS*, where a *pure DRS* is
-- defined as a DRS without otiose declarations of discourse referents
isPureDRS :: DRS -> Bool
isPureDRS d = isPure d []
  where isPure :: DRS -> [DRSRef] -> Bool
        isPure (LambdaDRS _) _  = True
        isPure (Merge d1 d2) rs = isPure d1 rs && isPure d2 (rs ++ drsUniverse d1)
        isPure (DRS u c) rs     = not (any (`elem` rs) u) && all isPureCon c
          where isPureCon :: DRSCon -> Bool
                isPureCon (Rel _ _)    = True
                isPureCon (Neg d1)     = isPure d1 (u ++ rs)
                isPureCon (Imp d1 d2)  = isPure d1 (u ++ rs) && isPure d2 (u ++ rs ++ drsUniverse d1)
                isPureCon (Or d1 d2)   = isPure d1 (u ++ rs) && isPure d2 (u ++ rs ++ drsUniverse d1)
                isPureCon (Prop _ d1)  = isPure d1 (u ++ rs)
                isPureCon (Diamond d1) = isPure d1 (u ++ rs)
                isPureCon (Box d1)     = isPure d1 (u ++ rs)

-- | Returns whether a DRS is resolved (containing no unresolved merges 
-- or lambdas)
isResolvedDRS :: DRS -> Bool
isResolvedDRS (LambdaDRS _) = False
isResolvedDRS (Merge _ _)   = False
isResolvedDRS (DRS u c)     = all isResolvedRef u && all isResolvedCon c
  where isResolvedRef :: DRSRef -> Bool
        isResolvedRef (LambdaDRSRef _) = False
        isResolvedRef (DRSRef _)       = True
        isResolvedCon :: DRSCon -> Bool
        isResolvedCon (Rel _ d)    = all isResolvedRef d
        isResolvedCon (Neg d1)     = isResolvedDRS d1
        isResolvedCon (Imp d1 d2)  = isResolvedDRS d1 && isResolvedDRS d2
        isResolvedCon (Or d1 d2)   = isResolvedDRS d1 && isResolvedDRS d2
        isResolvedCon (Prop r d1)  = isResolvedRef r  && isResolvedDRS d1
        isResolvedCon (Diamond d1) = isResolvedDRS d1
        isResolvedCon (Box d1)     = isResolvedDRS d1

-- | Returns whether DRS @d@ is a FOL DRS
isFOLDRS :: DRS -> Bool
isFOLDRS d = isResolvedDRS d && isProperDRS d && isPureDRS d

-- | Returns whether a DRS is entirely a merge DRS (at its top-level)
isMergeDRS :: DRS -> Bool
isMergeDRS (LambdaDRS _) = False
isMergeDRS (Merge _ _)   = True
isMergeDRS (DRS _ _)     = False

-- | Returns whether a DRS is entirely a lambda DRS (at its top-level)
isLambdaDRS :: DRS -> Bool
isLambdaDRS (LambdaDRS _) = True
isLambdaDRS (Merge d1 d2) = isLambdaDRS d1 && isLambdaDRS d2
isLambdaDRS (DRS _ _)     = False

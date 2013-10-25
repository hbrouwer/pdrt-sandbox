{- |
Module      :  Data.DRS.Properties
Copyright   :  (c) Harm Brouwer and Noortje Venhuizen
License     :  Apache-2.0

Maintainer  :  me@hbrouwer.eu, n.j.venhuizen@rug.nl
Stability   :  provisional
Portability :  portable

DRS properties
-}

module Data.DRS.Properties 
( 
  isFOLDRS
, isLambdaDRS
, isMergeDRS
, isResolvedDRS
, isProperDRS
, isPureDRS
) where

import Data.DRS.Structure
import Data.DRS.Variables

---------------------------------------------------------------------------
-- * Exported
---------------------------------------------------------------------------

---------------------------------------------------------------------------
-- | Returns whether 'DRS' @d@ can be translated into a 'FOLForm'.
---------------------------------------------------------------------------
isFOLDRS :: DRS -> Bool
isFOLDRS d = isResolvedDRS d && isPureDRS d && isProperDRS d

---------------------------------------------------------------------------
-- | Returns whether a 'DRS' is entirely a 'LambdaDRS' (at its top-level).
---------------------------------------------------------------------------
isLambdaDRS :: DRS -> Bool
isLambdaDRS (LambdaDRS _) = True
isLambdaDRS (Merge d1 d2) = isLambdaDRS d1 && isLambdaDRS d2
isLambdaDRS (DRS _ _)     = False

---------------------------------------------------------------------------
-- | Returns whether a 'DRS' is entirely a 'Merge' (at its top-level).
---------------------------------------------------------------------------
isMergeDRS :: DRS -> Bool
isMergeDRS (LambdaDRS _) = False
isMergeDRS (Merge _ _)   = True
isMergeDRS (DRS _ _)     = False

---------------------------------------------------------------------------
-- | Returns whether a 'DRS' is resolved (containing no unresolved merges 
-- or lambdas)
---------------------------------------------------------------------------
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

---------------------------------------------------------------------------
-- | Returns whether 'DRS' @d@ is /proper/ , where:
--
-- ['DRS' @d@ is proper /iff/]
--
--  * @d@ does not contain any free variables
---------------------------------------------------------------------------
isProperDRS :: DRS -> Bool
isProperDRS d = isProperSubDRS d d
  where isProperSubDRS :: DRS -> DRS -> Bool
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

---------------------------------------------------------------------------
-- | Returns whether 'DRS' @d@ is /pure/, where:
--
-- ['DRS' @d@ is pure /iff/]
--
--  * @d@ does not contain any otiose declarations of discourse referents
--    (i.e., @d@ does not contain any unbound, duplicate uses of referents).
---------------------------------------------------------------------------
isPureDRS :: DRS -> Bool
isPureDRS gd = isPure gd []
  where isPure :: DRS -> [DRSRef] -> Bool
        isPure (LambdaDRS _) _   = True
        isPure (Merge d1 d2) srs = isPure d1 srs && isPure d2 (srs ++ drsVariables d1)
        isPure ld@(DRS u c) srs  = not (any (`elem` srs) u) && pureCons c (srs ++ u)
          where pureCons :: [DRSCon] -> [DRSRef] -> Bool
                pureCons []              _  = True
                pureCons (Rel _ ds:cs)   rs = pureRefs ds rs  && pureCons cs (rs ++ ds)
                pureCons (Neg d1:cs)     rs = isPure d1 rs    && pureCons cs (rs ++ drsVariables d1)
                pureCons (Imp d1 d2:cs)  rs = isPure d1 rs    && isPure d2 rs' && pureCons cs (rs' ++ drsVariables d2)
                  where rs' = rs ++ drsVariables d1
                pureCons (Or d1 d2:cs)   rs = isPure d1 rs    && isPure d2 rs' && pureCons cs (rs' ++ drsVariables d2)
                  where rs' = rs ++ drsVariables d1
                pureCons (Prop r d1:cs)  rs = pureRefs [r] rs && isPure d1 rs  && pureCons cs (rs ++ drsVariables d1)
                pureCons (Diamond d1:cs) rs = isPure d1 rs    && pureCons cs (rs ++ drsVariables d1)
                pureCons (Box d1:cs)     rs = isPure d1 rs    && pureCons cs (rs ++ drsVariables d1)
                pureRefs :: [DRSRef] -> [DRSRef] -> Bool
                pureRefs rs srs = all (\r -> drsBoundRef r ld gd || r `notElem` srs) rs


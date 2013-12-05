{- |
Module      :  Data.PDRS.Properties
Copyright   :  (c) Harm Brouwer and Noortje Venhuizen
License     :  Apache-2.0

Maintainer  :  me@hbrouwer.eu, n.j.venhuizen@rug.nl
Stability   :  provisional
Portability :  portable

PDRS properties
-}

module Data.PDRS.Properties 
(
  isMergePDRS
, isResolvedPDRS
, isPresupPDRS
) where

import Data.PDRS.Structure
import Data.PDRS.Variables

---------------------------------------------------------------------------
-- * Exported
---------------------------------------------------------------------------

---------------------------------------------------------------------------
-- | Returns whether a 'PDRS' is an 'AMerge' or 'PMerge' (at its top-level)
---------------------------------------------------------------------------
isMergePDRS :: PDRS -> Bool
isMergePDRS (LambdaPDRS {}) = False
isMergePDRS (AMerge {})     = True
isMergePDRS (PMerge {})     = True
isMergePDRS (PDRS {})       = False

---------------------------------------------------------------------------
-- | Returns whether a 'PDRS' is resolved (containing no unresolved merges 
-- or lambdas)
---------------------------------------------------------------------------
isResolvedPDRS :: PDRS -> Bool
isResolvedPDRS (LambdaPDRS {}) = False
isResolvedPDRS (AMerge {})     = False
isResolvedPDRS (PMerge {})     = False
isResolvedPDRS (PDRS _ _ u c)  = all isResolvedRef (map (\(PRef _ r) -> r) u) && all isResolvedPCon c
  where isResolvedRef :: PDRSRef -> Bool
        isResolvedRef (LambdaPDRSRef _) = False
        isResolvedRef (PDRSRef _)       = True
        isResolvedPCon :: PCon -> Bool
        isResolvedPCon (PCon _ (Rel _ d))    = all isResolvedRef d
        isResolvedPCon (PCon _ (Neg p1))     = isResolvedPDRS p1
        isResolvedPCon (PCon _ (Imp p1 p2))  = isResolvedPDRS p1 && isResolvedPDRS p2
        isResolvedPCon (PCon _ (Or p1 p2))   = isResolvedPDRS p1 && isResolvedPDRS p2
        isResolvedPCon (PCon _ (Prop r p1))  = isResolvedRef r && isResolvedPDRS p1
        isResolvedPCon (PCon _ (Diamond p1)) = isResolvedPDRS p1
        isResolvedPCon (PCon _ (Box p1))     = isResolvedPDRS p1

---------------------------------------------------------------------------
-- | Returns whether a 'PDRS' is /presuppositional/, where:
--
-- [A 'PDRS' @p@ is presuppositional /iff/]
--
--  * @p@ contains free pointers
---------------------------------------------------------------------------
isPresupPDRS :: PDRS -> Bool
isPresupPDRS (LambdaPDRS {}) = False
isPresupPDRS (AMerge p1 p2)  = isPresupPDRS p1 || isPresupPDRS p2
isPresupPDRS (PMerge {})     = True
isPresupPDRS p@(PDRS {})     = any (`pdrsIsFreePVar` p) (pdrsPVars p)

{- |
Module      :  Data.PDRS.Structure
Copyright   :  (c) Harm Brouwer and Noortje Venhuizen
License     :  Apache-2.0

Maintainer  :  me@hbrouwer.eu, n.j.venhuizen@rug.nl
Stability   :  provisional
Portability :  portable

Structural operations on PDRSs
-}

module Data.PDRS.Structure
(
  emptyPDRS
, isLambdaPDRS
, isMergePDRS
, isResolvedPDRS
, isSubPDRS
) where

import Data.PDRS.DataType

---------------------------------------------------------------------------
-- * Exported
---------------------------------------------------------------------------

---------------------------------------------------------------------------
-- | Returns an empty 'PDRS', if possible with the same label as 'PDRS' @p@.
---------------------------------------------------------------------------
emptyPDRS :: PDRS -> PDRS
emptyPDRS lp@(LambdaPDRS _) = lp
emptyPDRS (AMerge p1 p2)
  | isLambdaPDRS p2 = AMerge (emptyPDRS p1) p2
  | otherwise       = emptyPDRS p2
emptyPDRS (PMerge p1 p2)
  | isLambdaPDRS p2 = PMerge (emptyPDRS p1) p2
  | otherwise       = emptyPDRS p2
emptyPDRS (PDRS l _ _ _)    = PDRS l [] [] []

---------------------------------------------------------------------------
-- | Returns whether a PDRS is entirely a 'LambdaPDRS' (at its top-level)
---------------------------------------------------------------------------
isLambdaPDRS :: PDRS -> Bool
isLambdaPDRS (LambdaPDRS {}) = True
isLambdaPDRS (AMerge p1 p2)  = isLambdaPDRS p1 && isLambdaPDRS p2
isLambdaPDRS (PMerge p1 p2)  = isLambdaPDRS p1 && isLambdaPDRS p2
isLambdaPDRS (PDRS {})       = False

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
-- | Returns whether 'PDRS' @p1@ is a direct or indirect sub-'PDRS' of
-- 'PDRS' @p2@.
---------------------------------------------------------------------------
isSubPDRS :: PDRS -> PDRS -> Bool
isSubPDRS _  (LambdaPDRS _)    = False
isSubPDRS p1 (AMerge p2 p3)    = isSubPDRS p1 p2 || isSubPDRS p1 p3
isSubPDRS p1 (PMerge p2 p3)    = isSubPDRS p1 p2 || isSubPDRS p1 p3
isSubPDRS p1 p2@(PDRS _ _ _ c) = p1 == p2 || any subPDRS c
  where subPDRS :: PCon -> Bool
        subPDRS (PCon _ (Rel _ _ ))   = False
        subPDRS (PCon _ (Neg p3))     = isSubPDRS p1 p3
        subPDRS (PCon _ (Imp p3 p4))  = isSubPDRS p1 p3 || isSubPDRS p1 p4
        subPDRS (PCon _ (Or p3 p4))   = isSubPDRS p1 p3 || isSubPDRS p1 p4
        subPDRS (PCon _ (Prop _ p3))  = isSubPDRS p1 p3
        subPDRS (PCon _ (Diamond p3)) = isSubPDRS p1 p3
        subPDRS (PCon _ (Box p3))     = isSubPDRS p1 p3

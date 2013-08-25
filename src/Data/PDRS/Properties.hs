-- Properties.hs

{- |
  PDRS properties
-}
module Data.PDRS.Properties 
(
  isResolvedPDRS
, isMergePDRS
, isLambdaPDRS
, isPresupPDRS
) where

import Data.PDRS.Structure
import Data.PDRS.Variables

-- | Returns whether a PDRS is resolved (containing no unresolved merges 
-- or lambdas)
isResolvedPDRS :: PDRS -> Bool
isResolvedPDRS (LambdaPDRS _) = False
isResolvedPDRS (AMerge _ _)   = False
isResolvedPDRS (PMerge _ _)   = False
isResolvedPDRS (PDRS _ _ u c) = all isResolvedRef (map (\(PRef _ r) -> r) u) && all isResolvedPCon c
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

-- | Returns whether a PDRS is entirely a merge PDRS (at its top-level)
isMergePDRS :: PDRS -> Bool
isMergePDRS (LambdaPDRS _) = False
isMergePDRS (AMerge _ _)   = True
isMergePDRS (PMerge _ _)   = True
isMergePDRS (PDRS _ _ _ _) = False

-- | Returns whether a PDRS is entirely a lambda PDRS (at its top-level)
isLambdaPDRS :: PDRS -> Bool
isLambdaPDRS (LambdaPDRS _) = True
isLambdaPDRS (AMerge p1 p2) = isLambdaPDRS p1 && isLambdaPDRS p2
isLambdaPDRS (PMerge p1 p2) = isLambdaPDRS p1 && isLambdaPDRS p2
isLambdaPDRS (PDRS _ _ _ _) = False

-- | Returns whether a PDRS is a *presuppositional PDRS* (a PDRS with
-- free pointers)
isPresupPDRS :: PDRS -> Bool
isPresupPDRS (LambdaPDRS _)   = False
isPresupPDRS (AMerge p1 p2)   = isPresupPDRS p1 || isPresupPDRS p2
isPresupPDRS (PMerge _ _)     = True
isPresupPDRS p@(PDRS _ _ _ _) = any ((flip pdrsIsFreePVar) p) (pdrsPVars p)

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
  isProperPDRS
, isPurePDRS
, isPresupPDRS
, isSimplePDRS
, isPlainPDRS
, pdrsIsDifferentNP
, pdrsIsSameNP
) where

import Data.List (union)

import Data.PDRS.Binding
import Data.PDRS.DataType
import Data.PDRS.LambdaCalculus
import Data.PDRS.Merge
import Data.PDRS.Structure
import Data.PDRS.Variables

---------------------------------------------------------------------------
-- * Exported
---------------------------------------------------------------------------

---------------------------------------------------------------------------
-- | Returns whether a 'PDRS' is /proper/, where:
--
-- [A 'PDRS' @p@ is proper /iff/]
--
--  * @p@ does not contain any free referents
---------------------------------------------------------------------------
isProperPDRS :: PDRS -> Bool
isProperPDRS p = isProperSubPDRS p p
  where isProperSubPDRS (LambdaPDRS _) _      = True
        isProperSubPDRS (AMerge p1 p2) gp     = isProperSubPDRS p1 gp && isProperSubPDRS p2 gp
        isProperSubPDRS (PMerge p1 p2) gp     = isProperSubPDRS p1 gp && isProperSubPDRS p2 gp
        isProperSubPDRS lp@(PDRS _ _ _ cs) gp = all properCon cs
          where properCon :: PCon -> Bool
                properCon (PCon p (Rel _ d))    = all (\d' -> pdrsBoundPRef (PRef p d') lp gp) d
                properCon (PCon _ (Neg p1))     = isProperSubPDRS p1 gp
                properCon (PCon _ (Imp p1 p2))  = isProperSubPDRS p1 gp && isProperSubPDRS p2 gp
                properCon (PCon _ (Or p1 p2))   = isProperSubPDRS p1 gp && isProperSubPDRS p2 gp
                properCon (PCon p (Prop r p1))  = pdrsBoundPRef (PRef p r) lp gp && isProperSubPDRS p1 gp
                properCon (PCon _ (Diamond p1)) = isProperSubPDRS p1 gp
                properCon (PCon _ (Box p1))     = isProperSubPDRS p1 gp

---------------------------------------------------------------------------
-- | Returns whether a 'PDRS' is /pure/, where:
--
-- [A 'PDRS' @p@ is pure /iff/]
--
--  * @p@ does not contain any duplicate (otiose) variables
---------------------------------------------------------------------------
isPurePDRS :: PDRS -> Bool
isPurePDRS p = p == pdrsPurify p

---------------------------------------------------------------------------
-- | Returns whether a 'PDRS' is /presuppositional/, where:
--
-- [A 'PDRS' @p@ is presuppositional /iff/]
--
--  * @p@ contains free pointers
---------------------------------------------------------------------------
isPresupPDRS :: PDRS -> Bool
isPresupPDRS (LambdaPDRS{}) = False
isPresupPDRS (AMerge p1 p2) = isPresupPDRS p1 || isPresupPDRS p2
isPresupPDRS (PMerge{})     = True
isPresupPDRS p@(PDRS{})     = any (`pdrsIsFreePVar` p) (pdrsPVars p)

isSimplePDRS :: PDRS -> Bool
isSimplePDRS = not . isPresupPDRS

---------------------------------------------------------------------------
-- | Returns whether a 'PDRS' is /plain/, where:
--
-- [A 'PDRS' @p@ is plain /iff/]
--
--  * all projection pointers in @p@ are locally bound
---------------------------------------------------------------------------
isPlainPDRS :: PDRS -> Bool
isPlainPDRS (LambdaPDRS{}) = True
isPlainPDRS (AMerge p1 p2) = isPlainPDRS p1 && isPlainPDRS p2
isPlainPDRS (PMerge{})     = False
isPlainPDRS (PDRS l _ u c) = all (\(PRef p _) -> p==l) u && all plain c
  where plain :: PCon -> Bool
        plain (PCon p (Rel{}))      = p==l
        plain (PCon p (Neg p1))     = p==l && isPlainPDRS p1
        plain (PCon p (Imp p1 p2))  = p==l && isPlainPDRS p1 && isPlainPDRS p2
        plain (PCon p (Or p1 p2))   = p==l && isPlainPDRS p1 && isPlainPDRS p2
        plain (PCon p (Prop _ p1))  = p==l && isPlainPDRS p1
        plain (PCon p (Diamond p1)) = p==l && isPlainPDRS p1
        plain (PCon p (Box p1))     = p==l && isPlainPDRS p1

---------------------------------------------------------------------------
-- | Disjoins 'unresolved PDRS' @n1@ from 'unresolved PDRS' @n2@.
---------------------------------------------------------------------------
pdrsIsDifferentNP :: ((PDRSRef -> PDRS) -> PDRS) -> ((PDRSRef -> PDRS) -> PDRS) -> (PDRSRef -> PDRS) -> PDRS
pdrsIsDifferentNP n1 n2 = pdrsUnresolve (pdrsDisjoin n1' n2') i
  where n1' = pdrsResolveMerges (n1 (\x -> LambdaPDRS (("t",[pdrsRefToDRSVar x]),i)))
        n2' = pdrsResolveMerges (n2 (\x -> LambdaPDRS (("t",[pdrsRefToDRSVar x]),0)))
        i   = maximum (map snd (pdrsLambdas (n1 (\x -> LambdaPDRS (("t",[]),0))))) + 1

---------------------------------------------------------------------------
-- | Equates 'unresolved PDRS' @n1@ with 'unresolved PDRS' @n2@ in terms of
-- its label and NP head.
---------------------------------------------------------------------------
pdrsIsSameNP :: ((PDRSRef -> PDRS) -> PDRS) -> ((PDRSRef -> PDRS) -> PDRS) -> (PDRSRef -> PDRS) -> PDRS
pdrsIsSameNP n1 n2 = pdrsUnresolve (pdrsAlphaConvert n1' [(pdrsLabel n1',pdrsLabel n2')] [(npHead n1,npHead n2)]) i
  where n1' = pdrsResolveMerges (n1 (\x -> LambdaPDRS (("t",[pdrsRefToDRSVar x]),i)))
        n2' = pdrsResolveMerges (n2 (\x -> LambdaPDRS (("t",[pdrsRefToDRSVar x]),0)))
        i   = maximum (map snd (pdrsLambdas (n1 (\x -> LambdaPDRS (("t",[]),0)))) `union` map snd (pdrsLambdas n2')) + 1

---------------------------------------------------------------------------
-- * Private
---------------------------------------------------------------------------

---------------------------------------------------------------------------
-- | Converts a PDRS that contains a 'LambdaPDRS' whose argument position
-- @li@ equals some 'Int' @i@ into an 'unresolved PDRS'.
---------------------------------------------------------------------------
pdrsUnresolve :: PDRS -> Int -> (PDRSRef -> PDRS) -> PDRS
pdrsUnresolve lp@(LambdaPDRS ((_,r),li)) i k 
  | li == i   = k (PDRSRef $ head r)
  | otherwise = lp
pdrsUnresolve (AMerge p1 p2) i k = AMerge (pdrsUnresolve p1 i k) (pdrsUnresolve p2 i k)
pdrsUnresolve (PMerge p1 p2) i k = PMerge (pdrsUnresolve p1 i k) (pdrsUnresolve p2 i k)
pdrsUnresolve (PDRS l m u c) i k = PDRS l m u (replaceLambda c k)
  where replaceLambda :: [PCon] -> (PDRSRef -> PDRS) -> [PCon]
        replaceLambda [] k                        = []
        replaceLambda (pc@(PCon _ (Rel{})):pcs) k = pc:replaceLambda pcs k
        replaceLambda (PCon p (Neg p1):pcs)     k = PCon p (Neg     (pdrsUnresolve p1 i k)):replaceLambda pcs k
        replaceLambda (PCon p (Imp p1 p2):pcs)  k = PCon p (Imp     (pdrsUnresolve p1 i k) (pdrsUnresolve p2 i k)):replaceLambda pcs k
        replaceLambda (PCon p (Or p1 p2):pcs)   k = PCon p (Or      (pdrsUnresolve p1 i k) (pdrsUnresolve p2 i k)):replaceLambda pcs k
        replaceLambda (PCon p (Prop r p1):pcs)  k = PCon p (Prop r  (pdrsUnresolve p1 i k)):replaceLambda pcs k
        replaceLambda (PCon p (Diamond p1):pcs) k = PCon p (Diamond (pdrsUnresolve p1 i k)):replaceLambda pcs k
        replaceLambda (PCon p (Box p1):pcs)     k = PCon p (Box     (pdrsUnresolve p1 i k)):replaceLambda pcs k

---------------------------------------------------------------------------
-- | Returns the head of 'unresolved PDRS' @np@, where the head of an NP is
-- defined as the main referent that is passed on to its argument.
---------------------------------------------------------------------------
npHead :: ((PDRSRef -> PDRS) -> PDRS) -> PDRSRef
npHead np = retrieveLambda (pdrsLambdas (np (\x -> LambdaPDRS (("t",[pdrsRefToDRSVar x]),i))))
  where i = maximum (map snd (pdrsLambdas (np (\x -> LambdaPDRS (("t",[]),0))))) + 1
        retrieveLambda :: [((DRSVar,[DRSVar]),Int)] -> PDRSRef
        retrieveLambda (((_,r),li):ls)
          | li == i   = PDRSRef (head r)
          | otherwise = retrieveLambda ls


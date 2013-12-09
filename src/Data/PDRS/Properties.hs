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
  isPresupPDRS
, pdrsIsDifferentNP
) where

import Data.DRS.Variables (drsRefToDRSVar)
import Data.PDRS.Binding
import Data.PDRS.DataType
import Data.PDRS.Merge
import Data.PDRS.Variables

---------------------------------------------------------------------------
-- * Exported
---------------------------------------------------------------------------

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

---------------------------------------------------------------------------
-- | Disjoins 'unresolved PDRS' @n1@ from 'unresolved PDRS' @n2@.
---------------------------------------------------------------------------
pdrsIsDifferentNP :: ((PDRSRef -> PDRS) -> PDRS) -> ((PDRSRef -> PDRS) -> PDRS) -> (PDRSRef -> PDRS) -> PDRS
pdrsIsDifferentNP n1 n2 = pdrsUnresolve (pdrsDisjoin n1' n2') i
  where n1' = n1 (\x -> LambdaPDRS (("t",[pdrsRefToDRSVar x]),i))
        n2' = n2 (\x -> LambdaPDRS (("t",[pdrsRefToDRSVar x]),0))
        i   = maximum (map snd (pdrsLambdas (n1 (\x -> LambdaPDRS (("t",[]),0))))) + 1

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

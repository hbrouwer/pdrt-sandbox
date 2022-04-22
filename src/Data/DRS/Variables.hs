{- |
Module      :  Data.DRS.Variables
Copyright   :  (c) Harm Brouwer and Noortje Venhuizen
License     :  Apache-2.0

Maintainer  :  me@hbrouwer.eu, n.j.venhuizen@rug.nl
Stability   :  provisional
Portability :  portable

DRS variables
-}

module Data.DRS.Variables
(
-- * Conversion
  drsRefToDRSVar
, drsRelToString
-- * New Variables
, newDRSRefs
-- * Variable Collections
, drsUniverse
, drsConditions
, drsUniverses
, drsVariables
, drsLambdas
) where

import Data.Char (isDigit)
import Data.DRS.DataType
import Data.List (sortBy, union)
import Data.Ord (comparing)

---------------------------------------------------------------------------
-- * Exported
---------------------------------------------------------------------------

---------------------------------------------------------------------------
-- ** Conversion
---------------------------------------------------------------------------

---------------------------------------------------------------------------
-- | Converts a 'DRSRef' @r@ into a 'DRSVar'.
---------------------------------------------------------------------------
drsRefToDRSVar :: DRSRef -> DRSVar
drsRefToDRSVar (LambdaDRSRef ((r,_),_)) = r
drsRefToDRSVar (DRSRef r)               = r

---------------------------------------------------------------------------
-- | Converts a 'DRSRef' @r@ into a 'DRSVar'.
---------------------------------------------------------------------------
drsRelToString :: DRSRel -> String
drsRelToString (LambdaDRSRel ((r,_),_)) = r
drsRelToString (DRSRel r)               = r

---------------------------------------------------------------------------
-- ** New Variables
---------------------------------------------------------------------------

---------------------------------------------------------------------------
-- | Returns a list of new 'DRSRef's, based on a list of old 'DRSRef's and
-- a list of existing 'DRSRef's.
---------------------------------------------------------------------------
newDRSRefs :: [DRSRef] -> [DRSRef] -> [DRSRef]
newDRSRefs [] _    = []
newDRSRefs (r:ors) ers
  | r' `elem` (ors `union` ers) = newDRSRefs (r':ors) ers
  | otherwise                   = r':newDRSRefs ors (r':ers)
  where r' = case r of 
          (LambdaDRSRef ((dv,dvs),lp)) -> LambdaDRSRef ((increase dv,dvs),lp)
          (DRSRef dv)                  -> DRSRef       (increase dv)

---------------------------------------------------------------------------
-- ** Variable Collections
---------------------------------------------------------------------------

---------------------------------------------------------------------------
-- | Returns the list of 'DRSRef's from the top-level universe in a 'DRS'.
---------------------------------------------------------------------------
drsUniverse :: DRS -> [DRSRef]
drsUniverse (LambdaDRS _) = []
drsUniverse (Merge d1 d2) = drsUniverse d1 ++ drsUniverse d2
drsUniverse (DRS u _)     = u

---------------------------------------------------------------------------
-- | Returns the list of 'DRSCon's in a 'DRS'.
---------------------------------------------------------------------------
drsConditions :: DRS -> [DRSCon]
drsConditions (LambdaDRS _) = []
drsConditions (Merge d1 d2) = drsConditions d1 ++ drsConditions d2
drsConditions (DRS _ c)     = c

---------------------------------------------------------------------------
-- | Returns the list of 'DRSRef's from all universes in a 'DRS'.
---------------------------------------------------------------------------
drsUniverses :: DRS -> [DRSRef]
drsUniverses (LambdaDRS _) = []
drsUniverses (Merge d1 d2) = drsUniverses d1 ++ drsUniverses d2
drsUniverses (DRS u c)     = u ++ universes c
  where universes :: [DRSCon] -> [DRSRef]
        universes []              = []
        universes (Rel _ _:cs)    = universes cs
        universes (Neg d1:cs)     = drsUniverses d1 ++ universes cs
        universes (Imp d1 d2:cs)  = drsUniverses d1 ++ drsUniverses d2 ++ universes cs
        universes (Or d1 d2:cs)   = drsUniverses d1 ++ drsUniverses d2 ++ universes cs
        universes (Prop _ d1:cs)  = drsUniverses d1 ++ universes cs
        universes (Diamond d1:cs) = drsUniverses d1 ++ universes cs
        universes (Box d1:cs)     = drsUniverses d1 ++ universes cs

---------------------------------------------------------------------------
-- | Returns the list of all 'DRSRef's in a 'DRS' (equals 'drsUniverses'
-- ++ drsFreeRefs).
---------------------------------------------------------------------------
drsVariables :: DRS -> [DRSRef]
drsVariables (LambdaDRS _) = []
drsVariables (Merge d1 d2) = drsVariables d1 `union` drsVariables d2
drsVariables (DRS u c)     = u `union` variables c
  where variables :: [DRSCon] -> [DRSRef]
        variables []              = []
        variables (Rel _ d:cs)    = d `union` variables cs
        variables (Neg d1:cs)     = drsVariables d1 `union` variables cs
        variables (Imp d1 d2:cs)  = drsVariables d1 `union` drsVariables d2 `union` variables cs
        variables (Or d1 d2:cs)   = drsVariables d1 `union` drsVariables d2 `union` variables cs
        variables (Prop r d1:cs)  = [r]             `union` drsVariables d1 `union` variables cs
        variables (Diamond d1:cs) = drsVariables d1 `union` variables cs
        variables (Box d1:cs)     = drsVariables d1 `union` variables cs

---------------------------------------------------------------------------
-- | Returns the ordered list of all lambda variables in a 'DRS'.
---------------------------------------------------------------------------
drsLambdas :: DRS -> [(DRSVar,[DRSVar])]
drsLambdas d = map fst (sortBy (comparing snd) (lambdas d))

---------------------------------------------------------------------------
-- * Private
---------------------------------------------------------------------------

---------------------------------------------------------------------------
-- | Returns the list of all lambda tuples in a 'DRS'.
---------------------------------------------------------------------------
lambdas :: DRS -> [((DRSVar,[DRSVar]),Int)]
lambdas (LambdaDRS lt) = [lt]
lambdas (Merge d1 d2)  = lambdas d1 `union` lambdas d2
lambdas (DRS u c)      = lamRefs u  `union` lamCons c
  where lamRefs :: [DRSRef] -> [((DRSVar,[DRSVar]),Int)] 
        lamRefs []                   = []
        lamRefs (DRSRef _:ds)        = lamRefs ds
        lamRefs (LambdaDRSRef lt:ds) = lt : lamRefs ds
        lamCons :: [DRSCon] -> [((DRSVar,[DRSVar]),Int)]
        lamCons []              = []
        lamCons (Rel r d:cs)    = lamRel r    `union` lamRefs d  `union` lamCons cs
        lamCons (Neg d1:cs)     = lambdas d1  `union` lamCons cs
        lamCons (Imp d1 d2:cs)  = lambdas d1  `union` lambdas d2 `union` lamCons cs
        lamCons (Or d1 d2:cs)   = lambdas d1  `union` lambdas d2 `union` lamCons cs
        lamCons (Prop r d1:cs)  = lamRefs [r] `union` lambdas d1 `union` lamCons cs
        lamCons (Diamond d1:cs) = lambdas d1  `union` lamCons cs
        lamCons (Box d1:cs)     = lambdas d1  `union` lamCons cs
        lamRel :: DRSRel -> [((DRSVar,[DRSVar]),Int)]
        lamRel (LambdaDRSRel lt) = [lt]
        lamRel (DRSRel _)        = []

---------------------------------------------------------------------------
-- | Increases the index of a 'DRSVar' by 1, or adds an index to it.
---------------------------------------------------------------------------
increase :: DRSVar -> DRSVar
increase v = reverse (dropWhile isDigit (reverse v)) ++ i
  where i = case index v of
          Nothing -> show (1 :: Int)
          Just n  -> show (n + 1)
        index :: DRSVar -> Maybe Int
        index v' 
          | i' == ""   = Nothing
          | otherwise = Just $ read i'
          where i' = reverse (takeWhile isDigit (reverse v'))

{- |
Module      :  Data.FOL.Formula
Copyright   :  (c) Harm Brouwer and Noortje Venhuizen
License     :  Apache-2.0

Maintainer  :  me@hbrouwer.eu, n.j.venhuizen@rug.nl
Stability   :  provisional
Portability :  portable

FOL formula data structure
-}

module Data.FOL.Formula
( 
  FOLForm (..)
, FOLVar
, FOLPred
) where

---------------------------------------------------------------------------
-- * Exported
---------------------------------------------------------------------------

---------------------------------------------------------------------------
-- | First Order Logic formula
---------------------------------------------------------------------------
data FOLForm =
  Exists FOLVar FOLForm   -- ^ An existential quantification
  | ForAll FOLVar FOLForm -- ^ A universal quantification
  | And FOLForm FOLForm   -- ^ A conjunction
  | Or FOLForm FOLForm    -- ^ A disjunction
  | Imp FOLForm FOLForm   -- ^ An implication
  | Neg FOLForm           -- ^ A negation
  | Rel FOLPred [FOLVar]  -- ^ A relation
  | Top                   -- ^ True constant
  | Bottom                -- ^ False constant
  deriving (Eq)

---------------------------------------------------------------------------
-- | First Order Logic variable
---------------------------------------------------------------------------
type FOLVar = String

---------------------------------------------------------------------------
-- | First Order Logic predicate
---------------------------------------------------------------------------
type FOLPred = String

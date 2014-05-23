{- |
Module      :  Data.DRS
Copyright   :  (c) Harm Brouwer and Noortje Venhuizen
License     :  Apache-2.0

Maintainer  :  me@hbrouwer.eu, n.j.venhuizen@rug.nl
Stability   :  provisional
Portability :  portable

Discourse Representation Structure
-}

module Data.DRS 
( 
  module DRS
, showFOLForm
, printFOLForm
) where

import Data.DRS.Binding as DRS
import Data.DRS.DataType as DRS
import Data.DRS.Input as DRS
import Data.DRS.LambdaCalculus as DRS
import Data.DRS.Merge as DRS
import Data.DRS.Properties as DRS
import Data.DRS.Show as DRS
import Data.DRS.Structure as DRS
import Data.DRS.Translate as DRS
import Data.DRS.Variables as DRS

import Data.FOL (showFOLForm, printFOLForm)

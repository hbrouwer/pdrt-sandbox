{- |
Module      :  Data.DRS
Copyright   :  (c) Harm Brouwer and Noortje Venhuizen
License     :  Apache-2.0

Maintainer  :  me@hbrouwer.eu
Stability   :  provisional
Portability :  portable

Discourse Representation Structure
-}

module Data.DRS 
( 
  module Data.DRS
, module DRS
, showFOLForm
, printFOLForm
) where

import Data.DRS.AlphaConversion as DRS
import Data.DRS.Merge as DRS
import Data.DRS.Properties as DRS
import Data.DRS.Show as DRS
import Data.DRS.Structure as DRS
import Data.DRS.Translate as DRS
import Data.DRS.Variables as DRS

import Data.FOL (showFOLForm, printFOLForm)

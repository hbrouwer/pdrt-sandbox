-- DRS.hs

{- |
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

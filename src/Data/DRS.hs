-- DRS.hs

{- |
  Discourse Representation Structure
-}
module Data.DRS 
( 
  module Data.DRS
, module Data.DRS.AlphaConversion
, module Data.DRS.Merge
, module Data.DRS.Properties
, module Data.DRS.Show
, module Data.DRS.Structure
, module Data.DRS.Translate
, module Data.DRS.Variables

, showFOLForm
, printFOLForm

) where

import Data.DRS.AlphaConversion
import Data.DRS.Merge
import Data.DRS.Properties
import Data.DRS.Show
import Data.DRS.Structure
import Data.DRS.Translate
import Data.DRS.Variables

import Data.FOL (showFOLForm, printFOLForm)

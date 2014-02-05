{- |
Module      :  Data.PDRS.ProjectionGraph
Copyright   :  (c) Harm Brouwer and Noortje Venhuizen
License     :  Apache-2.0

Maintainer  :  me@hbrouwer.eu, n.j.venhuizen@rug.nl
Stability   :  provisional
Portability :  portable

PDRS projection graph
-}

module Data.PDRS.ProjectionGraph
(
  PGraph
, projectionGraph
, path
, vertices
, pdrsIsAccessibleContext
) where

import Data.Graph (buildG, Edge, Graph, path, vertices)
import Data.List (union)
import Data.PDRS.DataType
import Data.PDRS.Structure

---------------------------------------------------------------------------
-- * Exported
---------------------------------------------------------------------------

---------------------------------------------------------------------------
-- | Projection graph type
---------------------------------------------------------------------------
type PGraph = Graph

---------------------------------------------------------------------------
-- | Derives a 'PGraph' for 'PDRS' @p@
---------------------------------------------------------------------------
projectionGraph :: PDRS -> PGraph
projectionGraph p = buildG (minimum ps, maximum ps) es
  where es = edges p
        ps = map fst es `union` map snd es

---------------------------------------------------------------------------
-- | Returns whether 'PDRS' context @p2@ is accessible from 'PDRS' 
-- context @p1@ in PDRS @p@
---------------------------------------------------------------------------
pdrsIsAccessibleContext :: PVar -> PVar -> PDRS -> Bool
pdrsIsAccessibleContext p1 p2 p 
  | p1 `notElem` vs || p2 `notElem` vs = False
  | path pg p1 p2                      = True
  | otherwise                          = False
  where pg = projectionGraph p
        vs = vertices pg

---------------------------------------------------------------------------
-- * Private
---------------------------------------------------------------------------

---------------------------------------------------------------------------
-- | Derives a list of 'PGraph' edges from a 'PDRS'
---------------------------------------------------------------------------
edges :: PDRS -> [Edge]
edges (LambdaPDRS _) = []
edges (AMerge p1 p2) = edges p1 ++ edges p2
edges (PMerge p1 p2) = edges p1 ++ edges p2
edges (PDRS l m _ c) = ((l,l):m) `union` pconEdges c
  where pconEdges :: [PCon] -> [Edge]
        pconEdges [] = []
        pconEdges (PCon p (Rel _ _):cs) = (l,p):pconEdges cs
        pconEdges (PCon p (Neg p1):cs)
          | noEdges p1 = (l,p):pconEdges cs
          | otherwise  = ((pdrsLabel p1,p) : edges p1) `union` ((l,p):pconEdges cs)
        pconEdges (PCon p (Imp p1 p2):cs)
          | noEdges p1 && noEdges p2      = (l,p):pconEdges cs
          | not(noEdges p1) && noEdges p2 = ((pdrsLabel p1,p):edges p1) `union` ((l,p):pconEdges cs)
          | noEdges p1 && not(noEdges p2) = ((pdrsLabel p2,p):edges p2) `union` ((l,p):pconEdges cs)
          | otherwise                     = ((pdrsLabel p1,p):edges p1) `union` ((pdrsLabel p2,pdrsLabel p1):edges p2) `union` ((l,p):pconEdges cs)
        pconEdges (PCon p (Or p1 p2):cs)
          | noEdges p1 && noEdges p2      = (l,p):pconEdges cs
          | not(noEdges p1) && noEdges p2 = ((pdrsLabel p1,p):edges p1) `union` ((l,p):pconEdges cs)
          | noEdges p1 && not(noEdges p2) = ((pdrsLabel p2,p):edges p2) `union` ((l,p):pconEdges cs)
          | otherwise                     = ((pdrsLabel p1,p):edges p1) `union` ((pdrsLabel p2,p):edges p2) `union` ((l,p):pconEdges cs)
        pconEdges (PCon p (Prop _ p1):cs)
          | noEdges p1 = (l,p):pconEdges cs
          | otherwise  = ((pdrsLabel p1,p) : edges p1) `union` ((l,p):pconEdges cs)
        pconEdges (PCon p (Diamond p1):cs)
          | noEdges p1 = (l,p):pconEdges cs
          | otherwise  = ((pdrsLabel p1,p) : edges p1) `union` ((l,p):pconEdges cs)
        pconEdges (PCon p (Box p1):cs)
          | noEdges p1 = (l,p):pconEdges cs
          | otherwise  = ((pdrsLabel p1,p) : edges p1) `union` ((l,p):pconEdges cs)
        noEdges :: PDRS -> Bool
        noEdges (LambdaPDRS {}) = True
        noEdges (AMerge {})     = True
        noEdges (PMerge {})     = True
        noEdges (PDRS {})       = False

{- |
Module      :  Data.PDRS.ProjectionGraph
Copyright   :  (c) Harm Brouwer and Noortje Venhuizen
License     :  Apache-2.0

Maintainer  :  me@hbrouwer.eu
Stability   :  provisional
Portability :  portable

PDRS projection graph
-}

module Data.PDRS.ProjectionGraph
(
  projectionGraph
, path
, vertices
) where

import Data.PDRS.Structure
import Data.Graph (buildG, Edge, Graph, path, vertices)
import Data.List (union)

-- | Projectiong graph type
type PGraph = Graph

-- | Derives a projection graph for PDRS @p@
projectionGraph :: PDRS -> PGraph
projectionGraph p = buildG (minimum ps, maximum ps) es
  where es = edges p
        ps = map fst es `union` map snd es

-- | Derives a list of projection graph edges from a PDRS
edges :: PDRS -> [Edge]
edges (LambdaPDRS _) = []
edges (AMerge p1 p2) = edges p1 ++ edges p2
edges (PMerge p1 p2) = edges p1 ++ edges p2
edges (PDRS l m _ c) = ((l,l):m) `union` pconEdges c
  where pconEdges :: [PCon] -> [Edge]
        pconEdges [] = []
        pconEdges (PCon p (Rel _ _):cs) = pconEdges cs
        pconEdges (PCon p (Neg p1):cs)
          | noEdges p1 = pconEdges cs
          | otherwise  = ((pdrsLabel p1,p) : edges p1) `union` pconEdges cs
        pconEdges (PCon p (Imp p1 p2):cs)
          | noEdges p1 && noEdges p2      = pconEdges cs
          | not(noEdges p1) && noEdges p2 = ((pdrsLabel p1,p) : edges p1) `union` pconEdges cs
          | noEdges p1 && not(noEdges p2) = ((pdrsLabel p2,p) : edges p2) `union` pconEdges cs
          | otherwise                     = ((pdrsLabel p1,p) : edges p1) `union` ((pdrsLabel p2,pdrsLabel p1) : edges p2) `union` pconEdges cs
        pconEdges (PCon p (Or p1 p2):cs)
          | noEdges p1 && noEdges p2      = pconEdges cs
          | not(noEdges p1) && noEdges p2 = ((pdrsLabel p1,p) : edges p1) `union` pconEdges cs
          | noEdges p1 && not(noEdges p2) = ((pdrsLabel p2,p) : edges p2) `union` pconEdges cs
          | otherwise                     = ((pdrsLabel p1,p) : edges p1) `union` ((pdrsLabel p2,pdrsLabel p1) : edges p2) `union` pconEdges cs
        pconEdges (PCon p (Prop _ p1):cs)
          | noEdges p1 = pconEdges cs
          | otherwise  = ((pdrsLabel p1,p) : edges p1) `union` pconEdges cs
        pconEdges (PCon p (Diamond p1):cs)
          | noEdges p1 = pconEdges cs
          | otherwise  = ((pdrsLabel p1,p) : edges p1) `union` pconEdges cs
        pconEdges (PCon p (Box p1):cs)
          | noEdges p1 = pconEdges cs
          | otherwise  = ((pdrsLabel p1,p) : edges p1) `union` pconEdges cs
        noEdges :: PDRS -> Bool
        noEdges (LambdaPDRS {}) = True
        noEdges (AMerge {})     = True
        noEdges (PMerge {})     = True
        noEdges (PDRS {})       = False

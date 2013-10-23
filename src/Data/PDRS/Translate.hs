{- |
Module      :  Data.PDRS.Translate
Copyright   :  (c) Harm Brouwer and Noortje Venhuizen
License     :  Apache-2.0

Maintainer  :  me@hbrouwer.eu, n.j.venhuizen@rug.nl
Stability   :  provisional
Portability :  portable

PDRS accommodation, PDRS to FOL translation, and PDRS
to DRS translation
-}

module Data.PDRS.Translate
(
  pdrsToFOL
, pdrsToDRS
) where

import qualified Data.DRS.Structure as D
import Data.DRS.Translate (drsToFOL)
import qualified Data.FOL.Formula as F
import Data.PDRS.LambdaCalculus
import Data.PDRS.Merge
import Data.PDRS.ProjectionGraph
import Data.PDRS.Properties
import Data.PDRS.Structure
import Data.PDRS.Variables

import Data.List (delete, intersect, union)

---------------------------------------------------------------------------
-- * Exported
---------------------------------------------------------------------------

---------------------------------------------------------------------------
-- | Translates a 'PDRS' into a 'FOLForm'.
---------------------------------------------------------------------------
pdrsToFOL :: PDRS -> F.FOLForm
pdrsToFOL p = drsToFOL (pdrsToDRS p)

---------------------------------------------------------------------------
-- | Translates a PDRS into a DRS.
---------------------------------------------------------------------------
pdrsToDRS :: PDRS -> D.DRS
pdrsToDRS p = stripPVars $ movePContent gp (emptyPDRS gp) gp
  where gp = pdrsPurify (pdrsResolveMerges p)

---------------------------------------------------------------------------
-- * Private
---------------------------------------------------------------------------

---------------------------------------------------------------------------
-- | Moves projected content in 'PDRS' to its interpretation site in
-- 'PDRS' @p@ based on global 'PDRS' @gp@.
---------------------------------------------------------------------------
movePContent :: PDRS -> PDRS -> PDRS -> PDRS
movePContent lp@(LambdaPDRS _) _ _  = lp
movePContent (AMerge p1 p2)    p gp = movePContent p2 (movePContent p1 p gp) gp
movePContent (PMerge p1 p2)    p gp = movePContent p2 (movePContent p1 p gp) gp
movePContent (PDRS _ _ u c)    p gp = move c (insertPRefs u p gp)
  where move :: [PCon] -> PDRS -> PDRS
        move [] p                          = p
        move (pc@(PCon _ (Rel _ _)):pcs) p = move pcs (insertPCon pc p gp)
        move (PCon pv (Neg p1):pcs)      p = move pcs (movePContent p1 
          (insertPCon (PCon pv (Neg     (emptyPDRS p1))) p gp) gp)
        move (PCon pv (Imp p1 p2):pcs)   p = move pcs (movePContent p2 (movePContent p1
          (insertPCon (PCon pv (Imp (emptyPDRS p1) (emptyPDRS p2))) p gp) gp) gp)
        move (PCon pv (Or  p1 p2):pcs)   p = move pcs (movePContent p2 (movePContent p1
          (insertPCon (PCon pv (Or  (emptyPDRS p1) (emptyPDRS p2))) p gp) gp) gp)
        move (PCon pv (Prop r p1):pcs)   p = move pcs (movePContent p1
          (insertPCon (PCon pv (Prop r  (emptyPDRS p1))) p gp) gp)
        move (PCon pv (Diamond p1):pcs)  p = move pcs (movePContent p1
          (insertPCon (PCon pv (Diamond (emptyPDRS p1))) p gp) gp)
        move (PCon pv (Box p1):pcs)      p = move pcs (movePContent p1
          (insertPCon (PCon pv (Box     (emptyPDRS p1))) p gp) gp)

---------------------------------------------------------------------------
-- | Inserts projected referents @prs@ in a 'PDRS' @p@ at the correct
-- interpretation site, based on the global 'PDRS' @gp@.
---------------------------------------------------------------------------
insertPRefs :: [PRef] -> PDRS -> PDRS -> PDRS
insertPRefs [] pdrs _             = pdrs
insertPRefs _ lp@(LambdaPDRS _) _ = lp
insertPRefs prs (AMerge p1 p2) gp = AMerge (insertPRefs prs p1 gp) (insertPRefs prs p2 gp)
insertPRefs prs (PMerge p1 p2) gp = PMerge (insertPRefs prs p1 gp) (insertPRefs prs p2 gp)
insertPRefs (pr@(PRef pv _):prs) (PDRS l m u c) gp
  | pv == l || pdrsIsFreePVar pv gp    = insertPRefs prs (PDRS l m (u `union` [pr]) c) gp
  | otherwise                          = insertPRefs prs (PDRS l m u (map insert c))   gp
  where insert :: PCon -> PCon
        insert pc@(PCon _ (Rel _ _)) = pc
        insert (PCon p (Neg p1))     = PCon p (Neg     (insertPRefs [pr] p1 gp))
        insert (PCon p (Imp p1 p2))  = PCon p (Imp     (insertPRefs [pr] p1 gp) (insertPRefs [pr] p2 gp))
        insert (PCon p (Or p1 p2))   = PCon p (Or      (insertPRefs [pr] p1 gp) (insertPRefs [pr] p2 gp))
        insert (PCon p (Prop r p1))  = PCon p (Prop r  (insertPRefs [pr] p1 gp))
        insert (PCon p (Diamond p1)) = PCon p (Diamond (insertPRefs [pr] p1 gp))
        insert (PCon p (Box p1))     = PCon p (Box     (insertPRefs [pr] p1 gp))

---------------------------------------------------------------------------
-- | Inserts projected condition @pc@ in 'PDRS' @p@ at its interpretation
-- site, based on the global 'PDRS' @gp@.
---------------------------------------------------------------------------
insertPCon :: PCon -> PDRS -> PDRS -> PDRS
insertPCon _ lp@(LambdaPDRS _) _ = lp
insertPCon pc (AMerge p1 p2) gp = AMerge (insertPCon pc p1 gp) (insertPCon pc p2 gp)
insertPCon pc (PMerge p1 p2) gp = PMerge (insertPCon pc p1 gp) (insertPCon pc p2 gp)
insertPCon pc@(PCon pv _) pdrs@(PDRS l m u c) gp
  | pv == l || pdrsIsFreePVar pv gp = PDRS l m u (c ++ [pc])
  | otherwise                       = PDRS l m u (map insert c)
    where insert :: PCon -> PCon
          insert pc'@(PCon _ (Rel _ _)) = pc'
          insert (PCon p (Neg p1))     = PCon p (Neg     (insertPCon pc p1 gp))
          insert (PCon p (Imp p1 p2))  = PCon p (Imp     (insertPCon pc p1 gp) (insertPCon pc p2 gp))
          insert (PCon p (Or p1 p2))   = PCon p (Or      (insertPCon pc p1 gp) (insertPCon pc p2 gp))
          insert (PCon p (Prop r p1))  = PCon p (Prop r  (insertPCon pc p1 gp))
          insert (PCon p (Diamond p1)) = PCon p (Diamond (insertPCon pc p1 gp))
          insert (PCon p (Box p1))     = PCon p (Box     (insertPCon pc p1 gp))

---------------------------------------------------------------------------
-- | Returns an empty 'PDRS', if possible with the same label as 'PDRS' @p@.
---------------------------------------------------------------------------
emptyPDRS :: PDRS -> PDRS
emptyPDRS lp@(LambdaPDRS _) = lp
emptyPDRS (AMerge p1 p2)
  | isLambdaPDRS p1 = AMerge p1 (emptyPDRS p2)
  | isLambdaPDRS p2 = AMerge (emptyPDRS p1) p2
  | otherwise       = emptyPDRS (p1 <<+>> p2)
emptyPDRS (PMerge p1 p2)
  | isLambdaPDRS p1 = PMerge p1 (emptyPDRS p2)
  | isLambdaPDRS p2 = PMerge (emptyPDRS p1) p2
  | otherwise       = emptyPDRS (p1 <<*>> p2)
emptyPDRS (PDRS l _ _ _)    = PDRS l [] [] []

---------------------------------------------------------------------------
-- | Strips projection variables from a 'PDRS' @p@, resulting in a 'DRS'.
---------------------------------------------------------------------------
stripPVars :: PDRS -> D.DRS
stripPVars (LambdaPDRS lt) = D.LambdaDRS lt
stripPVars (AMerge p1 p2)  = D.Merge (stripPVars p1) (stripPVars p2)
stripPVars (PMerge p1 p2)  = D.Merge (stripPVars p1) (stripPVars p2)
stripPVars (PDRS _ _ u c)  = D.DRS (map (pdrsRefToDRSRef . (\(PRef _ r) -> r)) u) (map stripPCon c)
  where stripPCon :: PCon -> D.DRSCon
        stripPCon (PCon _ (Rel r d))    = D.Rel     r (map pdrsRefToDRSRef d)
        stripPCon (PCon _ (Neg p1))     = D.Neg     (stripPVars p1)
        stripPCon (PCon _ (Imp p1 p2))  = D.Imp     (stripPVars p1)     (stripPVars p2)
        stripPCon (PCon _ (Or p1 p2))   = D.Or      (stripPVars p1)     (stripPVars p2)
        stripPCon (PCon _ (Prop r p1))  = D.Prop    (pdrsRefToDRSRef r) (stripPVars p1)
        stripPCon (PCon _ (Diamond p1)) = D.Diamond (stripPVars p1)
        stripPCon (PCon _ (Box p1))     = D.Box     (stripPVars p1)

{- |
Module      :  Data.PDRS.Translate
Copyright   :  (c) Harm Brouwer and Noortje Venhuizen
License     :  Apache-2.0

Maintainer  :  me@hbrouwer.eu
Stability   :  provisional
Portability :  portable

PDRS accommodation, PDRS to FOL translation, and PDRS
to DRS translation
-}

module Data.PDRS.Translate
(
  accommodatePDRS
, pdrsToFOL
, pdrsToDRS
, pdrsToCleanPDRS
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

-- | Translates a *presuppositional PDRS*, a PDRS with free pointers, into
-- an *accommodated PDRS*, a PDRS without free pointers. This is achieved by
-- accommodating all presupposed content into the global context.
accommodatePDRS :: PDRS -> PDRS
accommodatePDRS lp@(LambdaPDRS _) = lp
accommodatePDRS (AMerge p1 p2)    = AMerge (accommodatePDRS p1) (accommodatePDRS p2)
accommodatePDRS (PMerge p1 p2)    = PMerge (accommodatePDRS p1) (accommodatePDRS p2)
accommodatePDRS p@(PDRS l _ _ _)  = pdrsAlphaConvert p (zip fps (replicate (length fps) l)) []
  where fps = filter (`pdrsIsFreePVar` p) (delete l (vertices pg))
        pg  = projectionGraph p

-- | Translates a PDRS into FOL
pdrsToFOL :: PDRS -> F.FOLForm
pdrsToFOL p = drsToFOL (pdrsToDRS p)

-- | Translates a PDRS into a DRS
pdrsToDRS :: PDRS -> D.DRS
pdrsToDRS p = stripPVars $ movePContent (emptyPDRS p) $ accommodatePDRS $ pdrsResolveMerges p

-- | Moves projected content in PDRS to its interpretation site in PDRS @p@
movePContent :: PDRS -> PDRS -> PDRS
movePContent lp@(LambdaPDRS _) _ = lp
movePContent (AMerge p1 p2)    p = movePContent p2 (movePContent p1 p)
movePContent (PMerge p1 p2)    p = movePContent p2 (movePContent p1 p)
movePContent (PDRS _ _ u c)    p = movePCons c (movePRefs u p)

-- | Moves projected referents to their interpretation site in PDRS @p@
movePRefs :: [PRef] -> PDRS -> PDRS
movePRefs [] p                   = p
movePRefs (pr@(PRef pv d):prs) p = movePRefs prs (insertPRef pr p)

-- | Inserts projected referent @pr@ in PDRS @p@ at its interpretation site
insertPRef :: PRef -> PDRS -> PDRS
insertPRef _ lp@(LambdaPDRS _) = lp
insertPRef pr (AMerge p1 p2)   = AMerge (insertPRef pr p1) (insertPRef pr p2)
insertPRef pr (PMerge p1 p2)   = PMerge (insertPRef pr p1) (insertPRef pr p2)
insertPRef pr@(PRef pv _) (PDRS l m u c)
  | l == pv   = PDRS l m (u `union` [pr]) c
  | otherwise = PDRS l m u (map insert c)
    where insert :: PCon -> PCon
          insert pc@(PCon _ (Rel _ _)) = pc
          insert (PCon p (Neg p1))     = PCon p (Neg     (insertPRef pr p1))
          insert (PCon p (Imp p1 p2))  = PCon p (Imp     (insertPRef pr p1) (insertPRef pr p1))
          insert (PCon p (Or p1 p2))   = PCon p (Or      (insertPRef pr p1) (insertPRef pr p1))
          insert (PCon p (Prop r p1))  = PCon p (Prop r  (insertPRef pr p1))
          insert (PCon p (Diamond p1)) = PCon p (Diamond (insertPRef pr p1))
          insert (PCon p (Box p1))     = PCon p (Box     (insertPRef pr p1))

-- | Moves projected conditions to their interpretation site in PDRS @p@
movePCons :: [PCon] -> PDRS -> PDRS
movePCons [] p = p
movePCons (pc@(PCon _ (Rel _ _)):pcs) p = movePCons pcs (insertPCon pc p)
movePCons (PCon pv (Neg p1):pcs)      p = movePCons pcs (movePContent p1 (insertPCon (PCon pv (Neg     (emptyPDRS p1))) p))
movePCons (PCon pv (Imp p1 p2):pcs)   p = movePCons pcs (movePContent p1 (insertPCon (PCon pv (Imp     (emptyPDRS p1) (emptyPDRS p2))) p))
movePCons (PCon pv (Or  p1 p2):pcs)   p = movePCons pcs (movePContent p1 (insertPCon (PCon pv (Or      (emptyPDRS p1) (emptyPDRS p2))) p))
movePCons (PCon pv (Prop r p1):pcs)   p = movePCons pcs (movePContent p1 (insertPCon (PCon pv (Prop r  (emptyPDRS p1))) p))
movePCons (PCon pv (Diamond p1):pcs)  p = movePCons pcs (movePContent p1 (insertPCon (PCon pv (Diamond (emptyPDRS p1))) p))
movePCons (PCon pv (Box p1):pcs)      p = movePCons pcs (movePContent p1 (insertPCon (PCon pv (Box     (emptyPDRS p1))) p))

-- | Inserts projected condition @pc@ in PDRS @p@ at its interpretation site
insertPCon :: PCon -> PDRS -> PDRS
insertPCon _ lp@(LambdaPDRS _) = lp
insertPCon pc (AMerge p1 p2)   = AMerge (insertPCon pc p1) (insertPCon pc p2)
insertPCon pc (PMerge p1 p2)   = PMerge (insertPCon pc p1) (insertPCon pc p2)
insertPCon pc@(PCon pv _) (PDRS l m u c)
  | l == pv   = PDRS l m u (c ++ [pc])
  | otherwise = PDRS l m u (map insert c)
    where insert :: PCon -> PCon
          insert pc@(PCon _ (Rel _ _)) = pc
          insert (PCon p (Neg p1))     = PCon p (Neg     (insertPCon pc p1))
          insert (PCon p (Imp p1 p2))  = PCon p (Imp     (insertPCon pc p1) (insertPCon pc p1))
          insert (PCon p (Or p1 p2))   = PCon p (Or      (insertPCon pc p1) (insertPCon pc p1))
          insert (PCon p (Prop r p1))  = PCon p (Prop r  (insertPCon pc p1))
          insert (PCon p (Diamond p1)) = PCon p (Diamond (insertPCon pc p1))
          insert (PCon p (Box p1))     = PCon p (Box     (insertPCon pc p1))

-- | Returns an empty PDRS, if possible with the same label as PDRS @p@
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

-- | Strips projection variables from a PDRS @p@, resulting in a DRS
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

-----------------------------------------------------------------------------
-----------------------------------------------------------------------------

pdrsToCleanPDRS :: PDRS -> PDRS
pdrsToCleanPDRS gp = cleanPRefs cgp cgp (zip prs (newPRefs prs [] (pdrsVariables cgp)))
  where cgp = fst $ cleanPVars (gp,[]) gp
        prs = unboundDupPRefs cgp cgp []

cleanPRefs :: PDRS -> PDRS -> [(PRef,PRef)] -> PDRS
cleanPRefs lp@(LambdaPDRS _) _  _   = lp
cleanPRefs (AMerge p1 p2)    gp prs = AMerge (cleanPRefs p1 gp prs) (cleanPRefs p2 gp prs)
cleanPRefs (PMerge p1 p2)    gp prs = PMerge (cleanPRefs p1 gp prs) (cleanPRefs p2 gp prs)
cleanPRefs lp@(PDRS l m u c) gp prs = PDRS l m (map (convert prs) u) (map clean c)
  where convert :: [(PRef,PRef)] -> PRef -> PRef
        convert [] pr                                  = pr
        convert  ((PRef p' r',npr):prs) pr@(PRef p r)
          | r == r' && pdrsIsAccessibleContext p p' gp = npr
          | otherwise                                  = convert prs pr
        clean :: PCon -> PCon
        clean (PCon p (Rel r d))    = PCon p (Rel     r (map (prefToPDRSRef . convert prs . (`pdrsRefToPRef` p)) d))
        clean (PCon p (Neg p1))     = PCon p (Neg     (cleanPRefs p1 gp prs))
        clean (PCon p (Imp p1 p2))  = PCon p (Imp     (cleanPRefs p1 gp prs) (cleanPRefs p2 gp prs))
        clean (PCon p (Or  p1 p2))  = PCon p (Or      (cleanPRefs p1 gp prs) (cleanPRefs p2 gp prs))
        clean (PCon p (Prop r p1))  = PCon p (Prop    (prefToPDRSRef (convert prs (pdrsRefToPRef r p))) (cleanPRefs p1 gp prs))
        clean (PCon p (Diamond p1)) = PCon p (Diamond (cleanPRefs p1 gp prs))
        clean (PCon p (Box p1))     = PCon p (Box     (cleanPRefs p1 gp prs))

cleanPVars :: (PDRS,[PVar]) -> PDRS -> (PDRS,[PVar])
cleanPVars (lp@(LambdaPDRS _),pvs) _  = (lp,pvs)
cleanPVars (AMerge p1 p2,pvs)      gp = (AMerge cp1 cp2,pvs2)
  where (cp1,pvs1) = cleanPVars (p1,pvs)  gp
        (cp2,pvs2) = cleanPVars (p2,pvs1) gp
cleanPVars (PMerge p1 p2,pvs)      gp = (PMerge cp1 cp2,pvs2)
  where (cp1,pvs1) = cleanPVars (p1,pvs)  gp
        (cp2,pvs2) = cleanPVars (p2,pvs1) gp
cleanPVars (lp@(PDRS l m u c),pvs) gp
  | l `elem` pvs   = cleanPVars (pdrsAlphaConvert lp [(l,l')] [],pvs) gp
  | otherwise      = (PDRS l m u ccs,pvs')
  where (l':[])    = newPVars [l] (pdrsPVars gp `union` pdrsPVars lp)
        (ccs,pvs') = clean (c,l:pvs `union` upv `union` mpv)
        upv = filter (not . flip (`pdrsBoundPVar` lp) gp) (map prefToPVar u)
        mpv = filter (not . flip (`pdrsBoundPVar` lp) gp) (concatMap (\(x,y) -> [x,y]) m)
        clean :: ([PCon],[PVar]) -> ([PCon],[PVar])
        clean tp@([],pvs)  = tp
        clean (pc@(PCon p (Rel _ _)):pcs,pvs) = (pc:ccs,pvs1)
          where (ccs,pvs1) = clean (pcs,addUnboundPVar p lp pvs)
        clean (PCon p (Neg p1):pcs,pvs)       = (PCon p (Neg cp1):ccs,pvs2)
          where (cp1,pvs1) = cleanPVars (p1,addUnboundPVar p lp pvs) gp
                (ccs,pvs2) = clean (pcs,pvs1)
        clean (PCon p (Imp p1 p2):pcs,pvs)    = (PCon p (Imp cp1 cp2):ccs,pvs4)
          where (cp1,pvs2) = cleanPVars (pdrsAlphaConvert p1 npv [],pvs1) gp
                (cp2,pvs3) = cleanPVars (pdrsAlphaConvert p2 npv [],pvs2) gp
                (ccs,pvs4) = clean (pcs,pvs3)
                pvs1 = addUnboundPVar p lp pvs
                opv  = pvs1 `intersect` [pdrsLabel p1]
                npv  = zip opv (newPVars opv (pdrsPVars gp `union` pdrsPVars lp))
        clean (PCon p (Or  p1 p2):pcs,pvs)    = (PCon p (Or cp1 cp2):ccs,pvs4)
          where (cp1,pvs2) = cleanPVars (pdrsAlphaConvert p1 npv [],pvs1) gp
                (cp2,pvs3) = cleanPVars (pdrsAlphaConvert p2 npv [],pvs2) gp
                (ccs,pvs4) = clean (pcs,pvs3)
                pvs1 = addUnboundPVar p lp pvs
                opv  = pvs1 `intersect` [pdrsLabel p1]
                npv  = zip opv (newPVars opv (pdrsPVars gp `union` pdrsPVars lp))
        clean (PCon p (Prop r p1):pcs,pvs)    = (PCon p (Prop r cp1):ccs,pvs2)
          where (cp1,pvs1) = cleanPVars (p1,addUnboundPVar p lp pvs) gp
                (ccs,pvs2) = clean (pcs,pvs1)
        clean (PCon p (Diamond p1):pcs,pvs)   = (PCon p (Diamond cp1):ccs,pvs2)
          where (cp1,pvs1) = cleanPVars (p1,addUnboundPVar p lp pvs) gp
                (ccs,pvs2) = clean (pcs,pvs1)
        clean (PCon p (Box p1):pcs,pvs)       = (PCon p (Box cp1):ccs,pvs2)
          where (cp1,pvs1) = cleanPVars (p1,addUnboundPVar p lp pvs) gp
                (ccs,pvs2) = clean (pcs,pvs1)                
        addUnboundPVar :: PVar -> PDRS -> [PVar] -> [PVar]
        addUnboundPVar pv p pvs
          | not(pdrsBoundPVar pv p gp) = [pv] `union` pvs
          | otherwise                  = pvs

unboundDupPRefs :: PDRS -> PDRS -> [PRef] -> [PRef]
unboundDupPRefs (LambdaPDRS _) _ _    = []
unboundDupPRefs (AMerge p1 p2)    gp prs = unboundDupPRefs p1 gp prs ++ unboundDupPRefs p2 gp prs
unboundDupPRefs (PMerge p1 p2)    gp prs = unboundDupPRefs p1 gp prs ++ unboundDupPRefs p2 gp prs
unboundDupPRefs lp@(PDRS _ _ u c) gp prs = filter (dup prs) u ++ dups c (prs `union` u)
  where dup :: [PRef] -> PRef -> Bool
        dup [] _                                             = False
        dup (pr'@(PRef _ r'):prs) pr@(PRef _ r)
          | r == r' && not(pdrsPRefBoundByPRef pr lp pr' gp) = True
          | otherwise                                        = dup prs pr
        dups :: [PCon] -> [PRef] -> [PRef]
        dups [] _ = []
        dups (PCon p (Rel _ d):pcs)    prs = filter (dup prs) d'       ++ dups pcs (prs `union` d')
          where d' = map (`pdrsRefToPRef` p) d
        dups (PCon _ (Neg p1):pcs)     prs = unboundDupPRefs p1 gp prs ++ dups pcs (prs `union` pdrsPRefs p1)
        dups (PCon _ (Imp p1 p2):pcs)  prs = unboundDupPRefs p1 gp prs ++ unboundDupPRefs p2 gp prs ++ dups pcs (prs `union` pdrsUniverses p1 `union` pdrsUniverses p2)
        dups (PCon _ (Or p1 p2):pcs)   prs = unboundDupPRefs p1 gp prs ++ unboundDupPRefs p2 gp prs ++ dups pcs (prs `union` pdrsUniverses p1 `union` pdrsUniverses p2)
        dups (PCon p (Prop r p1):pcs)  prs = filter (dup prs) [r']     ++ unboundDupPRefs p1 gp prs ++ dups pcs (prs `union` [r']             `union` pdrsUniverses p1)
          where r' = pdrsRefToPRef r p
        dups (PCon _ (Diamond p1):pcs) prs = unboundDupPRefs p1 gp prs ++ dups pcs (prs `union` pdrsUniverses p1)
        dups (PCon _ (Box p1):pcs)     prs = unboundDupPRefs p1 gp prs ++ dups pcs (prs `union` pdrsUniverses p1)

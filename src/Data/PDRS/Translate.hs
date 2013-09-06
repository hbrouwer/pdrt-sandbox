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

import Data.List (delete, union)

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

-- | NEW STUFFFFF

pdrsToCleanPDRS :: PDRS -> PDRS
pdrsToCleanPDRS gp = fst (cleanLabels (gp,[]))
  where cleanLabels :: (PDRS,[PVar]) -> (PDRS,[PVar])
        cleanLabels (lp@(LambdaPDRS _),pvs) = (lp,pvs)
        cleanLabels ((AMerge p1 p2),pvs)   = (AMerge (fst p1') (fst p2'),snd p2')
          where p1' = cleanLabels (p1,pvs)
                p2' = cleanLabels (p2,snd p1')
        cleanLabels ((PMerge p1 p2),pvs)   = (PMerge (fst p1') (fst p2'),snd p2')
          where p1' = cleanLabels (p1,pvs)
                p2' = cleanLabels (p2,snd p1')
        cleanLabels (pdrs@(PDRS l m u c),pvs)
          | l `elem` pvs = cleanLabels (pdrsAlphaConvert pdrs [(l,head (newPVars 1 pdrs pdrs))] [],pvs)
          | otherwise    = (PDRS l m u (fst c'),(snd c'))
          where c' = cleanCons (c,(l:pvs'))
                pvs' = pvs `union` map (\(PRef p _) -> p) (filter (\(PRef p _) -> pdrsIsFreePVar p gp) u)
                cleanCons :: ([PCon],[PVar]) -> ([PCon],[PVar])
                cleanCons ([],pvs)                          = ([],pvs)
                cleanCons ((pc@(PCon p (Rel _ _)):pcs),pvs) = (pc : (fst pcs'), (snd pcs'))
                  where pcs' = cleanCons (pcs,addFreeVariable p pvs)
                cleanCons ((PCon p (Neg p1):pcs),pvs)       = ((PCon p (Neg (fst p1')):(fst pcs')),(snd pcs'))
                  where p1'  = cleanLabels (p1,addFreeVariable p pvs)
                        pcs' = cleanCons (pcs,(snd p1'))
                cleanCons ((PCon p (Imp p1 p2):pcs),pvs)    = ((PCon p (Imp (fst p1') (fst p2')):(fst pcs')),(snd pcs'))
                  where p1l  = pdrsLabel p1
                        pvs' = addFreeVariable p pvs
                        p1'
                          | p1l `elem` pvs = cleanLabels (pdrsAlphaConvert p1 [(p1l,npv)] [],pvs')
                          | otherwise      = cleanLabels (p1,pvs')
                        p2'
                          | p1l `elem` pvs = cleanLabels (pdrsAlphaConvert p2 [(p1l,npv)] [],snd p1')
                          | otherwise      = cleanLabels (p2,snd p1')
                        pcs' = cleanCons (pcs,(snd p2'))  
                        npv  = head (newPVars 1 pdrs pdrs)
                cleanCons ((PCon p (Or p1 p2):pcs),pvs)     = ((PCon p (Or (fst p1') (fst p2')):(fst pcs')),(snd pcs'))
                  where p1l  = pdrsLabel p1
                        pvs' = addFreeVariable p pvs
                        p1'
                          | p1l `elem` pvs = cleanLabels (pdrsAlphaConvert p1 [(p1l,npv)] [],pvs')
                          | otherwise      = cleanLabels (p1,pvs')
                        p2'
                          | p1l `elem` pvs = cleanLabels (pdrsAlphaConvert p2 [(p1l,npv)] [],snd p1')
                          | otherwise      = cleanLabels (p2,snd p1')
                        pcs' = cleanCons (pcs,(snd p2'))  
                        npv  = head (newPVars 1 pdrs pdrs)
                cleanCons ((PCon p (Prop r p1):pcs),pvs)    = ((PCon p (Prop r (fst p1')):(fst pcs')),(snd pcs'))
                  where p1'  = cleanLabels (p1,addFreeVariable p pvs)
                        pcs' = cleanCons (pcs,(snd p1'))
                cleanCons ((PCon p (Diamond p1):pcs),pvs)   = ((PCon p (Diamond (fst p1')):(fst pcs')),(snd pcs'))
                  where p1'  = cleanLabels (p1,addFreeVariable p pvs)
                        pcs' = cleanCons (pcs,(snd p1'))
                cleanCons ((PCon p (Box p1):pcs),pvs)       = ((PCon p (Box (fst p1')):(fst pcs')),(snd pcs'))
                  where p1'  = cleanLabels (p1,addFreeVariable p pvs)
                        pcs' = cleanCons (pcs,(snd p1'))
                addFreeVariable :: PVar -> [PVar] -> [PVar]
                addFreeVariable p pvs
                  | not(pdrsIsFreePVar p gp) = pvs
                  | otherwise                = [p] `union` pvs


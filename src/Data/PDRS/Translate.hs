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

-- pdrsToCleanPDRS :: PDRS -> PDRS
-- pdrsToCleanPDRS gp = cleanPRefs gp' gp' cl
--   where gp' = fst (cleanPVars (gp,[]) gp)
--         cl  = zip prs (newPRefs prs [] (pdrsVariables gp'))
--        prs = unboundDupPRefs gp' gp' []

pdrsToCleanPDRS :: PDRS -> PDRS
pdrsToCleanPDRS gp = cleanPRefs cgp cgp (zip prs (newPRefs prs [] (pdrsVariables cgp)))
  where cgp = fst $ cleanPVars (gp,[]) gp
        prs = unboundDupPRefs cgp cgp []

-- cleanPVars :: (PDRS,[PVar]) -> PDRS -> (PDRS,[PVar])
-- cleanPVars (lp@(LambdaPDRS _),pvs) _ = (lp,pvs)
-- cleanPVars ((AMerge p1 p2),pvs) gp   = (AMerge (fst p1') (fst p2'),snd p2')
-- where p1' = cleanPVars (p1,pvs) gp
--         p2' = cleanPVars (p2,snd p1') gp
-- cleanPVars ((PMerge p1 p2),pvs) gp   = (PMerge (fst p1') (fst p2'),snd p2')
--   where p1' = cleanPVars (p1,pvs) gp
--         p2' = cleanPVars (p2,snd p1') gp
-- cleanPVars (pdrs@(PDRS l m u c),pvs) gp
--   | l `elem` pvs = cleanPVars (pdrsAlphaConvert pdrs [(l,head (newPVars [l] (pdrsPVars pdrs)))] [],pvs) gp
--   | otherwise    = (PDRS l m u (fst c'),(snd c'))
--   where c'   = cleanCons (c,(l:pvs'))
--         pvs' = pvs `union` u' `union` m'
--         u'   = map (\(PRef p _) -> p) (filter (\(PRef p _) -> not(pdrsBoundPVar p pdrs gp)) u)
--
--         m'   = filter (\(p) -> not (pdrsBoundPVar p pdrs gp)) (concatMap (\(p1,p2) -> [p1,p2]) m)
--      
--      cleanCons :: ([PCon],[PVar]) -> ([PCon],[PVar])
--         cleanCons ([],pvs)                          = ([],pvs)
--         cleanCons ((pc@(PCon p (Rel _ _)):pcs),pvs) = (pc : (fst pcs'), (snd pcs'))
--           where pcs' = cleanCons (pcs,(addFreePVar p pdrs pvs))
--         cleanCons ((PCon p (Neg p1):pcs),pvs)       = ((PCon p (Neg (fst p1')):(fst pcs')),(snd pcs'))
--           where p1'  = cleanPVars (p1,(addFreePVar p pdrs pvs)) gp
--                 pcs' = cleanCons (pcs,(snd p1'))
--         cleanCons ((PCon p (Imp p1 p2):pcs),pvs)    = ((PCon p (Imp (fst p1') (fst p2')):(fst pcs')),(snd pcs'))
--           where pvs' = addFreePVar p pdrs pvs
--                 opv  = pvs' `intersect` [pdrsLabel p1]
--                 npv  = zip opv (newPVars opv (pdrsPVars gp `union` pdrsPVars pdrs))
--                 p1'  = cleanPVars (pdrsAlphaConvert p1 npv [],pvs') gp
--                 p2'  = cleanPVars (pdrsAlphaConvert p2 npv [],snd p1') gp
--                 pcs' = cleanCons (pcs,(snd p2'))
--         cleanCons ((PCon p (Or p1 p2):pcs),pvs)     = ((PCon p (Or (fst p1') (fst p2')):(fst pcs')),(snd pcs'))
--           where pvs' = addFreePVar p pdrs pvs
--                 opv  = pvs' `intersect` [pdrsLabel p1]
--                 npv  = zip opv (newPVars opv (pdrsPVars gp `union` pdrsPVars pdrs))
--                 p1'  = cleanPVars (pdrsAlphaConvert p1 npv [],pvs') gp
--                 p2'  = cleanPVars (pdrsAlphaConvert p2 npv [],snd p1') gp
--                 pcs' = cleanCons (pcs,(snd p2'))
--         cleanCons ((PCon p (Prop r p1):pcs),pvs)    = ((PCon p (Prop r (fst p1')):(fst pcs')),(snd pcs'))
--           where p1'  = cleanPVars (p1,(addFreePVar p pdrs pvs)) gp
--                 pcs' = cleanCons (pcs,(snd p1'))
--         cleanCons ((PCon p (Diamond p1):pcs),pvs)   = ((PCon p (Diamond (fst p1')):(fst pcs')),(snd pcs'))
--           where p1'  = cleanPVars (p1,(addFreePVar p pdrs pvs)) gp
--                 pcs' = cleanCons (pcs,(snd p1'))
--         cleanCons ((PCon p (Box p1):pcs),pvs)       = ((PCon p (Box (fst p1')):(fst pcs')),(snd pcs'))
--           where p1'  = cleanPVars (p1,(addFreePVar p pdrs pvs)) gp
--                 pcs' = cleanCons (pcs,(snd p1'))
--         addFreePVar :: PVar -> PDRS -> [PVar] -> [PVar]
--         addFreePVar p pdrs pvs
--           | pdrsBoundPVar p pdrs gp = pvs
--           | otherwise               = [p] `union` pvs

cleanPVars :: (PDRS,[PVar]) -> PDRS -> (PDRS,[PVar])
cleanPVars (lp@(LambdaPDRS _),pvs) _  = (lp,pvs)
cleanPVars (AMerge p1 p2,pvs)      gp = (AMerge (fst cp1) (fst cp2),snd cp2)
  where cp1 = cleanPVars (p1,pvs)     gp
        cp2 = cleanPVars (p2,snd cp1) gp
cleanPVars (PMerge p1 p2,pvs)      gp = (PMerge (fst cp1) (fst cp2),snd cp2)
  where cp1 = cleanPVars (p1,pvs)     gp
        cp2 = cleanPVars (p2,snd cp1) gp
cleanPVars (lp@(PDRS l m u c),pvs) gp
  | l `elem` pvs   = cleanPVars (pdrsAlphaConvert lp [(l,l')] [],pvs) gp
  | otherwise      = (PDRS l m u ccs,pvs')
  where (l':[])    = newPVars [l] (pdrsPVars lp)
        (ccs,pvs') = clean (c,l:pvs `union` u' `union` m')
        u' = filter (not . ((flip ((flip pdrsBoundPVar) lp)) gp)) (map prefToPVar u)
        m' = filter (not . ((flip ((flip pdrsBoundPVar) lp)) gp)) (concatMap (\(x,y) -> [x,y]) m)
        clean :: ([PCon],[PVar]) -> ([PCon],[PVar])
        clean tp@([],pvs) = tp
        clean ((pc@(PCon p (Rel _ _)):pcs),pvs) = (pc:ccs,pvs1)
          where (ccs,pvs1) = clean (pcs,addUnboundPVar p lp pvs)
        clean ((PCon p (Neg p1):pcs),pvs)       = ((PCon p (Neg cp1):ccs),pvs2)
          where (cp1,pvs1) = cleanPVars (p1,(addUnboundPVar p lp pvs)) gp
                (ccs,pvs2) = clean (pcs,pvs1)
        clean ((PCon p (Imp p1 p2):pcs),pvs)    = ((PCon p (Imp cp1 cp2):ccs),pvs4)
          where (cp1,pvs2) = cleanPVars (pdrsAlphaConvert p1 npv [],pvs1) gp
                (cp2,pvs3) = cleanPVars (pdrsAlphaConvert p2 npv [],pvs2) gp
                (ccs,pvs4) = clean (pcs,pvs3)
                pvs1 = addUnboundPVar p lp pvs
                opv  = pvs' `intersect` [pdrsLabel p1]
                npv  = zip opv (newPVars opv (pdrsPVars gp `union` pdrsPVars lp))
        clean ((PCon p (Or  p1 p2):pcs),pvs)    = ((PCon p (Or cp1 cp2):ccs),pvs4)
          where (cp1,pvs2) = cleanPVars (pdrsAlphaConvert p1 npv [],pvs1) gp
                (cp2,pvs3) = cleanPVars (pdrsAlphaConvert p2 npv [],pvs2) gp
                (ccs,pvs4) = clean (pcs,pvs3)
                pvs1 = addUnboundPVar p lp pvs
                opv  = pvs' `intersect` [pdrsLabel p1]
                npv  = zip opv (newPVars opv (pdrsPVars gp `union` pdrsPVars lp))
        clean ((PCon p (Prop r p1):pcs),pvs)    = ((PCon p (Prop r cp1):ccs),pvs2)
          where (cp1,pvs1) = cleanPVars (p1,(addUnboundPVar p lp pvs)) gp
                (ccs,pvs2) = clean (pcs,pvs1)
        clean ((PCon p (Diamond p1):pcs),pvs)   = ((PCon p (Diamond cp1):ccs),pvs2)
          where (cp1,pvs1) = cleanPVars (p1,(addUnboundPVar p lp pvs)) gp
                (ccs,pvs2) = clean (pcs,pvs1)
        clean ((PCon p (Box p1):pcs),pvs)       = ((PCon p (Box cp1):ccs),pvs2)
          where (cp1,pvs1) = cleanPVars (p1,(addUnboundPVar p lp pvs)) gp
                (ccs,pvs2) = clean (pcs,pvs1)                
        addUnboundPVar :: PVar -> PDRS -> [PVar] -> [PVar]
        addUnboundPVar pv p pvs
          | not(pdrsBoundPVar pv p gp) = [pv] `union` pvs
          | otherwise                  = pvs

-- pdrsDupPRefs :: PDRS -> PDRS -> [PRef] -> [PRef]
-- pdrsDupPRefs (LambdaPDRS _) _ _       = []
-- pdrsDupPRefs (AMerge p1 p2) gp prs    = pdrsDupPRefs p1 gp prs ++ pdrsDupPRefs p2 gp prs
-- pdrsDupPRefs (PMerge p1 p2) gp prs    = pdrsDupPRefs p1 gp prs ++ pdrsDupPRefs p2 gp prs
-- pdrsDupPRefs lp@(PDRS _ _ u c) gp prs = dupPRefs u prs ++ consDupPRefs c (prs `union` u)
--   where dupPRefs :: [PRef] -> [PRef] -> [PRef]
--        dupPRefs [] _          = []
--        dupPRefs _ []          = []
--        dupPRefs (pr@(PRef _ r):prs) seen@(pr'@(PRef _ r'):prs')
--          | r == r' && not (pdrsPRefBoundByPRef pr lp pr' gp) = [pr] ++ (dupPRefs prs seen)
--          | otherwise                         = (dupPRefs [pr] prs') ++ (dupPRefs prs seen)
--        consDupPRefs :: [PCon] -> [PRef] -> [PRef]
--        consDupPRefs [] prs                          = []
--        consDupPRefs ((PCon p (Rel _ ds)):pcs) prs   = dupPRefs ds'' prs ++ consDupPRefs pcs (prs `union` ds'')
--          where ds'  = map (\(PDRSRef r) -> PRef p (PDRSRef r)) ds
--                ds'' = ds' \\ (filter ((flip ((flip pdrsBoundPRef) lp)) gp) ds')
--        consDupPRefs ((PCon _ (Neg p1)):pcs) prs     = pdrsDupPRefs p1 gp prs ++ consDupPRefs pcs (prs `union` pdrsPReferents p1)
--        consDupPRefs ((PCon _ (Imp p1 p2)):pcs) prs  = pdrsDupPRefs p1 gp prs ++ pdrsDupPRefs p2 gp prs' ++ consDupPRefs pcs (prs' `union` pdrsPReferents p2)
--          where prs' = prs `union` pdrsPReferents p1
--        consDupPRefs ((PCon _ (Or p1 p2)):pcs) prs   = pdrsDupPRefs p1 gp prs ++ pdrsDupPRefs p2 gp prs' ++ consDupPRefs pcs (prs' `union` pdrsPReferents p2)
--          where prs' = prs `union` pdrsPReferents p1
--        consDupPRefs ((PCon p (Prop d p1)):pcs) prs  = dupPRefs d' prs ++ pdrsDupPRefs p1 gp prs ++ consDupPRefs pcs (prs `union` pdrsPReferents p1)
--          where d'   = [PRef p d] \\ (filter ((flip ((flip pdrsBoundPRef) lp)) gp) [PRef p d])
--        consDupPRefs ((PCon _ (Diamond p1)):pcs) prs = pdrsDupPRefs p1 gp prs ++ consDupPRefs pcs (prs `union` pdrsPReferents p1)
--        consDupPRefs ((PCon _ (Box p1)):pcs) prs     = pdrsDupPRefs p1 gp prs ++ consDupPRefs pcs (prs `union` pdrsPReferents p1)

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
        dups ((PCon p (Rel _ d)):pcs)    prs = filter (dup prs) d'       ++ dups pcs (prs `union` d')
          where d' = map (flip pdrsRefToPRef p) d
        dups ((PCon _ (Neg p1)):pcs)     prs = unboundDupPRefs p1 gp prs ++ dups pcs (prs `union` pdrsPRefs p1)
        dups ((PCon _ (Imp p1 p2)):pcs)  prs = unboundDupPRefs p1 gp prs ++ unboundDupPRefs p2 gp prs ++ dups pcs (prs `union` pdrsPRefs p1 `union` pdrsPRefs p2)
        dups ((PCon _ (Or p1 p2)):pcs)   prs = unboundDupPRefs p1 gp prs ++ unboundDupPRefs p2 gp prs ++ dups pcs (prs `union` pdrsPRefs p1 `union` pdrsPRefs p2)
        dups ((PCon p (Prop r p1)):pcs)  prs = filter (dup prs) [r']     ++ unboundDupPRefs p1 gp prs ++ dups pcs (prs `union` [r']         `union` pdrsPRefs p1)
          where r' = pdrsRefToPRef r p
        dups ((PCon _ (Diamond p1)):pcs) prs = unboundDupPRefs p1 gp prs ++ dups pcs (prs `union` pdrsPRefs p1)
        dups ((PCon _ (Box p1)):pcs)     prs = unboundDupPRefs p1 gp prs ++ dups pcs (prs `union` pdrsPRefs p1)

-- cleanPRefs :: PDRS -> PDRS -> [(PRef,PRef)] -> PDRS
-- cleanPRefs lp@(LambdaPDRS _) _ _      = lp
-- cleanPRefs (AMerge p1 p2) gp prs      = AMerge (cleanPRefs p1 gp prs) (cleanPRefs p2 gp prs)
-- cleanPRefs (PMerge p1 p2) gp prs      = PMerge (cleanPRefs p1 gp prs) (cleanPRefs p2 gp prs)
-- cleanPRefs pdrs@(PDRS l m u c) gp prs = PDRS l m (map ((flip convertPRef) prs) u) (cleanCons c prs)
--   where convertPRef :: PRef -> [(PRef,PRef)] -> PRef
--         convertPRef pr [] = pr
--         convertPRef pr@(PRef p r) (((PRef p' r'),npr):rs)
--           | r == r' && pdrsIsAccessibleContext p p' pdrs = npr
--           | otherwise                                    = convertPRef pr rs
--         cleanCons :: [PCon] -> [(PRef,PRef)] -> [PCon]
--         cleanCons [] _ = []
--
--         cleanCons ((PCon p (Rel r u)):pcs) prs    = (PCon p (Rel     r u')):cleanCons pcs prs
--           where u' = map (\(PRef _ d) -> d) (map ((flip convertPRef) prs) (map (\(PDRSRef d) -> (PRef p (PDRSRef d))) u))
--         cleanCons ((PCon p (Neg p1)):pcs) prs     = (PCon p (Neg     (cleanPRefs p1 gp prs))):cleanCons pcs prs
--         cleanCons ((PCon p (Imp p1 p2)):pcs) prs  = (PCon p (Imp     (cleanPRefs p1 gp prs) (cleanPRefs p2 gp prs))):cleanCons pcs prs
--         cleanCons ((PCon p (Or p1 p2)):pcs) prs   = (PCon p (Or      (cleanPRefs p1 gp prs) (cleanPRefs p2 gp prs))):cleanCons pcs prs
--         cleanCons ((PCon p (Prop d p1)):pcs) prs  = (PCon p (Prop d' (cleanPRefs p1 gp prs))):cleanCons pcs prs
--           where d' = (\(PRef _ u) -> u) (convertPRef (PRef p d) prs)
--         cleanCons ((PCon p (Diamond p1)):pcs) prs = (PCon p (Diamond (cleanPRefs p1 gp prs))):cleanCons pcs prs
--         cleanCons ((PCon p (Box p1)):pcs) prs     = (PCon p (Box     (cleanPRefs p1 gp prs))):cleanCons pcs prs

cleanPRefs :: PDRS -> PDRS -> [(PRef,PRef)] -> PDRS
cleanPRefs lp@(LambdaPDRS _) _  _   = lp
cleanPRefs (AMerge p1 p2)    gp prs = AMerge (cleanPRefs p1 gp prs) (cleanPRefs p2 gp prs)
cleanPRefs (PMerge p1 p2)    gp prs = PMerge (cleanPRefs p1 gp prs) (cleanPRefs p2 gp prs)
cleanPRefs lp@(PDRS l m u c) gp prs = PDRS l m (map (convert prs) u) (map clean c)
  where convert :: [(PRef,PRef)] -> PRef -> PRef
        convert [] pr                                  = pr
        convert  (((PRef p' r'),npr):prs) pr@(PRef p r)
          | r == r' && pdrsIsAccessibleContext p p' lp = npr
          | otherwise                                  = convert prs pr
        clean :: PCon -> PCon
        clean (PCon p (Rel r d))    = PCon p (Rel     r (map prefToPDRSRef (map (convert prs) (map (flip pdrsRefToPRef p) d))))
        clean (PCon p (Neg p1))     = PCon p (Neg     (cleanPRefs p1 gp prs))
        clean (PCon p (Imp p1 p2))  = PCon p (Imp     (cleanPRefs p1 gp prs) (cleanPRefs p2 gp prs))
        clean (PCon p (Or  p1 p2))  = PCon p (Or      (cleanPRefs p1 gp prs) (cleanPRefs p2 gp prs))
        clean (PCon p (Prop r p1))  = PCon p (Prop    (prefToPDRSRef (convert prs (pdrsRefToPRef r p))) (cleanPRefs p1 gp prs))
        clean (PCon p (Diamond p1)) = PCon p (Diamond (cleanPRefs p1 gp prs))
        clean (PCon p (Box p1))     = PCon p (Box     (cleanPRefs p1 gp prs))

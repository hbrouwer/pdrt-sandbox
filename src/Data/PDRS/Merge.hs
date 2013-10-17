{- |
Module      :  Data.PDRS.Merge
Copyright   :  (c) Harm Brouwer and Noortje Venhuizen
License     :  Apache-2.0

Maintainer  :  me@hbrouwer.eu, n.j.venhuizen@rug.nl
Stability   :  provisional
Portability :  portable

PDRS merges
-}

module Data.PDRS.Merge (
  pdrsAMerge
, (<<+>>)
, pdrsPMerge
, (<<*>>)
, pdrsResolveMerges
, pdrsDisjoin
, pdrsToCleanPDRS
) where

import Data.PDRS.LambdaCalculus
import Data.PDRS.Properties
import Data.PDRS.Structure
import Data.PDRS.Variables

import Data.List (delete, intersect, nub, union)

-- | Applies assertive merge to PDRS @p1@ and PDRS @p2@
pdrsAMerge :: PDRS -> PDRS -> PDRS
pdrsAMerge p1 p2 = amerge rp1 (pdrsDisjoin rp2 (pdrsPVars rp1) (pdrsVariables rp1))
  where rp1 = pdrsToCleanPDRS $ pdrsResolveMerges p1
        rp2 = pdrsToCleanPDRS $ pdrsResolveMerges p2
        amerge :: PDRS -> PDRS -> PDRS
        amerge p (PDRS l m u c) = PDRS l (m `union` m') (u `union` u') (c `union` c')
          where (PDRS l' m' u' c') = pdrsAlphaConvert p [(pdrsLabel p,l)] []
        
-- | Infix notation for 'pdrsAMerge'
(<<+>>) :: PDRS -> PDRS -> PDRS
p1 <<+>> p2 = p1 `pdrsAMerge` p2

-- | Applies projective merge to PDRS @p1@ and PDRS @p2@
pdrsPMerge :: PDRS -> PDRS -> PDRS
pdrsPMerge p1 p2 = pmerge rp1 (pdrsDisjoin rp2 (pdrsPVars rp1) (pdrsVariables rp1))
  where rp1 = pdrsToCleanPDRS $ pdrsResolveMerges p1
        rp2 = pdrsToCleanPDRS $ pdrsResolveMerges p2
        pmerge :: PDRS -> PDRS -> PDRS
        pmerge (PDRS l1 m1 u1 c1) (PDRS l2 m2 u2 c2) = PDRS l2 m u c
          where m = m1 `union` (m2 ++ [(l2,l1)])
                u = u1 `union` u2
                c = c1 `union` c2

-- | Infix notation for 'pdrsPMerge'
(<<*>>) :: PDRS -> PDRS -> PDRS
p1 <<*>> p2 = p1 `pdrsPMerge` p2

-- | Resolves all unresolved merges in a PDRS
pdrsResolveMerges :: PDRS -> PDRS
pdrsResolveMerges lp@(LambdaPDRS _) = lp
pdrsResolveMerges (AMerge p1 p2)
  | isLambdaPDRS p1 || isLambdaPDRS p2 = AMerge p1 p2
  | otherwise                          = p1 <<+>> p2
pdrsResolveMerges (PMerge p1 p2)
  | isLambdaPDRS p1 || isLambdaPDRS p2 = PMerge p1 p2
  | otherwise                          = p1 <<*>> p2
pdrsResolveMerges (PDRS l m u c) = PDRS l m u (map resolve c)
  where resolve :: PCon -> PCon
        resolve pc@(PCon _ (Rel _ _)) = pc
        resolve (PCon p (Neg p1))     = PCon p (Neg     (pdrsResolveMerges p1))
        resolve (PCon p (Imp p1 p2))  = PCon p (Imp     (pdrsResolveMerges p1) (pdrsResolveMerges p2))
        resolve (PCon p (Or p1 p2))   = PCon p (Or      (pdrsResolveMerges p1) (pdrsResolveMerges p2))
        resolve (PCon p (Prop r p1))  = PCon p (Prop r  (pdrsResolveMerges p1))
        resolve (PCon p (Diamond p1)) = PCon p (Diamond (pdrsResolveMerges p1))
        resolve (PCon p (Box p1))     = PCon p (Box     (pdrsResolveMerges p1))

pdrsDisjoin :: PDRS -> [PVar] -> [PDRSRef] -> PDRS
pdrsDisjoin p pvs prs = pdrsAlphaConvert p (zip ops nps) (zip ors nrs)
  where ops = pvs `intersect` pdrsPVars p
        nps = newPVars ops (pvs `union` pdrsPVars p)
        ors = prs `intersect` pdrsVariables p
        nrs = newPDRSRefs ors (prs `union` pdrsVariables p)

pdrsToCleanPDRS :: PDRS -> PDRS
pdrsToCleanPDRS gp = cleanPRefs cgp cgp (zip prs (newPRefs prs (pdrsVariables cgp)))
  where cgp = fst $ cleanPVars (gp,[]) gp
        prs = snd $ unboundDupPRefs cgp cgp []

cleanPRefs :: PDRS -> PDRS -> [(PRef,PRef)] -> PDRS
cleanPRefs lp@(LambdaPDRS _) _  _   = lp
cleanPRefs (AMerge p1 p2)    gp prs = AMerge (cleanPRefs p1 gp prs) (cleanPRefs p2 gp prs)
cleanPRefs (PMerge p1 p2)    gp prs = PMerge (cleanPRefs p1 gp prs) (cleanPRefs p2 gp prs)
cleanPRefs lp@(PDRS l m u c) gp prs = PDRS l m (map (convert prs) u) (map clean c)
  where convert :: [(PRef,PRef)] -> PRef -> PRef
        convert [] pr                                   = pr
        convert  ((pr'@(PRef p' r'),npr):prs) pr@(PRef p r)
          | pr == pr'                                   = npr
          | r == r' && pdrsPRefBoundByPRef pr lp pr' gp = npr
          | otherwise                                   = convert prs pr
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
          where (cp1,pvs2) = cleanPVars (alphaConvertSubPDRS p1 gp npv [],pvs1) gp
                (cp2,pvs3) = cleanPVars (alphaConvertSubPDRS p2 gp npv [],pvs2) gp
                (ccs,pvs4) = clean (pcs,pvs3)
                pvs1 = addUnboundPVar p lp pvs
                opv  = pvs1 `intersect` [pdrsLabel p1]
                npv  = zip opv (newPVars opv (pdrsPVars gp `union` pdrsPVars lp))
        clean (PCon p (Or  p1 p2):pcs,pvs)    = (PCon p (Or cp1 cp2):ccs,pvs4)
          where (cp1,pvs2) = cleanPVars (alphaConvertSubPDRS p1 gp npv [],pvs1) gp
                (cp2,pvs3) = cleanPVars (alphaConvertSubPDRS p2 gp npv [],pvs2) gp
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

unboundDupPRefs :: PDRS -> PDRS -> [PRef] -> ([PRef],[PRef])
unboundDupPRefs (LambdaPDRS _)    _  eps = (eps,[])
unboundDupPRefs (AMerge p1 p2)    gp eps = (eps2,dps1 ++ dps2)
  where (eps1,dps1) = unboundDupPRefs p1 gp eps
        (eps2,dps2) = unboundDupPRefs p2 gp eps1
unboundDupPRefs (PMerge p1 p2)    gp eps = (eps2,dps1 ++ dps2)
  where (eps1,dps1) = unboundDupPRefs p1 gp eps
        (eps2,dps2) = unboundDupPRefs p2 gp eps1
unboundDupPRefs lp@(PDRS _ _ u c) gp eps = (eps1,filter (dup eps) u ++ dps1)
  where (eps1,dps1) = dups c (eps ++ unboundPRefs u)
        dup :: [PRef] -> PRef -> Bool
        dup [] _                                             = False
        dup (pr'@(PRef _ r'):prs) pr@(PRef _ r)
          | r == r' && not(pdrsPRefBoundByPRef pr lp pr' gp) = True
          | otherwise                                        = dup prs pr
        dups :: [PCon] -> [PRef] -> ([PRef],[PRef])
        dups [] eps = (eps,[])
        dups (PCon p (Rel _ d):pcs)     eps = (eps2,filter (dup eps) prs ++ dps2)
          where (eps2,dps2) = dups pcs (eps ++ unboundPRefs prs)
                prs = map (`pdrsRefToPRef` p) d
        dups (PCon p (Neg p1):pcs)     eps = (eps2,dps1 ++ dps2)
          where (eps1,dps1) = unboundDupPRefs p1 gp eps
                (eps2,dps2) = dups pcs eps1
        dups (PCon p (Imp p1 p2):pcs)  eps = (eps3,dps1 ++ dps2 ++ dps3)
          where (eps1,dps1) = unboundDupPRefs p1 gp eps
                (eps2,dps2) = unboundDupPRefs p2 gp eps1
                (eps3,dps3) = dups pcs eps2
        dups (PCon p (Or p1 p2):pcs)   eps = (eps3,dps1 ++ dps2 ++ dps3)
          where (eps1,dps1) = unboundDupPRefs p1 gp eps
                (eps2,dps2) = unboundDupPRefs p2 gp eps1
                (eps3,dps3) = dups pcs eps2
        dups (PCon p (Prop r p1):pcs)  eps = (eps3,dps1 ++ dps2 ++ dps3)
          where (eps1,dps1) = unboundDupPRefs p1 gp eps
                (eps2,dps2) = dups pcs eps1
                (eps3,dps3) = (eps2 ++ unboundPRefs [pr],filter (dup eps) [pr])
                pr          = pdrsRefToPRef r p
        dups (PCon p (Diamond p1):pcs) eps = (eps2,dps1 ++ dps2)
          where (eps1,dps1) = unboundDupPRefs p1 gp eps
                (eps2,dps2) = dups pcs eps1
        dups (PCon p (Box p1):pcs)     eps = (eps2,dps1 ++ dps2)
          where (eps1,dps1) = unboundDupPRefs p1 gp eps
                (eps2,dps2) = dups pcs eps1
        unboundPRefs :: [PRef] -> [PRef]
        unboundPRefs []                 = []
        unboundPRefs (pr:prs)
            | not $ any (flip (pdrsPRefBoundByPRef pr lp) gp) u = pr : unboundPRefs prs
            | otherwise                                         = unboundPRefs prs
            where u = delete pr (pdrsUniverses gp)

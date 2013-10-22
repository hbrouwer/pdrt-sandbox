{- |
Module      :  Data.PDRS.Merge
Copyright   :  (c) Harm Brouwer and Noortje Venhuizen
License     :  Apache-2.0

Maintainer  :  me@hbrouwer.eu, n.j.venhuizen@rug.nl
Stability   :  provisional
Portability :  portable

The module "Data.PDRS.Merge" contains functions required for merging 'PDRS's.
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

-- * Exported

---------------------------------------------------------------------------
-- | Applies assertive merge to 'PDRS' @p1@ and 'PDRS' @p2@.
---------------------------------------------------------------------------
pdrsAMerge :: PDRS -> PDRS -> PDRS
pdrsAMerge p1 p2 = amerge rp1 (pdrsDisjoin rp2 (pdrsPVars rp1) (pdrsVariables rp1))
  where rp1 = pdrsToCleanPDRS $ pdrsResolveMerges p1
        rp2 = pdrsToCleanPDRS $ pdrsResolveMerges p2
        -- ^ Merged 'PDRS's should be clean, with resolved merges.
        amerge :: PDRS -> PDRS -> PDRS
        amerge p (PDRS l m u c) = PDRS l (m `union` m') (u `union` u') (c `union` c')
          where (PDRS l' m' u' c') = pdrsAlphaConvert p [(pdrsLabel p,l)] []
                -- ^ Make sure all asserted content in 'PDRS' @p@ remains
                -- asserted by renaming global label to @l@ before merging.

-- | Infix notation for 'pdrsAMerge'
(<<+>>) :: PDRS -> PDRS -> PDRS
p1 <<+>> p2 = p1 `pdrsAMerge` p2

---------------------------------------------------------------------------
-- | Applies projective merge to 'PDRS' @p1@ and 'PDRS' @p2@.
---------------------------------------------------------------------------
pdrsPMerge :: PDRS -> PDRS -> PDRS
pdrsPMerge p1 p2 = pmerge rp1 (pdrsDisjoin rp2 (pdrsPVars rp1) (pdrsVariables rp1))
  where rp1 = pdrsToCleanPDRS $ pdrsResolveMerges p1
        rp2 = pdrsToCleanPDRS $ pdrsResolveMerges p2
        -- ^ Merged 'PDRS's should be clean, with resolved merges.
        pmerge :: PDRS -> PDRS -> PDRS
        pmerge (PDRS l m u c) (PDRS l' m' u' c') 
            = PDRS l' ((l',l):m `union` m') (u `union` u') (c `union` c')
        -- ^ Content of 'PDRS' @p@ is added to 'PDRS' @p'@ without
        -- replacing pointers, resulting in the content of @p@ becoming
        -- projected in the resulting 'PDRS'.

-- | Infix notation for 'pdrsPMerge'
(<<*>>) :: PDRS -> PDRS -> PDRS
p1 <<*>> p2 = p1 `pdrsPMerge` p2

---------------------------------------------------------------------------
-- | Resolves all unresolved merges in a 'PDRS'.
---------------------------------------------------------------------------
pdrsResolveMerges :: PDRS -> PDRS
pdrsResolveMerges lp@(LambdaPDRS _)    = lp
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

---------------------------------------------------------------------------
-- | Cleans a 'PDRS' @p@ on the basis of a given set 'PVar's @pvs@ and 
-- 'PDRSRef's @prs@.
---------------------------------------------------------------------------
pdrsDisjoin :: PDRS -> [PVar] -> [PDRSRef] -> PDRS
pdrsDisjoin p pvs prs = pdrsAlphaConvert p (zip ops nps) (zip ors nrs)
  where ops = pvs `intersect` pdrsPVars p
        nps = newPVars ops (pvs `union` pdrsPVars p)
        ors = prs `intersect` pdrsVariables p
        nrs = newPDRSRefs ors (prs `union` pdrsVariables p)

---------------------------------------------------------------------------
-- | Cleans a 'PDRS' by first cleaning its projection variables, and then
-- cleaning its projected referents, where:
--
-- [A 'PDRS' is clean /iff/:]
--
-- * There are no occurrences of duplicate, unbound uses of the same
--   variable ('PVar' or 'PDRSRef').
---------------------------------------------------------------------------
pdrsToCleanPDRS :: PDRS -> PDRS
pdrsToCleanPDRS gp = cleanPRefs cgp cgp (zip prs (newPRefs prs (pdrsVariables cgp)))
  where cgp = fst $ cleanPVars (gp,[]) gp
        prs = snd $ unboundDupPRefs cgp cgp []

-- * Private

---------------------------------------------------------------------------
-- | Cleans a 'PDRS' on the basis of a conversion list for 'PRefs' @prs@, where:
--
-- [Given conversion pair @(pr',npr)@, 'PRef' @pr@ is replaced by @npr@ /iff/]
--
-- * @pr@ equals @pr'@, or
--
-- * @pr@ and @pr'@ have the same referent and @pr@ is bound by
--   @pr'@ in global 'PDRS' @gp@, or
--
-- * @pr@ and @pr'@ have the same referent and both occur free
--   in subordinated contexts in @gp@.
---------------------------------------------------------------------------
cleanPRefs :: PDRS -> PDRS -> [(PRef,PRef)] -> PDRS
cleanPRefs lp@(LambdaPDRS _) _  _   = lp
cleanPRefs (AMerge p1 p2)    gp prs = AMerge (cleanPRefs p1 gp prs) (cleanPRefs p2 gp prs)
cleanPRefs (PMerge p1 p2)    gp prs = PMerge (cleanPRefs p1 gp prs) (cleanPRefs p2 gp prs)
cleanPRefs lp@(PDRS l m u c) gp prs = PDRS l m (map (convert prs) u) (map clean c)
  where -- | Converts a 'PRef' @pr@ based on a conversion list
        convert :: [(PRef,PRef)] -> PRef -> PRef
        convert [] pr                                    = pr
        convert  ((pr'@(PRef p' r'),npr):prs) pr@(PRef p r)
          | pr == pr'                                    = npr
          | r  == r' && pdrsPRefBoundByPRef pr lp pr' gp = npr
          | r  == r' && not(pdrsBoundPRef pr lp gp) 
            && (pdrsIsAccessibleContext p p' gp)         = npr
          | otherwise                                    = convert prs pr
        -- | A projected condition is /clean/ iff all its subordinated
        -- referents have been converted based on the conversion list.
        clean :: PCon -> PCon
        clean (PCon p (Rel r d))    = PCon p (Rel   r (map (cleanPDRSRef p) d))
        clean (PCon p (Neg p1))     = PCon p (Neg     (cleanPRefs p1 gp prs))
        clean (PCon p (Imp p1 p2))  = PCon p (Imp     (cleanPRefs p1 gp prs) (cleanPRefs p2 gp prs))
        clean (PCon p (Or  p1 p2))  = PCon p (Or      (cleanPRefs p1 gp prs) (cleanPRefs p2 gp prs))
        clean (PCon p (Prop r p1))  = PCon p (Prop    (cleanPDRSRef p r) (cleanPRefs p1 gp prs))
        clean (PCon p (Diamond p1)) = PCon p (Diamond (cleanPRefs p1 gp prs))
        clean (PCon p (Box p1))     = PCon p (Box     (cleanPRefs p1 gp prs))
        cleanPDRSRef :: PVar -> PDRSRef -> PDRSRef
        cleanPDRSRef p r = prefToPDRSRef (convert prs (pdrsRefToPRef r p))

---------------------------------------------------------------------------
-- | Replaces duplicate uses of projection variables by new variables.
--
-- [This function implements the following algorithm:]
--
-- (1) start with the global 'PDRS' and an empty list of seen projection
--    variables @pvs@ (in 'pdrsToCleanPDRS');
-- 
-- 2. check the label @l@ of the first atomic 'PDRS' @pdrs@ against @pvs@
--    and, if necessary, alpha-convert @pdrs@ replacing @l@ for a new 'PVar';
-- 
-- 3. add the label and all free 'PVar's from the universe and set of 'MAP's
--    of @pdrs@ to the list of seen projection variables @pvs@;
-- 
-- 4. go through all conditions of @pdrs@, while updating @pvs@ by adding
--    'PVar's that occur free;
---------------------------------------------------------------------------
cleanPVars :: (PDRS,[PVar]) -> PDRS -> (PDRS,[PVar])
cleanPVars (lp@(LambdaPDRS _),pvs) _  = (lp,pvs)
cleanPVars (AMerge p1 p2,pvs)      gp = (AMerge cp1 cp2,pvs2)
  where (cp1,pvs1) = cleanPVars (p1,pvs)  gp
        (cp2,pvs2) = cleanPVars (p2,pvs1) gp
cleanPVars (PMerge p1 p2,pvs)      gp = (PMerge cp1 cp2,pvs2)
  where (cp1,pvs1) = cleanPVars (p1,pvs)  gp
        (cp2,pvs2) = cleanPVars (p2,pvs1) gp
-- | Step 2.
-- If necessary, update label @l@ in the entire local 'PDRS';
-- otherwise, clean conditions based on updated list of seen 'PVar's.
cleanPVars (lp@(PDRS l m u c),pvs) gp
  | l `elem` pvs   = cleanPVars (pdrsAlphaConvert lp [(l,l')] [],pvs) gp 
  | otherwise      = (PDRS l m u ccs,pvs')
  where (l':[])    = newPVars [l] (pdrsPVars gp `union` pdrsPVars lp)
        -- | Step 3.
        (ccs,pvs') = clean (c,l:pvs `union` upv `union` mpv)
        upv = filter (not . flip (`pdrsBoundPVar` lp) gp) (map prefToPVar u)
        mpv = filter (not . flip (`pdrsBoundPVar` lp) gp) (concatMap (\(x,y) -> [x,y]) m)
        -- | Step 4.
        clean :: ([PCon],[PVar]) -> ([PCon],[PVar])
        clean tp@([],pvs)  = tp
        clean (pc@(PCon p (Rel _ _)):pcs,pvs) = (pc:ccs,pvs1)
          where (ccs,pvs1) = clean (pcs,addUnboundPVar p lp pvs)
        clean (PCon p (Neg p1):pcs,pvs)       = (PCon p (Neg cp1):ccs,pvs2)
          where -- | If an embedded 'PDRS' is encountered, step 2 is
                -- recursively called.
                (cp1,pvs1) = cleanPVars (p1,addUnboundPVar p lp pvs) gp
                (ccs,pvs2) = clean (pcs,pvs1)
        clean (PCon p (Imp p1 p2):pcs,pvs)    = (PCon p (Imp cp1 cp2):ccs,pvs4)
          where -- | For binary operators an extra conversion step is
                -- required since the label of the first 'PDRS' can bind
                -- 'PVar's in the second 'PDRS'.
                (cp1,pvs2) = cleanPVars (alphaConvertSubPDRS p1 gp npv [],pvs1) gp
                (cp2,pvs3) = cleanPVars (alphaConvertSubPDRS p2 gp npv [],pvs2) gp
                (ccs,pvs4) = clean (pcs,pvs3)
                pvs1 = addUnboundPVar p lp pvs
                opv  = pvs1 `intersect` [pdrsLabel p1]
                npv  = zip opv (newPVars opv (pdrsPVars gp `union` pdrsPVars lp))
        clean (PCon p (Or p1 p2):pcs,pvs)     = (PCon p (Or cp1 cp2):ccs,pvs4)
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
        -- | Given a list of seen projection variables @pvs@, 'PVar' @pv@ is
        -- added to @pvs@ /iff/ @pv@ is not bound in global 'PDRS' @gp@.
        addUnboundPVar :: PVar -> PDRS -> [PVar] -> [PVar]
        addUnboundPVar pv p pvs
          | not(pdrsBoundPVar pv p gp) = [pv] `union` pvs
          | otherwise                  = pvs

---------------------------------------------------------------------------
-- | Returns a tuple of existing 'PRef's @eps@ and unbound duplicate 'PRef's
-- @dps@ in a 'PDRS', based on a list of seen 'PRef's @prs@, where:
--
-- [@pr = ('PRef' p r)@ is duplicate in 'PDRS' @gp@ /iff/]
--
-- * There exists a @p'@, such that @pr' = ('PRef' p' r)@ is an element
--   of @prs@, and @pr@ and @pr'@ are /independent/.
---------------------------------------------------------------------------
unboundDupPRefs :: PDRS -> PDRS -> [PRef] -> ([PRef],[PRef])
unboundDupPRefs (LambdaPDRS _)    _  eps = (eps,[])
unboundDupPRefs (AMerge p1 p2)    gp eps = (eps2,dps1 ++ dps2)
  where (eps1,dps1) = unboundDupPRefs p1 gp eps
        (eps2,dps2) = unboundDupPRefs p2 gp eps1
unboundDupPRefs (PMerge p1 p2)    gp eps = (eps2,dps1 ++ dps2)
  where (eps1,dps1) = unboundDupPRefs p1 gp eps
        (eps2,dps2) = unboundDupPRefs p2 gp eps1
unboundDupPRefs lp@(PDRS _ _ u c) gp eps = (eps1,filter (`dup` eps) uu ++ dps1)
  where (eps1,dps1) = dups c (eps ++ uu)
        uu = unboundPRefs u
        -- | Returns whether 'PRef' @pr@ is /duplicate/ wrt a list of 'PRef's.
        dup :: PRef -> [PRef] -> Bool
        dup _ []                                       = False
        dup pr@(PRef _ r) (pr'@(PRef _ r'):prs)
          | r == r' && independentPRefs pr [pr'] lp gp = True
          | otherwise                                  = dup pr prs
        -- | Returns a tuple of existing 'PRef's @eps'@ and duplicate
        -- 'PRef's @dps'@, based on a list of 'PCon's and a list of existing
        -- 'PRef's @eps@. 
        dups :: [PCon] -> [PRef] -> ([PRef],[PRef])
        dups [] eps = (eps,[])
        dups (PCon p (Rel _ d):pcs)    eps = (eps2,dps1 ++ dps2)
          where (eps2,dps2) = dups pcs (eps ++ prs)
                prs  = unboundPRefs $ map (`pdrsRefToPRef` p) d
                dps1 = filter (flip (flip (`independentPRefs` dps1) lp) gp) dps
                dps  = filter (`dup` eps) prs
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
                (eps3,dps3) = (eps2 ++ unboundPRefs [pr],filter (`dup` eps) [pr])
                pr          = pdrsRefToPRef r p
        dups (PCon p (Diamond p1):pcs) eps = (eps2,dps1 ++ dps2)
          where (eps1,dps1) = unboundDupPRefs p1 gp eps
                (eps2,dps2) = dups pcs eps1
        dups (PCon p (Box p1):pcs)     eps = (eps2,dps1 ++ dps2)
          where (eps1,dps1) = unboundDupPRefs p1 gp eps
                (eps2,dps2) = dups pcs eps1
        -- | Returns whether a referent is bound by some other referent
        -- than itself.
        unboundPRefs :: [PRef] -> [PRef]
        unboundPRefs [] = []
        unboundPRefs (pr:prs)
          | not $ any (flip (pdrsPRefBoundByPRef pr lp) gp) u = pr : unboundPRefs prs
          | otherwise                                         = unboundPRefs prs
          where u = delete pr (pdrsUniverses gp)

---------------------------------------------------------------------------
-- | Returns whether a 'PRef' @pr@ is /independent/ based on a list of
-- 'PRef's @prs@, where:
--
-- [@pr = ('PRef' p r)@ is independent w.r.t. @prs@ /iff/]
--
-- (1) @pr@ is not bound by any 'PRef' in @prs@; and
--
-- 2. it is not the case that @pr@ occurs free and there is some
--    element of @prs@ that is accessible from @pr@. (NB. this only
--    holds if both @pr@ and @pr'@ occur free in accessible contexts,
--    in which case they are not independent).
---------------------------------------------------------------------------
independentPRefs :: PRef -> [PRef] -> PDRS -> PDRS -> Bool
independentPRefs _ [] _ _                                          = True
independentPRefs pr@(PRef p r) prs lp gp
  | any (flip (pdrsPRefBoundByPRef pr lp) gp) prs                  = False
  | not(pdrsBoundPRef pr lp gp) 
    && any (\(PRef p' _) -> (pdrsIsAccessibleContext p p' gp)) prs = False
  | otherwise                                                      = True

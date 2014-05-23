{- |
Module      :  Data.PDRS.Properties
Copyright   :  (c) Harm Brouwer and Noortje Venhuizen
License     :  Apache-2.0

Maintainer  :  me@hbrouwer.eu, n.j.venhuizen@rug.nl
Stability   :  provisional
Portability :  portable

PDRS properties
-}

module Data.PDRS.Properties 
(
  isProperPDRS
, isPurePDRS
, isPresupPDRS
, isSimplePDRS
, isPlainPDRS
) where

import Data.PDRS.Binding
import Data.PDRS.DataType
import Data.PDRS.LambdaCalculus
import Data.PDRS.Variables

---------------------------------------------------------------------------
-- * Exported
---------------------------------------------------------------------------

---------------------------------------------------------------------------
-- | Returns whether a 'PDRS' is /proper/, where:
--
-- [A 'PDRS' @p@ is proper /iff/]
--
--  * @p@ does not contain any free referents
---------------------------------------------------------------------------
isProperPDRS :: PDRS -> Bool
isProperPDRS p = isProperSubPDRS p p
  where isProperSubPDRS (LambdaPDRS _) _      = True
        isProperSubPDRS (AMerge p1 p2) gp     = isProperSubPDRS p1 gp && isProperSubPDRS p2 gp
        isProperSubPDRS (PMerge p1 p2) gp     = isProperSubPDRS p1 gp && isProperSubPDRS p2 gp
        isProperSubPDRS lp@(PDRS _ _ _ cs) gp = all properCon cs
          where properCon :: PCon -> Bool
                properCon (PCon p' (Rel _ d))    = all (\d' -> pdrsBoundPRef (PRef p' d') lp gp) d
                properCon (PCon _  (Neg p1))     = isProperSubPDRS p1 gp
                properCon (PCon _  (Imp p1 p2))  = isProperSubPDRS p1 gp && isProperSubPDRS p2 gp
                properCon (PCon _  (Or p1 p2))   = isProperSubPDRS p1 gp && isProperSubPDRS p2 gp
                properCon (PCon p' (Prop r p1))  = pdrsBoundPRef (PRef p' r) lp gp && isProperSubPDRS p1 gp
                properCon (PCon _  (Diamond p1)) = isProperSubPDRS p1 gp
                properCon (PCon _  (Box p1))     = isProperSubPDRS p1 gp

---------------------------------------------------------------------------
-- | Returns whether a 'PDRS' is /pure/, where:
--
-- [A 'PDRS' @p@ is pure /iff/]
--
--  * @p@ does not contain any duplicate (otiose) variables
---------------------------------------------------------------------------
isPurePDRS :: PDRS -> Bool
isPurePDRS p = p == pdrsPurify p

---------------------------------------------------------------------------
-- | Returns whether a 'PDRS' is /presuppositional/, where:
--
-- [A 'PDRS' @p@ is presuppositional /iff/]
--
--  * @p@ contains free pointers
---------------------------------------------------------------------------
isPresupPDRS :: PDRS -> Bool
isPresupPDRS (LambdaPDRS{}) = False
isPresupPDRS (AMerge p1 p2) = isPresupPDRS p1 || isPresupPDRS p2
isPresupPDRS (PMerge{})     = True
isPresupPDRS p@(PDRS{})     = any (`pdrsIsFreePVar` p) (pdrsPVars p)

---------------------------------------------------------------------------
-- | Returns whether a 'PDRS' is /simple/, where:
--
-- [A 'PDRS' @p@ is simple /iff/]
--
--  * @p@ does not contain free pointers
---------------------------------------------------------------------------
isSimplePDRS :: PDRS -> Bool
isSimplePDRS = not . isPresupPDRS

---------------------------------------------------------------------------
-- | Returns whether a 'PDRS' is /plain/, where:
--
-- [A 'PDRS' @p@ is plain /iff/]
--
--  * all projection pointers in @p@ are locally bound
---------------------------------------------------------------------------
isPlainPDRS :: PDRS -> Bool
isPlainPDRS (LambdaPDRS{}) = True
isPlainPDRS (AMerge p1 p2) = isPlainPDRS p1 && isPlainPDRS p2
isPlainPDRS (PMerge{})     = False
isPlainPDRS (PDRS l _ u c) = all (\(PRef p _) -> p==l) u && all plain c
  where plain :: PCon -> Bool
        plain (PCon p (Rel{}))      = p==l
        plain (PCon p (Neg p1))     = p==l && isPlainPDRS p1
        plain (PCon p (Imp p1 p2))  = p==l && isPlainPDRS p1 && isPlainPDRS p2
        plain (PCon p (Or p1 p2))   = p==l && isPlainPDRS p1 && isPlainPDRS p2
        plain (PCon p (Prop _ p1))  = p==l && isPlainPDRS p1
        plain (PCon p (Diamond p1)) = p==l && isPlainPDRS p1
        plain (PCon p (Box p1))     = p==l && isPlainPDRS p1

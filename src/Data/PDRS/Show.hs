-- Show.hs

{-# LANGUAGE FlexibleInstances #-}

{- |
  Show PDRS
-}
module Data.PDRS.Show
(
  showPDRS
, printPDRS
, showAMerge
, printAMerge
, showPMerge
, printPMerge
, showPDRSBetaReduct
, printPDRSBetaReduct
, showPDRSRefBetaReduct
, printPDRSRefBetaReduct
) where

import Data.DRS.Properties (isFOLDRS)
import Data.DRS.Show
import Data.DRS.Translate (drsToFOL)
import Data.DRS.Variables (drsRefToDRSVar)
import Data.PDRS.Merge
import Data.PDRS.Properties
import Data.PDRS.Structure
import Data.PDRS.Translate
import Data.PDRS.Variables

import Data.List (intercalate, union)
import Data.Tuple (swap)

-- | Derive and instance of the Show typeclass for PDRS
instance Show PDRS where
  show p
    | isFOLDRS d = "\n" ++ showPDRS p ++ "\n" ++ show (drsToFOL d) ++ "\n"
    | otherwise  = "\n" ++ showPDRS p
    where d = pdrsToDRS p

-- | Typeclass for showable, but unresolved PDRSs
class ShowablePDRS p where 
  resolve :: p -> Int -> Int -> PDRS

-- | Derive an instance of ShowablePDRS for a resolved PDRS
instance ShowablePDRS PDRS where
  resolve p _ _ = p

-- | Derive an instance of ShowablePDRS for a PDRS that requires
-- at least one PDRS referent to resolve
instance (ShowablePDRS p) => ShowablePDRS (PDRSRef -> p) where
  resolve up nr np = resolve (up rv) (nr + 1) np
    where rv = LambdaPDRSRef ("r" ++ (show nr), nr + np)

-- | Derive an instance of ShowablePDRS for a PDRS that requires
-- at least one PDRS to resolve
instance (ShowablePDRS p) => ShowablePDRS (PDRS -> p) where
  resolve up nr np = resolve (up lv) nr (np + 1)
    where lv = LambdaPDRS ("k" ++ (show np), nr + np)

-- | Derive an instance of Show for a PDRS that requires
-- at least one PDRS referent to resolve
instance (ShowablePDRS p) => Show (PDRSRef -> p) where
  show p = show (resolve p 0 0)

-- | Derive an instance of Show for a PDRS that requires
-- at least one PDRS to resolve
instance (ShowablePDRS p) => Show (PDRS -> p) where
  show p = show (resolve p 0 0)

-- | Operator constants
opAMerge = "\x002B" -- ^ Assertive merge symbol
opPMerge = "\x002A" -- ^ Projective merge symbol

-- | Modifier constant
modPointer = "\x2190" -- ^ Pointer symbol
modEquals  = "\x003D" -- ^ Equals symbol
modSubord  = "\x2264" -- ^ Subordination symbol

-- | Shows a PDRS
showPDRS :: PDRS -> String
showPDRS p = showModifier (showPDRSLambdas p) 2 (showPDRSBox p)

-- | Show a PDRS box
showPDRSBox :: PDRS -> String
showPDRSBox (LambdaPDRS (v,_)) = v ++ "\n"
showPDRSBox (AMerge p1 p2)
  | isLambdaPDRS p1 && isLambdaPDRS p2      = showConcat (showPDRSBox p1) (showModifier opAMerge 0 (showPDRSBox p2))
  | not(isLambdaPDRS p1) && isLambdaPDRS p2 = showConcat (showPDRSBox p1) (showModifier opAMerge 2 (showPadding (showPDRSBox p2)))
  | isLambdaPDRS p1 && not(isLambdaPDRS p2) = showConcat (showPadding (showPDRSBox p1)) (showModifier opAMerge 2 (showPDRSBox p2))
  | otherwise                               = showPDRSBox (p1 <<+>> p2)
showPDRSBox (PMerge p1 p2)
  | isLambdaPDRS p1 && isLambdaPDRS p2      = showConcat (showPDRSBox p1) (showModifier opPMerge 0 (showPDRSBox p2))
  | not(isLambdaPDRS p1) && isLambdaPDRS p2 = showConcat (showPDRSBox p1) (showModifier opPMerge 2 (showPadding (showPDRSBox p2)))
  | isLambdaPDRS p1 && not(isLambdaPDRS p2) = showConcat (showPadding (showPDRSBox p1)) (showModifier opPMerge 2 (showPDRSBox p2))
  | otherwise                               = showPDRSBox (p1 <<*>> p2)
showPDRSBox (PDRS pl m u c)    = showHeaderLine l pl
  ++ showContent l ul ++ showHorizontalLine l boxMiddleLeft boxMiddleRight
  ++ showContent l cl ++ showHorizontalLine l boxMiddleLeft boxMiddleRight
  ++ showContent l ml ++ showHorizontalLine l boxBottomLeft boxBottomRight
  where ul = showUniverse u
        cl = showConditions c
        ml = showMAPs m
        l  = 4 + maximum ((map length (lines ul)) `union` (map length (lines cl)) `union` (map length (lines ml)) `union` [length (show pl)])

-- | Shows a horizontal line of width @l@ that label @pl@ in its center
showHeaderLine :: Int -> PVar -> String
showHeaderLine l pl = [boxTopLeft] ++ dl ++ sl ++ dr ++ [boxTopRight] ++ "\n"
  where sl = (show pl)
        dl = take ((floor   ((fromIntegral (l - 2)) / 2) - lf)) (repeat boxHorLine)
        dr = take ((ceiling ((fromIntegral (l - 2)) / 2) - lc)) (repeat boxHorLine)
        lf = floor   ((fromIntegral (length sl)) / 2)
        lc = ceiling ((fromIntegral (length sl)) / 2)

-- | Shows the universe @u@ of a PDRS
showUniverse :: [PRef] -> String
showUniverse u = foldr (++) " " (map showPRef u)
  where showPRef :: PRef -> String
        showPRef (PRef p r) = show p ++ " " ++ modPointer ++ " " ++ (drsRefToDRSVar . pdrsRefToDRSRef) r ++ "  "

-- | Shows the projected conditions @c@ of a PDRS
showConditions :: [PCon] -> String
showConditions [] = " "
showConditions c  = foldr (++) "" (map showPCon c)
  where showPCon :: PCon -> String
        showPCon (PCon p (Rel r d)) = projection p ++ " " ++ "(" ++ intercalate "," (map (drsRefToDRSVar . pdrsRefToDRSRef) d) ++ ")\n"
        showPCon (PCon p (Neg p1))
          | isLambdaPDRS p1 = showModifier (projection p) 0 (showModifier opNeg 0 b1)
          | otherwise       = showModifier (projection p) 2 (showModifier opNeg 2 b1)
          where b1 = showPDRSBox p1
        showPCon (PCon p (Imp p1 p2))
          | isLambdaPDRS p1 && isLambdaPDRS p2      = showModifier (projection p) 0 (showConcat b1 (showModifier opImp 0 b2))
          | not(isLambdaPDRS p1) && isLambdaPDRS p2 = showModifier (projection p) 2 (showConcat b1 (showModifier opImp 2 (showPadding b2)))
          | isLambdaPDRS p1 && not(isLambdaPDRS p2) = showModifier (projection p) 2 (showConcat (showPadding b1) (showModifier opImp 2 b2))
          | otherwise                               = showModifier (projection p) 2 (showConcat b1 (showModifier opImp 2 b2))
          where b1 = showPDRSBox p1
                b2 = showPDRSBox p2
        showPCon (PCon p (Or p1 p2))
          | isLambdaPDRS p1 && isLambdaPDRS p2      = showModifier (projection p) 0 (showConcat b1 (showModifier opOr 0 b2))
          | not(isLambdaPDRS p1) && isLambdaPDRS p2 = showModifier (projection p) 2 (showConcat b1 (showModifier opOr 2 (showPadding b2)))
          | isLambdaPDRS p1 && not(isLambdaPDRS p2) = showModifier (projection p) 2 (showConcat (showPadding b1) (showModifier opOr 2 b2))
          | otherwise                               = showModifier (projection p) 2 (showConcat b1 (showModifier opOr 2 b2))
          where b1 = showPDRSBox p1
                b2 = showPDRSBox p2
        showPCon (PCon p (Prop r p1))
          | isLambdaPDRS p1 = showModifier (projection p) 0 (showModifier (((drsRefToDRSVar . pdrsRefToDRSRef) r) ++ ":") 0 b1)
          | otherwise       = showModifier (projection p) 2 (showModifier (((drsRefToDRSVar . pdrsRefToDRSRef) r) ++ ":") 2 b1)
          where b1 = showPDRSBox p1
        showPCon (PCon p (Diamond p1))
          | isLambdaPDRS p1 = showModifier (projection p) 0 (showModifier opDiamond 0 b1)
          | otherwise       = showModifier (projection p) 2 (showModifier opDiamond 2 b1)
          where b1 = showPDRSBox p1
        showPCon (PCon p (Box p1))
          | isLambdaPDRS p1 = showModifier (projection p) 0 (showModifier opBox 0 b1)
          | otherwise       = showModifier (projection p) 2 (showModifier opBox 2 b1)
          where b1 = showPDRSBox p1
        projection :: PVar -> String
        projection p = show p ++ " " ++ modPointer

-- | Shows the minimally accessible PDRSs @m@ of a PDRS
showMAPs :: [(PVar,PVar)] -> String
showMAPs m = showUnique m []
  where showUnique :: [(PVar,PVar)] -> [(PVar,PVar)] -> String
        showUnique [] _ = " "
        showUnique (m@(pv1,pv2):ms) sms
          | swap m `elem` ms  = showUnique ms (m:sms)
          | swap m `elem` sms = show pv1 ++ " " ++ modEquals ++ " " ++ show pv2 ++ "  " ++ showUnique ms (m:sms)
          | otherwise         = show pv1 ++ " " ++ modSubord ++ " " ++ show pv2 ++ "  " ++ showUnique ms (m:sms)

-- | Shows lambda abstractions over PDRS @p@
showPDRSLambdas :: PDRS -> String
showPDRSLambdas p = show (pdrsLambdas p)
  where show :: [DRSVar] -> String
        show []     = []
        show (l:ls) = opLambda ++ l ++ "." ++ show ls

-- | Prints a PDRS
printPDRS :: PDRS -> IO ()
printPDRS p = putStrLn $ "\n" ++ showPDRS p

-- | Shows an assertive merge between PDRS @p1@ and PDRS @p@
showAMerge :: PDRS -> PDRS -> String
showAMerge p1 p2 = showConcat b1 (showModifier opAMerge 2 (showConcat b2 (showModifier "=" 2 mb)))
  where b1 = showPDRS p1
        b2 = showPDRS p2
        mb = showPDRS (p1 <<+>> p2)

-- | Prints an assertive merge between PDRS @p1@ and PDRS @p@
printAMerge :: PDRS -> PDRS -> IO ()
printAMerge p1 p2 = putStrLn $ "\n" ++ showAMerge p1 p2

-- | Shows a projective merge between PDRS @p1@ and PDRS @p@
showPMerge :: PDRS -> PDRS -> String
showPMerge p1 p2 = showConcat b1 (showModifier opPMerge 2 (showConcat b2 (showModifier "=" 2 mb)))
  where b1 = showPDRS p1
        b2 = showPDRS p2
        mb = showPDRS (p1 <<*>> p2)

-- | Print a projective merge between PDRS @p1@ and PDRS @p@
printPMerge :: PDRS -> PDRS -> IO ()
printPMerge p1 p2 = putStrLn $ "\n" ++ showPMerge p1 p2

-- | Shows the beta reduction of an unresolved PDRS @p1@ with a PDRS @p2@
showPDRSBetaReduct :: (ShowablePDRS p) => (PDRS -> p) -> PDRS -> String
showPDRSBetaReduct p1 p2 = showConcat (showConcat (showModifier "(" 2 b1) (showModifier ")" 2 b2)) (showModifier "=" 2 br)
  where b1 = showPDRS (resolve p1 0 0)
        b2 = showPDRS p2
        br = showPDRS (resolve (p1 p2) 0 0)

-- | Prints the beta reduction of an unresolved PDRS @p1@ with a PDRS @p2@
printPDRSBetaReduct :: (ShowablePDRS p) => (PDRS -> p) -> PDRS -> IO ()
printPDRSBetaReduct p1 p2 = putStrLn $ "\n" ++ showPDRSBetaReduct p1 p2

-- | Shows the beta reduction of an unresolved PDRS @p@ with a PDRS referent @r@
showPDRSRefBetaReduct :: (ShowablePDRS p) => (PDRSRef -> p) -> PDRSRef -> String
showPDRSRefBetaReduct p r@(PDRSRef v) = showConcat (showConcat (showModifier "(" 2 bx) (showModifier ")" 2 rv)) (showModifier "=" 2 br)
  where bx = showPDRS (resolve p 0 0)
        rv = showPadding (v ++ "\n")
        br = showPDRS (resolve (p r) 0 0)

-- | Shows the beta reduction of an unresolved PDRS @p@ with a PDRS referent @r@
printPDRSRefBetaReduct :: (ShowablePDRS p) => (PDRSRef -> p) -> PDRSRef -> IO ()
printPDRSRefBetaReduct p r = putStrLn $ "\n" ++ showPDRSRefBetaReduct p r

{-# LANGUAGE FlexibleInstances #-}
{- |
Module      :  Data.PDRS.Show
Copyright   :  (c) Harm Brouwer and Noortje Venhuizen
License     :  Apache-2.0

Maintainer  :  me@hbrouwer.eu
Stability   :  provisional
Portability :  portable

PDRS pretty printing
-}

module Data.PDRS.Show
(
-- * Pretty printing
  PDRSNotation (..)
, showPDRS
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
import Data.DRS.Show hiding (DRSNotation (..))
import Data.DRS.Structure (DRS)
import Data.DRS.Translate (drsToFOL)
import Data.DRS.Variables (drsRefToDRSVar)

import Data.PDRS.Merge
import Data.PDRS.Properties
import Data.PDRS.Structure
import Data.PDRS.Translate
import Data.PDRS.Variables

import Data.List (intercalate, union)
import Data.Tuple (swap)

-- PDRS Notation
data PDRSNotation p =
  Set p      -- ^ Set notation
  | Linear p -- ^ Linear notation
  | Boxes p  -- ^ Box notation

-- | Derive and instance of the Show typeclass for PDRS
instance Show PDRS where
  show p = '\n' : showPDRS (Boxes p)

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
    where rv = LambdaPDRSRef ('r' : show nr, nr + np)

-- | Derive an instance of ShowablePDRS for a PDRS that requires
-- at least one PDRS to resolve
instance (ShowablePDRS p) => ShowablePDRS (PDRS -> p) where
  resolve up nr np = resolve (up lv) nr (np + 1)
    where lv = LambdaPDRS ('k' : show np, nr + np)

-- | Derive an instance of Show for a PDRS that requires
-- at least one PDRS referent to resolve
instance (ShowablePDRS p) => Show (PDRSRef -> p) where
  show p = show (resolve p 0 0)

-- | Derive an instance of Show for a PDRS that requires
-- at least one PDRS to resolve
instance (ShowablePDRS p) => Show (PDRS -> p) where
  show p = show (resolve p 0 0)

-- | Derive an instance of Show for PDRS Notation
instance (ShowablePDRS p) => Show (PDRSNotation p) where
  show (Boxes p)  = '\n' : showPDRS (Boxes  (resolve p 0 0))
  show (Linear p) = '\n' : showPDRS (Linear (resolve p 0 0))
  show (Set p)    = '\n' : showPDRS (Set    (resolve p 0 0))

-- | Assertive merge symbol
opAMerge = "\x002B"
-- | Projective merge symbol
opPMerge = "\x002A"

-- | Pointer symbol
modPointer = "\x2190"
-- | Equals symbol
modEquals  = "\x003D"
-- | Subordination symbol
modSubord  = "\x2264"

-- | Shows a PDRS
showPDRS :: PDRSNotation PDRS -> String
showPDRS n =
  case n of
    (Boxes p)  -> showModifier (showPDRSLambdas rp) 2 (showPDRSBox rp)
      where rp = pdrsResolveMerges p
    (Linear p) -> showPDRSLambdas rp ++ showPDRSLinear rp ++ "\n" 
      where rp = pdrsResolveMerges p
    (Set p)    -> showPDRSLambdas rp ++ showPDRSSet rp  ++ "\n" 
      where rp = pdrsResolveMerges p

-- | Show a PDRS in Box notation
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
        l  = 4 + maximum (map length (lines ul) `union` map length (lines cl) `union` map length (lines ml) `union` [length (show pl)])

-- | Show a PDRS in Linear notation
showPDRSLinear :: PDRS -> String
showPDRSLinear (LambdaPDRS (v,_)) = v
showPDRSLinear (AMerge p1 p2)
  | not(isLambdaPDRS p1) && not(isLambdaPDRS p2) = showPDRSLinear (p1 <<+>> p2)
  | otherwise                                    = showPDRSLinear p1 ++ " " ++ opAMerge ++ " " ++ showPDRSLinear p2
showPDRSLinear (PMerge p1 p2)
  | not(isLambdaPDRS p1) && not(isLambdaPDRS p2) = showPDRSLinear (p1 <<*>> p2)
  | otherwise                                    = showPDRSLinear p1 ++ " " ++ opPMerge ++ " " ++ showPDRSLinear p2
showPDRSLinear (PDRS l m u c)     = show l ++ ":[" ++ showUniverseTuples u ++ "|" ++ intercalate "," (map showCon c) ++ "|" ++ showMAPsTuples m ++ "]"
  where showCon :: PCon -> String
        showCon (PCon p (Rel r d))    = "(" ++ show p ++ "," ++ r ++ "(" ++ intercalate "," (map (drsRefToDRSVar . pdrsRefToDRSRef) d) ++ "))"
        showCon (PCon p (Neg p1))     = "(" ++ show p ++ "," ++ opNeg ++ showPDRSLinear p1 ++ ")"
        showCon (PCon p (Imp p1 p2))  = "(" ++ show p ++ "," ++ showPDRSLinear p1 ++ " " ++ opImp ++ " " ++ showPDRSLinear p2 ++ ")"
        showCon (PCon p (Or p1 p2))   = "(" ++ show p ++ "," ++ showPDRSLinear p1 ++ " " ++ opOr  ++ " " ++ showPDRSLinear p2 ++ ")"
        showCon (PCon p (Prop r p1))  = "(" ++ show p ++ "," ++ (drsRefToDRSVar . pdrsRefToDRSRef) r ++ ": " ++ showPDRSLinear p1 ++ ")"
        showCon (PCon p (Diamond p1)) = "(" ++ show p ++ "," ++ opDiamond ++ showPDRSLinear p1 ++ ")"
        showCon (PCon p (Box p1))     = "(" ++ show p ++ "," ++ opBox ++ showPDRSLinear p1 ++ ")"

-- | Show a PDRS in Set notation
showPDRSSet :: PDRS -> String
showPDRSSet (LambdaPDRS (v,_)) = v
showPDRSSet (AMerge p1 p2)
  | not(isLambdaPDRS p1) && not(isLambdaPDRS p2) = showPDRSSet (p1 <<+>> p2)
  | otherwise                                    = showPDRSSet p1 ++ " " ++ opAMerge ++ " " ++ showPDRSSet p2
showPDRSSet (PMerge p1 p2)
  | not(isLambdaPDRS p1) && not(isLambdaPDRS p2) = showPDRSSet (p1 <<*>> p2)
  | otherwise                                    = showPDRSSet p1 ++ " " ++ opPMerge ++ " " ++ showPDRSSet p2
showPDRSSet (PDRS l m u c)     = "<" ++ show l ++ ",{" ++ showMAPsTuples m ++ "},{" ++ showUniverseTuples u ++ "},{" ++ intercalate "," (map showCon c) ++ "}>"
  where showCon :: PCon -> String
        showCon (PCon p (Rel r d))    = "(" ++ show p ++ "," ++ r ++ "(" ++ intercalate "," (map (drsRefToDRSVar . pdrsRefToDRSRef) d) ++ "))"
        showCon (PCon p (Neg p1))     = "(" ++ show p ++ "," ++ opNeg ++ showPDRSSet p1 ++ ")"
        showCon (PCon p (Imp p1 p2))  = "(" ++ show p ++ "," ++ showPDRSSet p1 ++ " " ++ opImp ++ " " ++ showPDRSSet p2 ++ ")"
        showCon (PCon p (Or p1 p2))   = "(" ++ show p ++ "," ++ showPDRSSet p1 ++ " " ++ opOr  ++ " " ++ showPDRSSet p2 ++ ")"
        showCon (PCon p (Prop r p1))  = "(" ++ show p ++ "," ++ (drsRefToDRSVar . pdrsRefToDRSRef) r ++ ": " ++ showPDRSSet p1 ++ ")"
        showCon (PCon p (Diamond p1)) = "(" ++ show p ++ "," ++ opDiamond ++ showPDRSSet p1 ++ ")"
        showCon (PCon p (Box p1))     = "(" ++ show p ++ "," ++ opBox ++ showPDRSSet p1 ++ ")"

-- | Shows a horizontal line of width @l@ that label @pl@ in its center
showHeaderLine :: Int -> PVar -> String
showHeaderLine l pl = [boxTopLeft] ++ dl ++ sl ++ dr ++ [boxTopRight] ++ "\n"
  where sl = show pl
        dl = replicate (floor   (fromIntegral (l - 2) / 2) - lf) boxHorLine
        dr = replicate (ceiling (fromIntegral (l - 2) / 2) - lc) boxHorLine
        lf = floor   (fromIntegral (length sl) / 2)
        lc = ceiling (fromIntegral (length sl) / 2)

-- | Shows the universe @u@ of a PDRS
showUniverse :: [PRef] -> String
showUniverse u = intercalate "  " (map showPRef u)
  where showPRef :: PRef -> String
        showPRef (PRef p r) = show p ++ " " ++ modPointer ++ " " ++ (drsRefToDRSVar . pdrsRefToDRSRef) r

-- | Shows the universe @u@ of a PDRS as tuples
showUniverseTuples :: [PRef] -> String
showUniverseTuples u = intercalate "," (map showPRef u)
  where showPRef :: PRef -> String
        showPRef (PRef p r) = "(" ++ show p ++ "," ++ (drsRefToDRSVar . pdrsRefToDRSRef) r ++ ")"

-- | Shows the projected conditions @c@ of a PDRS
showConditions :: [PCon] -> String
showConditions [] = " "
showConditions c  = foldr ((++) . showPCon) "" c
  where showPCon :: PCon -> String
        showPCon (PCon p (Rel r d)) = projection p ++ " " ++ r ++ "(" ++ intercalate "," (map (drsRefToDRSVar . pdrsRefToDRSRef) d) ++ ")\n"
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
          | isLambdaPDRS p1 = showModifier (projection p) 0 (showModifier ((drsRefToDRSVar . pdrsRefToDRSRef) r ++ ":") 0 b1)
          | otherwise       = showModifier (projection p) 2 (showModifier ((drsRefToDRSVar . pdrsRefToDRSRef) r ++ ":") 2 b1)
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

-- | Shows the minimally accessible PDRSs @m@ of a PDRS as tuples
showMAPsTuples :: [(PVar,PVar)] -> String
showMAPsTuples m = intercalate "," (map show (unique m []))
  where unique :: [(PVar,PVar)] -> [(PVar,PVar)] -> [(PVar,PVar)]
        unique [] _ = []
        unique (m@(pv1,pv2):ms) sms
          | swap m `elem` ms  = unique ms (m:sms)
          | swap m `elem` sms = m : unique ms (m:sms)
          | otherwise         = m : unique ms (m:sms)

-- | Shows lambda abstractions over PDRS @p@
showPDRSLambdas :: PDRS -> String
showPDRSLambdas p = show (pdrsLambdas p)
  where show :: [DRSVar] -> String
        show []     = []
        show (l:ls) = opLambda ++ l ++ "." ++ show ls

-- | Prints a PDRS
printPDRS :: PDRS -> IO ()
printPDRS p = putStrLn $ '\n' : showPDRS (Boxes p)

-- | Shows an assertive merge between PDRS @p1@ and PDRS @p@
showAMerge :: PDRS -> PDRS -> String
showAMerge p1 p2 = showConcat b1 (showModifier opAMerge 2 (showConcat b2 (showModifier "=" 2 mb)))
  where b1 = showPDRS (Boxes p1)
        b2 = showPDRS (Boxes p2)
        mb = showPDRS (Boxes (p1 <<+>> p2))

-- | Prints an assertive merge between PDRS @p1@ and PDRS @p@
printAMerge :: PDRS -> PDRS -> IO ()
printAMerge p1 p2 = putStrLn $ '\n' : showAMerge p1 p2

-- | Shows a projective merge between PDRS @p1@ and PDRS @p@
showPMerge :: PDRS -> PDRS -> String
showPMerge p1 p2 = showConcat b1 (showModifier opPMerge 2 (showConcat b2 (showModifier "=" 2 mb)))
  where b1 = showPDRS (Boxes p1)
        b2 = showPDRS (Boxes p2)
        mb = showPDRS (Boxes (p1 <<*>> p2))

-- | Print a projective merge between PDRS @p1@ and PDRS @p@
printPMerge :: PDRS -> PDRS -> IO ()
printPMerge p1 p2 = putStrLn $ '\n' : showPMerge p1 p2

-- | Shows the beta reduction of an unresolved PDRS @p1@ with a PDRS @p2@
showPDRSBetaReduct :: (ShowablePDRS p) => (PDRS -> p) -> PDRS -> String
showPDRSBetaReduct p1 p2 = showConcat (showConcat (showModifier "(" 2 b1) (showModifier ")" 2 b2)) (showModifier "=" 2 br)
  where b1 = showPDRS (Boxes (resolve p1 0 0))
        b2 = showPDRS (Boxes p2)
        br = showPDRS (Boxes (resolve (p1 p2) 0 0))

-- | Prints the beta reduction of an unresolved PDRS @p1@ with a PDRS @p2@
printPDRSBetaReduct :: (ShowablePDRS p) => (PDRS -> p) -> PDRS -> IO ()
printPDRSBetaReduct p1 p2 = putStrLn $ '\n' : showPDRSBetaReduct p1 p2

-- | Shows the beta reduction of an unresolved PDRS @p@ with a PDRS referent @r@
showPDRSRefBetaReduct :: (ShowablePDRS p) => (PDRSRef -> p) -> PDRSRef -> String
showPDRSRefBetaReduct p r@(PDRSRef v) = showConcat (showConcat (showModifier "(" 2 bx) (showModifier ")" 2 rv)) (showModifier "=" 2 br)
  where bx = showPDRS (Boxes (resolve p 0 0))
        rv = showPadding (v ++ "\n")
        br = showPDRS (Boxes (resolve (p r) 0 0))

-- | Shows the beta reduction of an unresolved PDRS @p@ with a PDRS referent @r@
printPDRSRefBetaReduct :: (ShowablePDRS p) => (PDRSRef -> p) -> PDRSRef -> IO ()
printPDRSRefBetaReduct p r = putStrLn $ '\n' : showPDRSRefBetaReduct p r

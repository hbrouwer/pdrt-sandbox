{-# LANGUAGE FlexibleInstances #-}
{-# OPTIONS_GHC -fno-warn-orphans #-}
{- |
Module      :  Data.DRS.Show
Copyright   :  (c) Harm Brouwer and Noortje Venhuizen
License     :  Apache-2.0

Maintainer  :  me@hbrouwer.eu, n.j.venhuizen@rug.nl
Stability   :  provisional
Portability :  portable

DRS pretty printing
-}

module Data.DRS.Show
(
-- * Show DRS (pretty printing)
  DRSNotation (..)
, showDRS
, printDRS
, showMerge
, printMerge
, showDRSBetaReduct
, printDRSBetaReduct
, showDRSRefBetaReduct
, printDRSRefBetaReduct
-- ** DRS Operator symbols
, opNeg
, opImp
, opOr
, opDiamond
, opBox
, opLambda
-- ** DRS Box Construction
, boxTopLeft
, boxTopRight
, boxBottomLeft
, boxBottomRight
, boxMiddleLeft
, boxMiddleRight
, boxHorLine
, boxVerLine
, showConcat
, showContent
, showHorizontalLine
, showModifier
, showPadding
) where

import Data.DRS.DataType
import Data.DRS.Merge
import Data.DRS.Structure
import Data.DRS.Variables

import Data.List (intercalate, union)

---------------------------------------------------------------------------
-- * Exported
---------------------------------------------------------------------------

---------------------------------------------------------------------------
-- ** Show DRS
---------------------------------------------------------------------------

---------------------------------------------------------------------------
-- | Derive an instance of the 'Show' typeclass for 'DRS'.
---------------------------------------------------------------------------
instance Show DRS where
  show d = '\n' : showDRS (Boxes d)

---------------------------------------------------------------------------
-- | Typeclass for 'showableDRS's, that are unresolved.
---------------------------------------------------------------------------
class ShowableDRS d where 
  resolve :: d -> Int -> Int -> DRS

-- | Derive appropriate instances of 'ShowableDRS'.
instance ShowableDRS DRS where
  resolve d _ _ = d
instance (ShowableDRS d) => ShowableDRS (DRSRef -> d) where
  resolve ud nr nd = resolve (ud rv) (nr + 1) nd
    where rv = LambdaDRSRef (('r' : show nr,[]), nr + nd)
instance (ShowableDRS d) => ShowableDRS (DRS -> d) where
  resolve ud nr nd = resolve (ud lv) nr (nd + 1)
    where lv = LambdaDRS (('k' : show nd,[]), nr + nd)
instance (ShowableDRS d) => ShowableDRS ((DRSRef -> DRS) -> d) where
  resolve ud nr nd = resolve (ud lv) nr (nd + 1)
    where lv x = LambdaDRS (('k' : show nd,[drsRefToDRSVar x]), nr + nd)
instance (ShowableDRS d) => ShowableDRS (DRSRel -> d) where
  resolve ud nr nd = resolve (ud lv) nr (nd + 1)
    where lv = LambdaDRSRel (('P' : show nd,[]), nr + nd)

-- | Derive appropriate instances of 'Show' for 'ShowableDRS's.
instance (ShowableDRS d) => Show (DRSRef -> d) where
  show d = show (resolve d 0 0)
instance (ShowableDRS d) => Show (DRS -> d) where
  show d = show (resolve d 0 0)
instance (ShowableDRS d) => Show ((DRSRef -> DRS) -> d) where
  show d = show (resolve d 0 0)
instance (ShowableDRS d) => Show (DRSRel -> d) where
  show d = show (resolve d 0 0)

---------------------------------------------------------------------------
-- | 'DRS' notations.
---------------------------------------------------------------------------
data DRSNotation d =
  Set d      -- ^ Set notation
  | Linear d -- ^ Linear notation
  | Boxes d  -- ^ Box notation
  | Debug d  -- ^ Debug notation

-- | Derive an instance of Show for 'DRSNotation'.
instance (ShowableDRS d) => Show (DRSNotation d) where
  show (Boxes d)  = '\n' : showDRS (Boxes  (resolve d 0 0))
  show (Linear d) = '\n' : showDRS (Linear (resolve d 0 0))
  show (Set d)    = '\n' : showDRS (Set    (resolve d 0 0))
  show (Debug d)  = '\n' : showDRS (Debug  (resolve d 0 0))

---------------------------------------------------------------------------
-- | Shows a 'DRS'.
---------------------------------------------------------------------------
showDRS :: DRSNotation DRS -> String
showDRS n = 
  case n of
    (Boxes d)  -> showModifier (showDRSLambdas d) 2 (showDRSBox d)
    (Linear d) -> showDRSLambdas d ++ showDRSLinear d ++ "\n"
    (Set d)    -> showDRSLambdas d ++ showDRSSet d    ++ "\n"
    (Debug d)  -> showDRSDebug d   ++ "\n"

---------------------------------------------------------------------------
-- | Prints a 'DRS'.
---------------------------------------------------------------------------
printDRS :: DRS -> IO ()
printDRS d = putStrLn $ '\n' : showDRS (Boxes d)

---------------------------------------------------------------------------
-- ** Show Merge
---------------------------------------------------------------------------

---------------------------------------------------------------------------
-- | Shows a merge between two 'DRS's.
---------------------------------------------------------------------------
showMerge :: DRS -> DRS -> String
showMerge d1 d2 = showConcat (showConcat b1 (showModifier "+" 2 b2)) (showModifier "=" 2 mr)
  where b1 = showDRS (Boxes d1)
        b2 = showDRS (Boxes d2)
        mr = showDRS (Boxes (d1 <<+>> d2))

---------------------------------------------------------------------------
-- | Prints a merge between two 'DRS's.
---------------------------------------------------------------------------
printMerge :: DRS -> DRS -> IO ()
printMerge d1 d2 = putStrLn $ '\n' : showMerge d1 d2

---------------------------------------------------------------------------
-- ** Show Beta Reduction
---------------------------------------------------------------------------

---------------------------------------------------------------------------
-- | Shows the beta reduction of an 'unresolved DRS' @d1@ with a 'DRS' 
-- @d2@.
---------------------------------------------------------------------------
showDRSBetaReduct :: (ShowableDRS d) => (DRS -> d) -> DRS -> String
showDRSBetaReduct d1 d2 
  = showConcat (showConcat (showModifier "(" 2 b1) (showModifier ")" 2 b2)) (showModifier "=" 2 br)
  where b1 = showDRS (Boxes (resolve d1 0 0))
        b2 = showDRS (Boxes d2)
        br = showDRS (Boxes (resolve (d1 d2) 0 0))

---------------------------------------------------------------------------
-- | Prints the beta reduction of an 'unresolved DRS' @d1@ with a 'DRS'
-- @d2@.
---------------------------------------------------------------------------
printDRSBetaReduct :: (ShowableDRS d) => (DRS -> d) -> DRS -> IO ()
printDRSBetaReduct d1 d2 = putStrLn $ '\n' : showDRSBetaReduct d1 d2

---------------------------------------------------------------------------
-- | Shows the beta reduction of an 'unresolved DRS' @d@ with a 'DRSRef'
-- @r@.
---------------------------------------------------------------------------
showDRSRefBetaReduct :: (ShowableDRS d) => (DRSRef -> d) -> DRSRef -> String
showDRSRefBetaReduct _ (LambdaDRSRef _) = error "impossible beta reduction"
showDRSRefBetaReduct d r@(DRSRef v)     = showConcat (showConcat (showModifier "(" 2 bx) (showModifier ")" 2 rv)) (showModifier "=" 2 br)
  where bx = showDRS (Boxes (resolve d 0 0))
        rv = showPadding (v ++ "\n")
        br = showDRS (Boxes (resolve (d r) 0 0))

---------------------------------------------------------------------------
-- | Prints the beta reduction of an 'unresolved DRS' @d@ with a 'DRSRef'
-- @r@.
---------------------------------------------------------------------------
printDRSRefBetaReduct :: (ShowableDRS d) => (DRSRef -> d) -> DRSRef -> IO ()
printDRSRefBetaReduct d r = putStrLn $ '\n' : showDRSRefBetaReduct d r

---------------------------------------------------------------------------
-- ** Operators
---------------------------------------------------------------------------

-- | Negation symbol
opNeg :: String
opNeg = "\x00AC"

-- | Implication symbol
opImp :: String
opImp = "\x21D2"

-- | Disjunction symbol
opOr :: String
opOr = "\x2228"

-- | Diamond symbol
opDiamond :: String
opDiamond = "\x25C7"

-- | Box symbol
opBox :: String
opBox = "\x25FB"

-- | Lambda symbol
opLambda :: String
opLambda = "\x03BB"

-- | Merge symbol
opMerge :: String
opMerge = "\x002B"

---------------------------------------------------------------------------
-- ** Box Construction
---------------------------------------------------------------------------

-- | Top left corner symbol
boxTopLeft :: Char
boxTopLeft = '\x250C' 
-- | Top right corner symbol
boxTopRight :: Char
boxTopRight = '\x2510'
-- | Bottom left corner symbol
boxBottomLeft :: Char
boxBottomLeft = '\x2514'
-- | Bottom right corner symbol
boxBottomRight :: Char
boxBottomRight = '\x2518'
-- | Middle left corner symbol
boxMiddleLeft :: Char
boxMiddleLeft = '\x251C'
-- | Middle right corner symbol
boxMiddleRight :: Char
boxMiddleRight = '\x2524'
-- | Horizontal line symbol
boxHorLine :: Char
boxHorLine = '-'
-- | Vertical line symbol
boxVerLine :: Char
boxVerLine = '|'

---------------------------------------------------------------------------
-- | Shows the line by line concatenation of two 'String's.
---------------------------------------------------------------------------
showConcat :: String -> String -> String
showConcat s1 s2 = unlines (conc ls1 ls2)
  where conc :: [String] -> [String] -> [String]
        conc [] []         = []
        conc (a:as) []     = (a ++ " " ++ showWhitespace (length (head ls2))) : conc as []
        conc [] (b:bs)     = (showWhitespace (length (head ls1)) ++ " " ++ b) : conc [] bs
        conc (a:as) (b:bs) = (a ++ " " ++ b) : conc as bs
        ls1 = lines s1
        ls2 = lines s2

---------------------------------------------------------------------------
-- | Shows the content of a 'DRS' box surrounded by vertical bars.
---------------------------------------------------------------------------
showContent :: Int -> String -> String
showContent l s = unlines (map show' (lines s))
  where show' :: String -> String
        show' s' = [boxVerLine] ++ " " ++ s' ++ showWhitespace (l - 4 - length s') ++ " " ++ [boxVerLine]

---------------------------------------------------------------------------
-- | Shows a horizontal line of length @l@ with left corner symbol @lc@ and
-- right corner symbol @rc@.
---------------------------------------------------------------------------
showHorizontalLine :: Int -> Char -> Char -> String
showHorizontalLine l lc rc = [lc] ++ replicate (l - 2) boxHorLine ++ [rc] ++ "\n"

---------------------------------------------------------------------------
-- | Shows a modifier @m@ at line number @p@ in front of 'String' @s@.
---------------------------------------------------------------------------
showModifier :: String -> Int -> String -> String
showModifier [] _ s = s
showModifier m p s  = unlines (modifier 0 (lines s))
  where modifier :: Int -> [String] -> [String]
        modifier _ [] = []
        modifier n (l:ls)
          | n == p    = (m ++ " " ++ l) : modifier (n + 1) ls
          | otherwise = (showWhitespace (length m + 1) ++ l) : modifier (n + 1) ls

---------------------------------------------------------------------------
-- | Adds two lines of whitespace to the beginning of 'String' @s@.
---------------------------------------------------------------------------
showPadding :: String -> String
showPadding s = showWhitespace l ++ "\n" ++ showWhitespace l ++ "\n" ++ s
  where l = length s - 1

---------------------------------------------------------------------------
-- * Private
---------------------------------------------------------------------------

---------------------------------------------------------------------------
-- **  Notations for showing DRSs
---------------------------------------------------------------------------

---------------------------------------------------------------------------
-- | Shows a 'DRS' in 'Boxes' notation.
---------------------------------------------------------------------------
showDRSBox :: DRS -> String
showDRSBox (LambdaDRS ((v,d),_)) 
  | not (null d) = v ++ "(" ++ intercalate "," d ++ ")" ++ "\n"
  | otherwise    = v ++ "\n"
showDRSBox (Merge d1 d2)
  | isLambdaDRS d1 && isLambdaDRS d2      = showModifier "(" 0 (showConcat (showConcat (showDRSBox d1) (showModifier opMerge 0 (showDRSBox d2))) ")")
  | not(isLambdaDRS d1) && isLambdaDRS d2 = showBrackets (showConcat (showDRSBox d1) (showModifier opMerge 2 (showPadding (showDRSBox d2))))
  | isLambdaDRS d1 && not(isLambdaDRS d2) = showBrackets (showConcat (showPadding (showDRSBox d1)) (showModifier opMerge 2 (showDRSBox d2)))
  | otherwise                             = showBrackets (showConcat (showDRSBox d1) (showModifier opMerge 2 (showDRSBox d2)))
  where showBrackets :: String -> String
        showBrackets s = showModifier "(" 2 (showConcat s (showPadding ")\n"))
showDRSBox (DRS u c)   = showHorizontalLine l boxTopLeft boxTopRight
  ++ showContent l ul ++ showHorizontalLine l boxMiddleLeft boxMiddleRight
  ++ showContent l cl ++ showHorizontalLine l boxBottomLeft boxBottomRight
  where ul
          | not(null u) = showUniverse u "  "
          | otherwise   = " "
        cl = showConditions c
        l  = 4 + maximum (map length (lines ul) `union` map length (lines cl))

---------------------------------------------------------------------------
-- | Shows a DRS in 'Linear' notation.
---------------------------------------------------------------------------
showDRSLinear :: DRS -> String
showDRSLinear (LambdaDRS ((v,d),_)) 
  | not (null d) = v ++ "(" ++ intercalate "," d ++ ")"
  | otherwise    = v
showDRSLinear (Merge d1 d2)
  | not(isLambdaDRS d1) && not(isLambdaDRS d2) = showDRSLinear (d1 <<+>> d2)
  | otherwise                                  = showDRSLinear d1 ++ " " ++ opMerge ++ " " ++ showDRSLinear d2
showDRSLinear (DRS u c)         = "[" ++ showUniverse u "," ++ ": " ++  intercalate "," (map showCon c) ++ "]"
  where showCon :: DRSCon -> String
        showCon (Rel r d)    = drsRelToString r ++ "(" ++ intercalate "," (map drsRefToDRSVar d) ++ ")"
        showCon (Neg d1)     = opNeg ++ showDRSLinear d1
        showCon (Imp d1 d2)  = showDRSLinear d1 ++ " " ++ opImp ++ " " ++ showDRSLinear d2
        showCon (Or d1 d2)   = showDRSLinear d1 ++ " " ++ opOr  ++ " " ++ showDRSLinear d2
        showCon (Prop r d1)  = drsRefToDRSVar r ++ ": " ++ showDRSLinear d1
        showCon (Diamond d1) = opNeg ++ showDRSLinear d1
        showCon (Box d1)     = opNeg ++ showDRSLinear d1

---------------------------------------------------------------------------
-- | Shows a 'DRS' in 'Set' notation.
---------------------------------------------------------------------------
showDRSSet :: DRS -> String
showDRSSet (LambdaDRS ((v,d),_)) 
  | not (null d) = v ++ "(" ++ intercalate "," d ++ ")"
  | otherwise    = v
showDRSSet (Merge d1 d2)
  | not(isLambdaDRS d1) && not(isLambdaDRS d2) = showDRSSet (d1 <<+>> d2)
  | otherwise                                  = showDRSSet d1 ++ " " ++ opMerge ++ " " ++ showDRSSet d2
showDRSSet (DRS u c)         = "<{" ++ showUniverse u "," ++ "},{" ++ intercalate "," (map showCon c) ++ "}>"
  where showCon :: DRSCon -> String
        showCon (Rel r d)    = drsRelToString r ++ "(" ++ intercalate "," (map drsRefToDRSVar d) ++ ")"
        showCon (Neg d1)     = opNeg ++ showDRSSet d1
        showCon (Imp d1 d2)  = showDRSSet d1 ++ " " ++ opImp ++ " " ++ showDRSSet d2
        showCon (Or d1 d2)   = showDRSSet d1 ++ " " ++ opOr  ++ " " ++ showDRSSet d2
        showCon (Prop r d1)  = drsRefToDRSVar r ++ ": " ++ showDRSSet d1
        showCon (Diamond d1) = opNeg ++ showDRSSet d1
        showCon (Box d1)     = opNeg ++ showDRSSet d1

---------------------------------------------------------------------------
-- | Show a 'DRS' in 'Debug' notation.
---------------------------------------------------------------------------
showDRSDebug :: DRS -> String
showDRSDebug (LambdaDRS l) = "LambdaPDRS" ++ " "  ++ show l
showDRSDebug (Merge d1 d2) = "Merge"      ++ " (" ++ showDRSDebug d1 ++ ") (" ++ showDRSDebug d2 ++ ")"
showDRSDebug (DRS u c)     = "DRS"        ++ " "  ++ show u ++ " [" ++ intercalate "," (map showCon c) ++ "]"
  where showCon :: DRSCon -> String
        showCon (Rel r d)    = "Rel ("     ++ show r          ++ ")" ++ " " ++ show d
        showCon (Neg d1)     = "Neg ("     ++ showDRSDebug d1 ++ ")"
        showCon (Imp d1 d2)  = "Imp ("     ++ showDRSDebug d1 ++ ") (" ++ showDRSDebug d2 ++ ")"
        showCon (Or d1 d2)   = "Or ("      ++ showDRSDebug d1 ++ ") (" ++ showDRSDebug d2 ++ ")"
        showCon (Box d1)     = "Box ("     ++ showDRSDebug d1 ++ ")"
        showCon (Diamond d1) = "Diamond (" ++ showDRSDebug d1 ++ ")"
        showCon (Prop r d1)  = "Prop ("    ++ show r          ++ ") (" ++ showDRSDebug d1 ++ ")"

---------------------------------------------------------------------------
-- **  Showing the subparts of a DRS
---------------------------------------------------------------------------

---------------------------------------------------------------------------
-- | Shows whitespace of width @l@.
---------------------------------------------------------------------------
showWhitespace :: Int -> String
showWhitespace l = replicate l ' '

---------------------------------------------------------------------------
-- | Shows the universe @u@ of a 'DRS', using 'String' @d@ as a delimiter
-- between referents.
---------------------------------------------------------------------------
showUniverse :: [DRSRef] -> String -> String
showUniverse u d = intercalate d (map drsRefToDRSVar u)

---------------------------------------------------------------------------
-- | Shows the conditions @c@ of a 'DRS'.
---------------------------------------------------------------------------
showConditions :: [DRSCon] -> String
showConditions [] = " "
showConditions c  = foldr ((++) . showCon) "" c
  where showCon :: DRSCon -> String
        showCon (Rel r d) = drsRelToString r ++ "(" ++ intercalate "," (map drsRefToDRSVar d) ++ ")\n"
        showCon (Neg d1)
          | isLambdaDRS d1 = showModifier opNeg 0 b1
          | otherwise      = showModifier opNeg 2 b1
          where b1 = showDRSBox d1
        showCon (Imp d1 d2)
          | isLambdaDRS d1      && isLambdaDRS d2      = showConcat b1 (showModifier opImp 0 b2)
          | not(isLambdaDRS d1) && isLambdaDRS d2      = showConcat b1 (showModifier opImp 2 (showPadding b2))
          | isLambdaDRS d1      && not(isLambdaDRS d2) = showConcat (showPadding b1) (showModifier opImp 2 b2)
          | otherwise                                  = showConcat b1 (showModifier opImp 2 b2)
          where b1 = showDRSBox d1
                b2 = showDRSBox d2
        showCon (Or d1 d2)
          | isLambdaDRS d1      && isLambdaDRS d2      = showConcat b1 (showModifier opOr 0 b2)
          | not(isLambdaDRS d1) && isLambdaDRS d2      = showConcat b1 (showModifier opOr 2 (showPadding b2))
          | isLambdaDRS d1      && not(isLambdaDRS d2) = showConcat (showPadding b1) (showModifier opOr 2 b2)
          | otherwise                                  = showConcat b1 (showModifier opOr 2 b2)
          where b1 = showDRSBox d1
                b2 = showDRSBox d2
        showCon (Prop r d1)
          | isLambdaDRS d1 = showModifier (drsRefToDRSVar r ++ ":") 0 b1
          | otherwise      = showModifier (drsRefToDRSVar r ++ ":") 2 b1
          where b1 = showDRSBox d1
        showCon (Diamond d1)
          | isLambdaDRS d1 = showModifier opDiamond 0 b1
          | otherwise      = showModifier opDiamond 2 b1
          where b1 = showDRSBox d1
        showCon (Box d1)
          | isLambdaDRS d1 = showModifier opBox 0 b1
          | otherwise      = showModifier opBox 2 b1
          where b1 = showDRSBox d1

---------------------------------------------------------------------------
-- | Shows lambda abstractions over 'DRS' @d@.
---------------------------------------------------------------------------
showDRSLambdas :: DRS -> String
showDRSLambdas d = show' (drsLambdas d)
  where show' :: [(DRSVar,[DRSVar])] -> String
        show' []     = []
        show' ((l,_):ls) = opLambda ++ l ++ "." ++ show' ls

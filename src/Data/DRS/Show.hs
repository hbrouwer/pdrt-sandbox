-- Show.hs

{-# LANGUAGE FlexibleInstances #-}

{- |
  Show DRS
-}
module Data.DRS.Show
(
  showDRS
, printDRS
, showMerge
, printMerge
, showDRSBetaReduct
, printDRSBetaReduct
, showDRSRefBetaReduct
, printDRSRefBetaReduct

, boxTopLeft
, boxTopRight
, boxBottomLeft
, boxBottomRight
, boxMiddleLeft
, boxMiddleRight
, boxHorLine
, boxVerLine

, opNeg
, opImp
, opOr
, opDiamond
, opBox
, opLambda

, showConcat
, showContent
, showHorizontalLine
, showModifier
, showPadding
) where

import Data.DRS.Merge
import Data.DRS.Properties
import Data.DRS.Structure
import Data.DRS.Translate
import Data.DRS.Variables
import Data.List (intercalate, union)

-- | Derive an instance of the Show typeclass for DRS
instance Show DRS where
  show d
    | isFOLDRS rd = '\n' : showDRS rd ++ "\n" ++ show (drsToFOL rd) ++ "\n"
    | otherwise   = '\n' : showDRS rd
    where rd = drsResolveMerges d

-- | Typeclass for showable, but unresolved DRSs
class ShowableDRS d where 
  resolve :: d -> Int -> Int -> DRS

-- | Derive an instance of ShowableDRS for a resolved DRS
instance ShowableDRS DRS where
  resolve d _ _ = d

-- | Derive an instance of ShowableDRS for a DRS that requires
-- at least one DRS referent to resolve
instance (ShowableDRS d) => ShowableDRS (DRSRef -> d) where
  resolve ud nr nd = resolve (ud rv) (nr + 1) nd
    where rv = LambdaDRSRef ('r' : show nr, nr + nd)

-- | Derive an instance of ShowableDRS for a DRS that requires
-- at least one DRS to resolve
instance (ShowableDRS d) => ShowableDRS (DRS -> d) where
  resolve ud nr nd = resolve (ud lv) nr (nd + 1)
    where lv = LambdaDRS ('k' : show nd, nr + nd)

-- | Derive an instance of Show for a DRS that requires
-- at least one DRS referent to resolve
instance (ShowableDRS d) => Show (DRSRef -> d) where
  show d = show (resolve d 0 0)

-- | Derive an instance of Show for a DRS that requires
-- at least one DRS to resolve
instance (ShowableDRS d) => Show (DRS -> d) where
  show d = show (resolve d 0 0)

-- | Box construction constants
boxTopLeft     = '\x250C' -- Top left corner symbol
boxTopRight    = '\x2510' -- Top right corner symbol
boxBottomLeft  = '\x2514' -- Bottom left corner symbol
boxBottomRight = '\x2518' -- Bottom right corner symbol
boxMiddleLeft  = '\x251C' -- Middle left corner symbol
boxMiddleRight = '\x2524' -- Middle right corner symbol
boxHorLine     = '-'      -- Horizontal line symbol
boxVerLine     = '|'      -- Vertical line symbol

-- | Operator constants
opNeg     = "\x00AC" -- Negation symbol
opImp     = "\x21D2" -- Implication symbol
opOr      = "\x2228" -- Disjunction symbol
opDiamond = "\x25C7" -- Diamond symbol
opBox     = "\x25FB" -- Box symbol
opLambda  = "\x03BB" -- Lambda symbol
opMerge   = "\x002B" -- Merge symbol

-- | Shows a DRS
showDRS :: DRS -> String
showDRS d = showModifier (showDRSLambdas d) 2 (showDRSBox d)
--    Set    -> showDRSLambdas d ++ showDRSSet d ++ "\n"
--    Linear -> showDRSLambdas d ++ showDRSLinear d ++ "\n"
--    Boxes  -> showModifier (showDRSLambdas d) 2 (showDRSBox d)

-- | Shows a DRS in Set notation
showDRSSet :: DRS -> String
showDRSSet (LambdaDRS (v,_)) = v
showDRSSet (Merge d1 d2)
  | not(isLambdaDRS d1) && not(isLambdaDRS d2) = showDRSSet (d1 <<+>> d2)
  | otherwise                                  = showDRSSet d1 ++ " " ++ opMerge ++ " " ++ showDRSSet d2
showDRSSet (DRS u c)         = "<{" ++ showUniverse u ++ "}, {" ++ intercalate ", " (map showCon c) ++ "}>"
  where showUniverse :: [DRSRef] -> String
        showUniverse u = intercalate "," (map drsRefToDRSVar u)
        showCon :: DRSCon -> String
        showCon (Rel r d)    = r ++ "(" ++ intercalate "," (map drsRefToDRSVar d) ++ ")"
        showCon (Neg d1)     = opNeg ++ showDRSSet d1
        showCon (Imp d1 d2)  = showDRSSet d1 ++ " " ++ opImp ++ " " ++ showDRSSet d2
        showCon (Or d1 d2)   = showDRSSet d1 ++ " " ++ opOr  ++ " " ++ showDRSSet d2
        showCon (Prop r d1)  = drsRefToDRSVar r ++ ": " ++ showDRSSet d1
        showCon (Diamond d1) = opNeg ++ showDRSSet d1
        showCon (Box d1)     = opNeg ++ showDRSSet d1

-- | Shows a DRS in Linear notation
showDRSLinear :: DRS -> String
showDRSLinear (LambdaDRS (v,_)) = v
showDRSLinear (Merge d1 d2)
  | not(isLambdaDRS d1) && not(isLambdaDRS d2) = showDRSLinear (d1 <<+>> d2)
  | otherwise                                  = showDRSLinear d1 ++ " " ++ opMerge ++ " " ++ showDRSLinear d2
showDRSLinear (DRS u c)         = "[" ++ showUniverse u ++ ": " ++  intercalate ", " (map showCon  c) ++ "]"
  where showUniverse :: [DRSRef] -> String
        showUniverse u = intercalate "," (map drsRefToDRSVar u)
        showCon :: DRSCon -> String
        showCon (Rel r d)    = r ++ "(" ++ intercalate "," (map drsRefToDRSVar d) ++ ")"
        showCon (Neg d1)     = opNeg ++ showDRSLinear d1
        showCon (Imp d1 d2)  = showDRSLinear d1 ++ " " ++ opImp ++ " " ++ showDRSLinear d2
        showCon (Or d1 d2)   = showDRSLinear d1 ++ " " ++ opOr  ++ " " ++ showDRSLinear d2
        showCon (Prop r d1)  = drsRefToDRSVar r ++ ": " ++ showDRSLinear d1
        showCon (Diamond d1) = opNeg ++ showDRSLinear d1
        showCon (Box d1)     = opNeg ++ showDRSLinear d1

-- | Shows a DRS in Box notation
showDRSBox :: DRS -> String
showDRSBox (LambdaDRS (v,_)) = v ++ "\n"
showDRSBox (Merge d1 d2)
  | isLambdaDRS d1 && isLambdaDRS d2      = showConcat (showDRSBox d1) (showModifier opMerge 0 (showDRSBox d2))
  | not(isLambdaDRS d1) && isLambdaDRS d2 = showConcat (showDRSBox d1) (showModifier opMerge 2 (showPadding (showDRSBox d2)))
  | isLambdaDRS d1 && not(isLambdaDRS d2) = showConcat (showPadding (showDRSBox d1)) (showModifier opMerge 2 (showDRSBox d2))
  | otherwise                             = showDRSBox (d1 <<+>> d2)
showDRSBox (DRS u c)         = showHorizontalLine l boxTopLeft boxTopRight
  ++ showContent l ul ++ showHorizontalLine l boxMiddleLeft boxMiddleRight
  ++ showContent l cl ++ showHorizontalLine l boxBottomLeft boxBottomRight
  where ul = showUniverse u
        cl = showConditions c
        l  = 4 + maximum (map length (lines ul) `union` map length (lines cl))

-- | Shows a horizontal line of length @l@ with left corner symbol @lc@ and
-- right corner symbol @rc@
showHorizontalLine :: Int -> Char -> Char -> String
showHorizontalLine l lc rc = [lc] ++ replicate (l - 2) boxHorLine ++ [rc] ++ "\n"

-- | Shows DRS box content surrounded by vertical DRS box bars
showContent :: Int -> String -> String
showContent l s = unlines (map show (lines s))
  where show :: String -> String
        show s = [boxVerLine] ++ " " ++ s ++ showWhitespace (l - 4 - length s) ++ " " ++ [boxVerLine]

-- | Shows whitespace of width @l@
showWhitespace :: Int -> String
showWhitespace l = replicate l ' '

-- | Shows the universe @u@ of a DRS
showUniverse :: [DRSRef] -> String
showUniverse = foldr ((++) . (\r -> drsRefToDRSVar r ++ "  ")) " "

-- | Shows the conditions @c@ of a DRS
showConditions :: [DRSCon] -> String
showConditions [] = " "
showConditions c  = foldr ((++) . showCon) "" c
  where showCon :: DRSCon -> String
        showCon (Rel r d) = r ++ "(" ++ intercalate "," (map drsRefToDRSVar d) ++ ")\n"
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

-- | Adds two lines of whitespace to the beginning of string @s@
showPadding :: String -> String
showPadding s = showWhitespace l ++ "\n" ++ showWhitespace l ++ "\n" ++ s
  where l = length s - 1

-- | Shows a modifier @m@ at line number @p@ in front of string @s@
showModifier :: String -> Int -> String -> String
showModifier m p s = unlines (modifier 0 (lines s))
  where modifier :: Int -> [String] -> [String]
        modifier _ [] = []
        modifier n (l:ls)
          | n == p    = (m ++ " " ++ l) : modifier (n + 1) ls
          | otherwise = (showWhitespace (length m + 1) ++ l) : modifier (n + 1) ls

-- | Shows the line by line concatenation of two strings
showConcat :: String -> String -> String
showConcat s1 s2 = unlines (conc ls1 ls2)
  where conc :: [String] -> [String] -> [String]
        conc [] []         = []
        conc (a:as) []     = (a ++ " " ++ showWhitespace (length (head ls2))) : conc as []
        conc [] (b:bs)     = (showWhitespace (length (head ls1)) ++ " " ++ b) : conc [] bs
        conc (a:as) (b:bs) = (a ++ " " ++ b) : conc as bs
        ls1 = lines s1
        ls2 = lines s2

-- | Shows lambda abstractions over DRS @d@
showDRSLambdas :: DRS -> String
showDRSLambdas d = show (drsLambdas d)
  where show :: [DRSVar] -> String
        show []     = []
        show (l:ls) = opLambda ++ l ++ "." ++ show ls

-- | Prints a DRS
printDRS :: DRS -> IO ()
printDRS d = putStrLn $ '\n' : showDRS d

-- | Shows a merge between two DRSs
showMerge :: DRS -> DRS -> String
showMerge d1 d2 = showConcat (showConcat b1 (showModifier "+" 2 b2)) (showModifier "=" 2 mr)
  where b1 = showDRS d1
        b2 = showDRS d2
        mr = showDRS (d1 <<+>> d2)

-- | Prints a merge between two DRSs
printMerge :: DRS -> DRS -> IO ()
printMerge d1 d2 = putStrLn $ '\n' : showMerge d1 d2

-- | Shows the beta reduction of an unresolved DRS @d1@ with a DRS @d2@
showDRSBetaReduct :: (ShowableDRS d) => (DRS -> d) -> DRS -> String
showDRSBetaReduct d1 d2 = showConcat (showConcat (showModifier "(" 2 b1) (showModifier ")" 2 b2)) (showModifier "=" 2 br)
  where b1 = showDRS (resolve d1 0 0)
        b2 = showDRS d2
        br = showDRS (resolve (d1 d2) 0 0)

-- | Prints the beta reduction of an unresolved DRS @d1@ with a DRS @d2@
printDRSBetaReduct :: (ShowableDRS d) => (DRS -> d) -> DRS -> IO ()
printDRSBetaReduct d1 d2 = putStrLn $ '\n' : showDRSBetaReduct d1 d2

-- | Shows the beta reduction of an unresolved DRS @d@ with a DRS referent @r@
showDRSRefBetaReduct :: (ShowableDRS d) => (DRSRef -> d) -> DRSRef -> String
showDRSRefBetaReduct d r@(DRSRef v) = showConcat (showConcat (showModifier "(" 2 bx) (showModifier ")" 2 rv)) (showModifier "=" 2 br)
  where bx = showDRS (resolve d 0 0)
        rv = showPadding (v ++ "\n")
        br = showDRS (resolve (d r) 0 0)

-- | Prints the beta reduction of an unresolved DRS @d@ with a DRS referent @r@
printDRSRefBetaReduct :: (ShowableDRS d) => (DRSRef -> d) -> DRSRef -> IO ()
printDRSRefBetaReduct d r = putStrLn $ '\n' : showDRSRefBetaReduct d r

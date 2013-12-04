{- |
Module      :  Data.DRS.Input.String
Copyright   :  (c) Harm Brouwer and Noortje Venhuizen
License     :  Apache-2.0

Maintainer  :  me@hbrouwer.eu, n.j.venhuizen@rug.nl
Stability   :  provisional
Portability :  portable

String to DRS
-}

module Data.DRS.Input.String
(
  stringNegOps
, stringImpOps
, stringOrOps
, stringBoxOps
, stringDiamondOps
, stringToDRS
, BracketType (..)
, brackets
, felicitousBracketing
, dropOuterBrackets
, takeUpToMatchingBracket
, dropUpToMatchingBracket
, replaceArrows
, splitOn
) where

import Data.DRS.Structure

import Data.Char (isSpace, toLower)
import Data.List (intercalate)

---------------------------------------------------------------------------
-- * Exported
---------------------------------------------------------------------------

---------------------------------------------------------------------------
-- ** String representations for operators
---------------------------------------------------------------------------

-- | Negation operators (case insensitive): @!, not, neg@.
stringNegOps     = ["!", "not", "neg"]

-- | Implication operators (case insensitive): @imp, ->, =>, then@.
stringImpOps     = ["imp", "->", "=>", "then"]

-- | Disjuction operators (case insensitive): @v, or@.
stringOrOps      = ["v", "or"]

-- | Box operators (case insensitive): @b, box, necessary@.
stringBoxOps     = ["b", "box", "necessary"]

-- | Diamond operators (case insensitive): @d, diamond, maybe@.
stringDiamondOps = ["d", "diamond", "maybe"]

---------------------------------------------------------------------------
-- ** String to DRS Conversion
---------------------------------------------------------------------------

---------------------------------------------------------------------------
-- | Transforms a 'String' representation of a DRS into a 'DRS'.
---------------------------------------------------------------------------
stringToDRS :: String -> DRS
stringToDRS s@('<':_)
  | felicitousBracketing s1 = DRS (parseRefs s2) (parseCons (tail (dropUpToMatchingBracket Curly s2)))
  | otherwise               = error "infelicitous bracketing"
  where s1 = filter (not . isSpace) (replaceArrows s)
        s2 = dropOuterBrackets s1

---------------------------------------------------------------------------
-- * Private
---------------------------------------------------------------------------

---------------------------------------------------------------------------
-- | Data type for brackets.
---------------------------------------------------------------------------
data BracketType = Parentheses | Curly | Angle

---------------------------------------------------------------------------
-- | Returns tuple with brackets from given 'BracketType'.
---------------------------------------------------------------------------
brackets :: BracketType -> (Char,Char)
brackets Parentheses = ('(',')')
brackets Curly       = ('{','}')
brackets Angle       = ('<','>')

---------------------------------------------------------------------------
-- | Checks if 'String @s@' contains the same number of opening and
-- closing brackets of the same type.
---------------------------------------------------------------------------
felicitousBracketing :: String -> Bool
felicitousBracketing s = isFelicitous s 0 0 0
  where isFelicitous :: String -> Int -> Int -> Int -> Bool
        isFelicitous []     np nc na = np == 0 && nc == 0 && na == 0
        isFelicitous (c:cs) np nc na
          | c == '('           = isFelicitous cs (np + 1) nc na
          | c == ')'           = isFelicitous cs (np - 1) nc na
          | c == '{'           = isFelicitous cs np (nc + 1) na
          | c == '}'           = isFelicitous cs np (nc - 1) na
          | c == '<'           = isFelicitous cs np nc (na + 1)
          | c == '>'           = isFelicitous cs np nc (na - 1)
          | otherwise          = isFelicitous cs np nc na

---------------------------------------------------------------------------
-- | Removes the outer brackets from a 'String'.
---------------------------------------------------------------------------
dropOuterBrackets :: String -> String
dropOuterBrackets = tail . init

---------------------------------------------------------------------------
-- | Returns part of 'String' @s@ between opening bracket @ob@ of type @bt@
-- and its matching closing bracket.
---------------------------------------------------------------------------
takeUpToMatchingBracket :: BracketType -> String -> String
takeUpToMatchingBracket bt (ob:s) = takeUpTo s [ob] 0
  where ob = fst bs
        bs = brackets bt
        takeUpTo :: String -> String -> Int -> String
        takeUpTo []     s n = reverse s
        takeUpTo (c:cs) s n
          | c == snd bs && n == 0 = reverse (c:s)
          | c == snd bs && n > 0  = takeUpTo cs (c:s) (n - 1)
          | c == fst bs           = takeUpTo cs (c:s) (n + 1)
          | otherwise             = takeUpTo cs (c:s) n

---------------------------------------------------------------------------
-- | Returns part of 'String' @s@ after opening bracket @ob@ of type @bt@
-- and its matching closing bracket.
---------------------------------------------------------------------------
dropUpToMatchingBracket :: BracketType -> String -> String
dropUpToMatchingBracket _  []     = []
dropUpToMatchingBracket bt (ob:s) = dropUpTo s 0
  where ob = fst bs
        bs = brackets bt
        dropUpTo :: String -> Int -> String
        dropUpTo []     n = []
        dropUpTo (c:cs) n
          | c == snd bs && n == 0 = cs
          | c == snd bs && n > 0  = dropUpTo cs (n - 1)
          | c == fst bs           = dropUpTo cs (n + 1)
          | otherwise             = dropUpTo cs n

---------------------------------------------------------------------------
-- | Replaces ASCII representations of arrows in 'String' @s@ by operator
-- @"imp"@.
---------------------------------------------------------------------------
replaceArrows :: String -> String
replaceArrows s = replace s []
  where replace :: String -> String -> String
        replace [] s'          = s'
        replace ('-':'>':cs) s' = replace cs (s' ++ "imp")
        replace ('=':'>':cs) s' = replace cs (s' ++ "imp")
        replace (c:cs)       s' = replace cs (s' ++ [c])

---------------------------------------------------------------------------
-- | Converts a 'String' into a set of 'DRSRef's.
---------------------------------------------------------------------------
parseRefs :: String -> [DRSRef]
parseRefs []        = []
parseRefs s@('{':_) = map DRSRef (splitOn ',' (dropOuterBrackets $ takeUpToMatchingBracket Curly s))

---------------------------------------------------------------------------
-- | Converts a 'String' into a set of 'DRSCon's.
---------------------------------------------------------------------------
parseCons :: String -> [DRSCon]
parseCons []        = []
parseCons s@('{':_) = parse $ dropOuterBrackets $ takeUpToMatchingBracket Curly s
  where parse :: String -> [DRSCon]
        parse []      = []
        parse (',':s) = parse s
        parse s
          | pfx_op `elem` stringNegOps     = Neg     (stringToDRS d1)                   : parse (drop (length pfx_op + length d1) s)
          | ifx_op `elem` stringImpOps     = Imp     (stringToDRS d1) (stringToDRS d2)  : parse (drop (length ifx_op + length d1 + length d2) s)
          | ifx_op `elem` stringOrOps      = Or      (stringToDRS d1) (stringToDRS d2)  : parse (drop (length ifx_op + length d1 + length d2) s)
          | ':'    `elem` pfx_op           = Prop    (DRSRef prop_r)  (stringToDRS d1)  : parse (drop (length prop_r + 1 + length d1) s)
          | pfx_op `elem` stringDiamondOps = Diamond (stringToDRS d1)                   : parse (drop (length pfx_op + length d1) s)
          | pfx_op `elem` stringBoxOps     = Box     (stringToDRS d1)                   : parse (drop (length pfx_op + length d1) s)
          | otherwise                      = Rel     (DRSRel rel)     (map DRSRef refs) : parse (drop (length rel + 2 + length (intercalate "," refs)) s)
          where pfx_op = map toLower (takeWhile (/= '<') s)
                ifx_op = map toLower (takeWhile (/= '<') (dropUpToMatchingBracket Angle s))
                prop_r = takeWhile (/= ':') s
                rel    = takeWhile (/= '(') s
                refs   = splitOn ',' (dropOuterBrackets (takeUpToMatchingBracket Parentheses (dropWhile (/= '(') s)))
                d1     = takeUpToMatchingBracket Angle is
                d2     = takeUpToMatchingBracket Angle (drop (length ifx_op) (dropUpToMatchingBracket Angle is))
                is     = dropWhile (/= '<') s

---------------------------------------------------------------------------
-- | Modification of 'words', where 'String' @s@ is broken into parts based
-- on delimiter @c@.
---------------------------------------------------------------------------
splitOn :: Char -> String -> [String]
splitOn c s = case dropWhile (c ==) s of 
  "" -> []
  s1 -> w : splitOn c s2
        where (w, s2) = break (c ==) s1

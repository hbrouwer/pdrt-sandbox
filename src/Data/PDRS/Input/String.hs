{- |
Module      :  Data.PDRS.Input.String
Copyright   :  (c) Harm Brouwer and Noortje Venhuizen
License     :  Apache-2.0

Maintainer  :  me@hbrouwer.eu, n.j.venhuizen@rug.nl
Stability   :  provisional
Portability :  portable

String to PDRS
-}

module Data.PDRS.Input.String
(
  stringToPDRS
) where

import Data.Char (isSpace, toLower)
import Data.DRS.Input.String
import Data.List (intercalate)
import Data.PDRS.Structure

---------------------------------------------------------------------------
-- * Exported
---------------------------------------------------------------------------

---------------------------------------------------------------------------
-- | Transforms a 'String' representation of a PDRS into a 'PDRS'.
---------------------------------------------------------------------------

stringToPDRS :: String -> PDRS
stringToPDRS s@('<':_)
  | felicitousBracketing s' = parsePDRS (filter (not . isSpace) s')
  | otherwise               = error "infelicitous bracketing"
  where s' = replaceArrows s

---------------------------------------------------------------------------
-- * Private
---------------------------------------------------------------------------

---------------------------------------------------------------------------
-- | Converts a 'String' into a 'PDRS'.
---------------------------------------------------------------------------
parsePDRS :: String -> PDRS
parsePDRS s = PDRS l m u c
  where l  = read $ takeWhile (/= ',') (dropOuterBrackets s)
        m  = parseMAPs $ tail (dropUpToMatchingBracket Curly (tail (dropUpToMatchingBracket Curly s')))
        u  = parseRefs s'
        c  = parseCons $ tail (dropUpToMatchingBracket Curly s')
        s' = tail $ dropWhile (/= ',') s

---------------------------------------------------------------------------
-- | Converts a 'String' into a set of 'PRef's.
---------------------------------------------------------------------------
parseRefs :: String -> [PRef]
parseRefs [] = []
parseRefs s  = parse $ dropOuterBrackets $ takeUpToMatchingBracket Curly s
  where parse :: String -> [PRef]
        parse [] = []
        parse (',':s) = parse s
        parse s = PRef p (PDRSRef r) : parse (drop (length (show p) + length r + 3) s)
          where p = read $ head t
                r = head $ tail t
                t = splitOn ',' (dropOuterBrackets $ takeUpToMatchingBracket Parentheses s)

---------------------------------------------------------------------------
-- | Converts a 'String' into a set of 'PCon's.
---------------------------------------------------------------------------
parseCons :: String -> [PCon]
parseCons []        = []
parseCons s@('{':_) = parse $ dropOuterBrackets $ takeUpToMatchingBracket Curly s
  where parse :: String -> [PCon]
        parse []      = []
        parse (',':s) = parse s
        parse s
          | pfx `elem` opNegString     = PCon p (Neg     (parsePDRS d1))                   : parse (drop (pl + length pfx  + length d1) s)
          | ifx `elem` opImpString     = PCon p (Imp     (parsePDRS d1) (parsePDRS d2))    : parse (drop (pl + length ifx  + length d1 + length d2) s)
          | ifx `elem` opOrString      = PCon p (Or      (parsePDRS d1) (parsePDRS d2))    : parse (drop (pl + length ifx  + length d1 + length d2) s)
          | ':' `elem` pfx             = PCon p (Prop    (PDRSRef prop) (parsePDRS d1))    : parse (drop (pl + length prop + 1 + length d1) s)
          | pfx `elem` opDiamondString = PCon p (Diamond (parsePDRS d1))                   : parse (drop (pl + length pfx  + length d1) s)
          | pfx `elem` opBoxString     = PCon p (Box     (parsePDRS d1))                   : parse (drop (pl + length pfx  + length d1) s)
          | otherwise                  = PCon p (Rel     (PDRSRel rel) (map PDRSRef refs)) : parse (drop (pl + length rel  + 2 + length (intercalate "," refs)) s)
          where pfx  = map toLower (takeWhile (/= '<') c)
                ifx  = map toLower (takeWhile (/= '<') (dropUpToMatchingBracket Angle c))
                prop = takeWhile (/= ':') c
                rel  = takeWhile (/= '(') c
                d1   = takeUpToMatchingBracket Angle (dropWhile (/= '<') c)
                d2   = takeUpToMatchingBracket Angle (drop (length ifx) (dropUpToMatchingBracket Angle (dropWhile (/= '<') c)))
                refs = splitOn ',' (dropOuterBrackets (takeUpToMatchingBracket Parentheses (dropWhile (/= '(') c)))
                c  = tail $ dropWhile (/= ',') t
                p  = read $ takeWhile (/= ',') t
                t  = dropOuterBrackets $ takeUpToMatchingBracket Parentheses s
                pl = length (show p) + 3

---------------------------------------------------------------------------
-- | Converts a 'String' into a set of 'MAP's.
---------------------------------------------------------------------------
parseMAPs :: String -> [MAP]
parseMAPs [] = []
parseMAPs s  = parse $ dropOuterBrackets $ takeUpToMatchingBracket Curly s
  where parse :: String -> [MAP]
        parse [] = []
        parse (',':s) = parse s
        parse s = (p1,p2) : parse (drop (length (show p1) + length (show p2) + 3) s)
          where p1 = read $ head t
                p2 = read $ head $ tail t
                t  = splitOn ',' (dropOuterBrackets $ takeUpToMatchingBracket Parentheses s)

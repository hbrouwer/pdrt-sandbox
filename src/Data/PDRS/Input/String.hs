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

import Data.PDRS.Structure

import Data.Char (isSpace, toLower)

import Data.DRS.Input.String (stringNegOps, stringImpOps, stringOrOps, stringBoxOps, stringDiamondOps)
import Data.DRS.Input.String (BracketType (..), brackets, felicitousBracketing, dropOuterBrackets)
import Data.DRS.Input.String (takeUpToMatchingBracket, dropUpToMatchingBracket)
import Data.DRS.Input.String (replaceArrows, splitOn)

import Data.List (intercalate)

---------------------------------------------------------------------------
-- * Exported
---------------------------------------------------------------------------

---------------------------------------------------------------------------
-- ** String to PDRS Conversion
---------------------------------------------------------------------------

---------------------------------------------------------------------------
-- | Transforms a 'String' representation of a PDRS into a 'PDRS'.
---------------------------------------------------------------------------

stringToPDRS :: String -> PDRS
stringToPDRS s@('<':_)
  | felicitousBracketing s1 = PDRS l m u c
  | otherwise               = error "infelicitous bracketing"
  where s1 = filter (not . isSpace) (replaceArrows s)
        s2 = dropOuterBrackets s1
        s3 = tail $ dropWhile (/= ',') s2
        l  = read $ takeWhile (/= ',') s2
        u  = parseRefs s3
        c  = parseCons $ tail (dropUpToMatchingBracket Curly s3)
        m  = parseMAPs $ tail (dropUpToMatchingBracket Curly (tail (dropUpToMatchingBracket Curly s3)))

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

parseCons :: String -> [PCon]
parseCons []        = []
parseCons s@('{':_) = parse $ dropOuterBrackets $ takeUpToMatchingBracket Curly s
  where parse :: String -> [PCon]
        parse []      = []
        parse (',':s) = parse s
        parse s
          | pfx_op `elem` stringNegOps     = PCon p (Neg     (stringToPDRS d1)                   ) : parse (drop (pl + length pfx_op + length d1) s)
          | ifx_op `elem` stringImpOps     = PCon p (Imp     (stringToPDRS d1) (stringToPDRS d2) ) : parse (drop (pl + length ifx_op + length d1 + length d2) s)
          | ifx_op `elem` stringOrOps      = PCon p (Or      (stringToPDRS d1) (stringToPDRS d2) ) : parse (drop (pl + length ifx_op + length d1 + length d2) s)
          | ':'    `elem` pfx_op           = PCon p (Prop    (PDRSRef prop_r)  (stringToPDRS d1) ) : parse (drop (pl + length prop_r + 1 + length d1) s)
          | pfx_op `elem` stringDiamondOps = PCon p (Diamond (stringToPDRS d1)                   ) : parse (drop (pl + length pfx_op + length d1) s)
          | pfx_op `elem` stringBoxOps     = PCon p (Box     (stringToPDRS d1)                   ) : parse (drop (pl + length pfx_op + length d1) s)
          | otherwise                      = PCon p (Rel     (PDRSRel rel)     (map PDRSRef refs)) : parse (drop (pl + length rel + 2 + length (intercalate "," refs)) s)
          where p = read $ takeWhile (/= ',') t
                c = tail $ dropWhile (/= ',') t
                t = dropOuterBrackets $ takeUpToMatchingBracket Parentheses s
                pfx_op = map toLower (takeWhile (/= '<') c)
                ifx_op = map toLower (takeWhile (/= '<') (dropUpToMatchingBracket Angle c))
                prop_r = takeWhile (/= ':') c
                rel    = takeWhile (/= '(') c
                refs   = splitOn ',' (dropOuterBrackets (takeUpToMatchingBracket Parentheses (dropWhile (/= '(') c)))
                d1     = takeUpToMatchingBracket Angle is
                d2     = takeUpToMatchingBracket Angle (drop (length ifx_op) (dropUpToMatchingBracket Angle is))
                is     = dropWhile (/= '<') c
                pl     = length (show p) + 3

parseMAPs :: String -> [(PVar,PVar)]
parseMAPs [] = []
parseMAPs s  = parse $ dropOuterBrackets $ takeUpToMatchingBracket Curly s
  where parse :: String -> [(PVar,PVar)]
        parse [] = []
        parse (',':s) = parse s
        parse s = (p1,p2) : parse (drop (length (show p1) + length (show p2) + 3) s)
          where p1 = read $ head t
                p2 = read $ head $ tail t
                t  = splitOn ',' (dropOuterBrackets $ takeUpToMatchingBracket Parentheses s)

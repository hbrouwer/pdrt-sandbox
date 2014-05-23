{- |
Module      :  Data.PDRS.Input.Boxer
Copyright   :  (c) Harm Brouwer and Noortje Venhuizen
License     :  Apache-2.0

Maintainer  :  me@hbrouwer.eu, n.j.venhuizen@rug.nl
Stability   :  provisional
Portability :  portable

Converts Boxer's Prolog output to PDRS
-}

module Data.PDRS.Input.Boxer
(
  boxerToPDRS
) where

import Data.Char (isNumber, toUpper)
import Data.List (isPrefixOf)
import Data.DRS.Input.Boxer
import Data.DRS.Input.String
import Data.PDRS.DataType

---------------------------------------------------------------------------
-- * Exported
---------------------------------------------------------------------------

---------------------------------------------------------------------------
-- | Converts Boxer's output into a 'DRS'.
---------------------------------------------------------------------------
boxerToPDRS :: String -> PDRS
boxerToPDRS s@('s':'e':'m':'(':_) = plPDRSToPDRS $ replaceLambdas (convertPrologVars plpdrs []) 0
  where plpdrs = tail $ dropUpToMatchingBracket Square (dropWhile (/= '[') s)
boxerToPDRS _                     = error "infelicitous input string"

---------------------------------------------------------------------------
-- * Private
---------------------------------------------------------------------------

---------------------------------------------------------------------------
-- | Converts a 'PrologDRS' into a 'DRS'.
---------------------------------------------------------------------------
plPDRSToPDRS :: PrologDRS -> PDRS
plPDRSToPDRS s
  | pdrsType == "drs"    = PDRS label [] (parsePlRefs pdrs) (parsePlCons (tail (dropUpToMatchingBracket Square pdrs)))
  | pdrsType == "merge"  = AMerge (plPDRSToPDRS pdrs) (plPDRSToPDRS pdrs')
  | pdrsType == "smerge" = AMerge (plPDRSToPDRS pdrs) (plPDRSToPDRS pdrs')
  | pdrsType == "alfa"   = PMerge (plPDRSToPDRS (tail (dropWhile (/= ',') pdrs))) (plPDRSToPDRS pdrs')
  | pdrsType == "lambda" = LambdaPDRS ((takeWhile (/= ':') pdrs,[]), read (dropWhile (/= ':') pdrs) :: Int)
  | pdrsType == "app"    = LambdaPDRS ((takeWhile (/= ':') l,[last sd]), read (tail (dropWhile (/= ':') (init l))) :: Int)
  | otherwise            = error "not a valid PDRS"
  where pdrsType = (takeWhile (/= '(') . tail . dropWhile (/= ':')) s
        label    = read ((filter isNumber . takeWhile (/= ':')) s) :: Int
        pdrs     = dropOuterBrackets $ takeUpToMatchingBracket Parentheses (dropWhile (/= '(') s)
        pdrs'    = tail (dropUpToMatchingBracket Parentheses (dropWhile (/= '(') pdrs))
        -- | For app:
        l  = tail (dropWhile (/= '(') (head sd))
        sd = splitOn ',' pdrs

---------------------------------------------------------------------------
-- | Converts a 'String' with Prolog referents into a set of 'PRef's.
---------------------------------------------------------------------------
parsePlRefs :: String -> [PRef]
parsePlRefs [] = []
parsePlRefs s@(b:_)
  | b == '['  = map parse (splitOn ',' (dropOuterBrackets $ takeUpToMatchingBracket Square s))
  | otherwise = error "infelicitous input string"
  where parse :: String -> PRef
        parse r = PRef lab (toPDRSRef r')
          where lab = read ((filter isNumber . takeWhile (/= ':')) r) :: Int
                r'  = tail (tail (dropWhile (/= ']') r))

---------------------------------------------------------------------------
-- | Converts a 'String' with Prolog conditions into a set of 'PCon's.
---------------------------------------------------------------------------
parsePlCons :: String -> [PCon]
parsePlCons [] = []
parsePlCons s@(b:_)
  | b == '['  = parse (dropOuterBrackets $ takeUpToMatchingBracket Square s)
  | otherwise = error "infelicitous input string"
  where parse :: String -> [PCon]
        parse [] = []
        parse (',':cs) = parse cs
        parse cs
          | pfx == "not"   = PCon lab (Neg     (plPDRSToPDRS c))                                                         : etc
          | pfx == "imp"   = PCon lab (Imp     (plPDRSToPDRS c) (plPDRSToPDRS c'))                                       : etc
          | pfx == "or"    = PCon lab (Or      (plPDRSToPDRS c) (plPDRSToPDRS c'))                                       : etc
          | pfx == "pos"   = PCon lab (Diamond (plPDRSToPDRS c))                                                         : etc
          | pfx == "nec"   = PCon lab (Box     (plPDRSToPDRS c))                                                         : etc
          | pfx == "prop"  = PCon lab (Prop    (toPDRSRef (takeWhile (/= ',') c)) (plPDRSToPDRS (dropWhile (/= ',') c))) : etc
          | pfx == "pred"  = PCon lab (Rel     (PDRSRel (ct !! 1))                [toPDRSRef (head ct)])                 : etc
          | pfx == "rel"   = PCon lab (Rel     (PDRSRel (ct !! 2))                (map toPDRSRef (take 2 ct)))           : etc
          | pfx == "role"  = PCon lab (Rel     (PDRSRel (capitalize (ct !! 2)))   (map toPDRSRef (take 2 ct)))           : etc
          | pfx == "named" = PCon lab (Rel     (PDRSRel (capitalize (ct !! 1)))   [toPDRSRef (head ct)])                 : etc
          | pfx == "timex" = PCon lab (Rel     (PDRSRel (ct !! 1))                [toPDRSRef (head ct)])                 : etc
          | pfx == "card"  = PCon lab (Rel     (PDRSRel ((ct !! 2) ++ (ct !! 1))) [toPDRSRef (head ct)])                 : etc
          | pfx == "eq"    = PCon lab (Rel     (PDRSRel "=")                      (map toPDRSRef ct))                    : etc
          | otherwise      = error "not a valid condition"
          where pfx = (reverse . takeWhile (/= ':'). reverse . takeWhile (/= '(')) cs
                lab = read ((filter isNumber . takeWhile (/= ':')) cs) :: Int
                c   = dropOuterBrackets $ takeUpToMatchingBracket Parentheses (dropWhile (/= '(') cs)
                etc = parse ((drop (length c + 2) . dropWhile (/= '(')) cs)
                c'  = tail $ dropUpToMatchingBracket Parentheses (dropWhile (/= '(') c)
                ct  = splitOn ',' c
                capitalize :: String -> String
                capitalize []    = []
                capitalize (h:t) = toUpper h:t

---------------------------------------------------------------------------
-- | Converts a 'String' to a 'PDRSRef', which may be a 'LambdaPDRSRef'.
---------------------------------------------------------------------------
toPDRSRef :: String -> PDRSRef
toPDRSRef r
  | "lambda(" `isPrefixOf` r = LambdaPDRSRef ((takeWhile (/= ':') (drop 7 r),[]),read (dropWhile (/= ':') r) :: Int)
  | otherwise                = PDRSRef r

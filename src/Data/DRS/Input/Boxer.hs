{- |
Module      :  Data.DRS.Input.Boxer
Copyright   :  (c) Harm Brouwer and Noortje Venhuizen
License     :  Apache-2.0

Maintainer  :  me@hbrouwer.eu, n.j.venhuizen@rug.nl
Stability   :  provisional
Portability :  portable

Converts Boxer's Prolog output to DRS
-}

module Data.DRS.Input.Boxer
(
  PrologDRS
, boxerToDRS
, plDRSToDRS

, toDRSRef
, replaceLambdas
) where

import Data.Char (isPunctuation, toUpper)
import Data.DRS.DataType
import Data.DRS.Input.String

---------------------------------------------------------------------------
-- * Exported
---------------------------------------------------------------------------

-- | Data type for 'PrologDRS'.
type PrologDRS = String

---------------------------------------------------------------------------
-- | Converts Boxer's output into a 'DRS'.
---------------------------------------------------------------------------
boxerToDRS :: String -> DRS
boxerToDRS s@('s':'e':'m':'(':_) = plDRSToDRS $ tail (dropUpToMatchingBracket Square (dropWhile (/= '[') s))

---------------------------------------------------------------------------
-- | Converts a 'PrologDRS' into a 'DRS'.
---------------------------------------------------------------------------
plDRSToDRS :: PrologDRS -> DRS
plDRSToDRS s
  | drsType == "drs"    = DRS   (parsePlRefs drs) (parsePlCons (tail (dropUpToMatchingBracket Square drs)))
  | drsType == "merge"  = Merge (plDRSToDRS drs)  (plDRSToDRS drs')
  | drsType == "smerge" = Merge (plDRSToDRS drs)  (plDRSToDRS drs')
  | drsType == "alfa"   = Merge (plDRSToDRS (tail (dropWhile (/= ',') drs))) (plDRSToDRS drs')
  | drsType == "lambda" = LambdaDRS ((takeWhile (/= ':') drs,[]), read (dropWhile (/= ':') drs) :: Int)
  | drsType == "app"    = LambdaDRS ((takeWhile (/= ':') l,[last sd]), read (tail (dropWhile (/= ':') (init l))) :: Int)
  | otherwise           = error "not a valid DRS"
  where s'      = replaceLambdas s 0
        drsType = takeWhile (/= '(') s'
        drs     = dropOuterBrackets $ takeUpToMatchingBracket Parentheses (drop (length drsType) s')
        drs'    = tail (dropUpToMatchingBracket Parentheses (dropWhile (/= '(') drs))
        -- | For app:
        l  = tail (dropWhile (/= '(') (head sd))
        sd = splitOn ',' drs

---------------------------------------------------------------------------
-- * Private
---------------------------------------------------------------------------

---------------------------------------------------------------------------
-- Converts a 'String' to a 'DRSRef', which may be a 'LambdaDRSRef'.
---------------------------------------------------------------------------
toDRSRef :: String -> DRSRef
toDRSRef r
  | (take 7 r) == "lambda(" = LambdaDRSRef ((takeWhile (/= ':') (drop 7 r),[]),read (dropWhile (/= ':') r) :: Int)
  | otherwise               = DRSRef r

---------------------------------------------------------------------------
-- | Converts a 'String' with Prolog referents into a set of 'DRSRef's.
---------------------------------------------------------------------------
parsePlRefs :: String -> [DRSRef]
parsePlRefs []        = []
parsePlRefs s@('[':_) = map (toDRSRef . strip) (splitOn ',' (dropOuterBrackets $ takeUpToMatchingBracket Square s))
  where strip :: String -> String
        strip r@('[':_) = strip (dropUpToMatchingBracket Square r)
        strip r@(':':d) = d

---------------------------------------------------------------------------
-- | Converts a 'String' with Prolog conditions into a set of 'DRSCon's.
---------------------------------------------------------------------------
parsePlCons :: String -> [DRSCon]
parsePlCons []        = []
parsePlCons s@('[':_) = parse (dropOuterBrackets $ takeUpToMatchingBracket Square s)
  where parse :: String -> [DRSCon]
        parse [] = []
        parse (',':cs)   = parse cs
        parse (':':cs)   = parse cs
        parse cs@('[':_) = parse (dropUpToMatchingBracket Square cs)
        parse cs
          | pfx == "not"   = Neg     (plDRSToDRS c)                                                     : etc
          | pfx == "imp"   = Imp     (plDRSToDRS c) (plDRSToDRS c')                                     : etc
          | pfx == "or"    = Or      (plDRSToDRS c) (plDRSToDRS c')                                     : etc
          | pfx == "pos"   = Diamond (plDRSToDRS c)                                                     : etc
          | pfx == "nec"   = Box     (plDRSToDRS c)                                                     : etc
          | pfx == "prop"  = Prop (toDRSRef (takeWhile (/= ',') c)) (plDRSToDRS (dropWhile (/= ',') c)) : etc
          | pfx == "pred"  = Rel  (DRSRel (ct !! 1))                [toDRSRef (head ct)]                : etc
          | pfx == "rel"   = Rel  (DRSRel (ct !! 2))                (map toDRSRef (take 2 ct))          : etc
          | pfx == "role"  = Rel  (DRSRel (capitalize (ct !! 2)))   (map toDRSRef (take 2 ct))          : etc
          | pfx == "named" = Rel  (DRSRel (capitalize (ct !! 1)))   [toDRSRef (head ct)]                : etc
          | pfx == "timex" = Rel  (DRSRel (ct !! 1))                [toDRSRef (head ct)]                : etc
          | pfx == "card"  = Rel  (DRSRel ((ct !! 2) ++ (ct !! 1))) [toDRSRef (head ct)]                : etc
          | pfx == "eq"    = Rel  (DRSRel "=")                      (map toDRSRef ct)                   : etc
          | otherwise      = error "not a valid condition"
          where pfx = takeWhile (/= '(') cs
                c   = dropOuterBrackets $ takeUpToMatchingBracket Parentheses (drop (length pfx) cs)
                ct  = splitOn ',' c
                etc = parse (drop (length pfx + length c + 2) cs)
                c'  = tail $ dropUpToMatchingBracket Parentheses (dropWhile (/= '(') c)
                capitalize :: String -> String
                capitalize (h:t) = toUpper h:t

---------------------------------------------------------------------------
-- | Replaces all lambda-variables in a 'PrologDRS' by lambda-identifiers.
---------------------------------------------------------------------------
replaceLambdas :: String -> Int -> String
replaceLambdas [] _  = []
replaceLambdas s i 
  | drsType == "lam" = replaceLambdas (replace (tail $ dropWhile (/= ',') drs) (takeWhile  (/= ',') (tail drs)) i) (i + 1)
  | otherwise        = (head s) : replaceLambdas (tail s) i
  where drsType = takeWhile (/= '(') s
        drs     = dropWhile (/= '(') s
        replace :: String -> String -> Int -> String
        replace [] _ _                                    = []
        replace d@(h:t) l j 
          | init lv == l && isPunctuation (last lv) = "lambda(" ++ l ++ ":" ++ show i ++ ")" ++ replace (drop (length l) d) l j
          | otherwise                               = h : (replace t l j)
          where lv = take (length l + 1) d


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
, replaceLambdas
, convertPrologVars
) where

import Data.Char (isAlpha, isNumber, isPunctuation, toUpper)
import Data.List (partition, isPrefixOf)
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
boxerToDRS s@('s':'e':'m':'(':_) = plDRSToDRS $ replaceLambdas pldrs 0
  where pldrs = tail $ dropUpToMatchingBracket Square (dropWhile (/= '[') s)
        -- pldrs' = convertPrologVars pldrs []
boxerToDRS _                     = error "infelicitous input string"

---------------------------------------------------------------------------
-- | Replaces all lambda-variables in a 'PrologDRS' by lambda-identifiers.
---------------------------------------------------------------------------
replaceLambdas :: PrologDRS -> Int -> PrologDRS
replaceLambdas [] _  = []
replaceLambdas s i 
  | drsType == "lam" = replaceLambdas (replace (tail $ dropWhile (/= ',') drs) (takeWhile  (/= ',') (tail drs)) i) (i + 1)
  | otherwise        = head s : replaceLambdas (tail s) i
  where drsType = takeWhile (/= '(') s
        drs     = dropWhile (/= '(') s
        replace :: PrologDRS -> String -> Int -> PrologDRS
        replace [] _ _                                    = []
        replace d@(h:t) l j
          | init lv == l && isPunctuation (last lv) = "lambda(" ++ l ++ ":" ++ show i ++ ")" ++ replace (drop (length l) d) l j
          | otherwise                               = h : replace t l j
          where lv = take (length l + 1) d

---------------------------------------------------------------------------
-- | Converts all Prolog Variables into new Variables.
---------------------------------------------------------------------------
convertPrologVars :: PrologDRS -> [(String,String)] -> PrologDRS
convertPrologVars [] _ = []
convertPrologVars s@(h:t) cl
  | h == '_'  = newvar ++ convertPrologVars (drop (length var + 1) s) newcl
  | otherwise = h : convertPrologVars t cl
  where var            = takeWhile (not . isPunctuation) t
        (newvar,newcl) = convert (take (length var + 2) s) cl cl
        convert :: String -> [(String,String)] -> [(String,String)] -> (String,[(String,String)])
        convert v [] ocl
          | last v == ':' = (np, (init v,np) : ocl) -- for projection variables
          | otherwise     = (nr, (init v,nr) : ocl)
          where np        = show (1 + maximum (0 : map (\i -> read i :: Int) ops))
                nr        = 'x' : show (1 + maximum (0 : map (\i -> read i :: Int) suffixes))
                suffixes  = filter (not . null) (map (reverse . takeWhile isNumber. reverse) ors)
                (ops,ors) = partition (all isNumber) (map snd ocl)
        convert v (n:ns) ocl
          | init v == fst n = (snd n,ocl)
          | otherwise       = convert v ns ocl

---------------------------------------------------------------------------
-- * Private
---------------------------------------------------------------------------

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
  | drsType == "app"    = LambdaDRS ((takeWhile (/= ':') appl,[last sd]), read (tail (dropWhile (/= ':') (init appl))) :: Int)
  | drsType == "sdrs"   = plSDRSToDRS (tail drs)
  | otherwise           = error ("not a valid DRS: " ++ drsType)
  where drsType = (reverse . takeWhile isAlpha . reverse . takeWhile (/= '(')) s
        drs     = dropOuterBrackets $ takeUpToMatchingBracket Parentheses (dropWhile (/= '(') s)
        drs'    = tail (dropUpToMatchingBracket Parentheses (dropWhile (/= '(') drs))
        appl    = tail (dropWhile (/= '(') (head sd))
        sd      = splitOn ',' drs

---------------------------------------------------------------------------
-- | Converts a 'PrologDRS' of type sdrs into a 'DRS'.
-- 
-- XXX SDRSs are currently translated to DRSs with same accessibility
-- and spacial properties as SDRSs:
-- 
-- * coordinated relation  -> Merge
--
-- * subordinated relation -> Embedded propositional condition
---------------------------------------------------------------------------
plSDRSToDRS :: String -> DRS
plSDRSToDRS k
    | (sdrsType == "lab") && head (postBrackets k) == ',' = segToDRS k         -- last coordinated SDRS
    |  sdrsType == "lab" = Merge (segToDRS k) (plSDRSToDRS (postBrackets k))   -- coordinated SDRS relation
    |  sdrsType == "sub" = Merge k1 (DRS subUniverse (subCons ++ subRelation)) -- subordinated SDRS relation
    | otherwise          = error "not a valid SDRS"
    where sdrsType      = takeWhile (/= '(') k
          inBrackets    = dropOuterBrackets . takeUpToMatchingBracket Parentheses . dropWhile (/= '(')
          postBrackets  = tail . dropUpToMatchingBracket Parentheses . dropWhile (/= '(')
          k1@(DRS u1 _) = segToDRS k
          segToDRS      = plDRSToDRS . tail . dropWhile (/= ',') . inBrackets
          subUniverse   = map (\(Prop pr _) -> pr) subCons 
          subCons       = [Prop ((toDRSRef . takeWhile (/= ',') . inBrackets) s) (segToDRS s)]
              where s = postBrackets (inBrackets k)
          subRelation   = [Rel (findRel (dropWhile (/= ':') (postBrackets k))) relRefs]
              where findRel :: String -> DRSRel
                    findRel (':':'r':'e':'l':rel)
                        | toDRSRef (r !! 1) == head subUniverse = DRSRel (last r)
                        | otherwise                             = findRel (dropWhile (/= ':') rel)
                        where r = splitOn ',' (inBrackets rel)
                    findRel _ = DRSRel "subordinated"
                    relRefs = [DRSRef e | DRSRef e <- u1, head e == 'e'] ++ subUniverse

---------------------------------------------------------------------------
-- | Converts a 'String' with Prolog referents into a set of 'DRSRef's.
---------------------------------------------------------------------------
parsePlRefs :: String -> [DRSRef]
parsePlRefs [] = []
parsePlRefs s@(b:_)
  | b == '['  = map (toDRSRef . strip) (splitOn ',' (dropOuterBrackets $ takeUpToMatchingBracket Square s))
  | otherwise = error "infelicitous input string"
  where strip :: String -> String
        strip []        = []
        strip r@('[':_) = strip (dropUpToMatchingBracket Square r)
        strip (':':d)   = d
        strip (_:_)     = error "infelicitous input string"

---------------------------------------------------------------------------
-- | Converts a 'String' with Prolog conditions into a set of 'DRSCon's.
---------------------------------------------------------------------------
parsePlCons :: String -> [DRSCon]
parsePlCons [] = []
parsePlCons s@(b:_)
  | b == '['  = parse (dropOuterBrackets $ takeUpToMatchingBracket Square s)
  | otherwise = error "infelicitous input string"
  where parse :: String -> [DRSCon]
        parse [] = []
        parse (',':cs)   = parse cs
        parse cs
          | pfx == "not"    = Neg     (plDRSToDRS c)                                                        : etc
          | pfx == "imp"    = Imp     (plDRSToDRS c) (plDRSToDRS c')                                        : etc
          | pfx == "or"     = Or      (plDRSToDRS c) (plDRSToDRS c')                                        : etc
          | pfx == "pos"    = Diamond (plDRSToDRS c)                                                        : etc
          | pfx == "nec"    = Box     (plDRSToDRS c)                                                        : etc
          | pfx == "prop"   = Prop    (toDRSRef (takeWhile (/= ',') c)) (plDRSToDRS (dropWhile (/= ',') c)) : etc
          | pfx == "pred"   = Rel     (DRSRel (ct !! 1))                [toDRSRef (head ct)]                : etc
          | pfx == "rel"    = Rel     (DRSRel (ct !! 2))                (map toDRSRef (take 2 ct))          : etc
          | pfx == "role"   = Rel     (DRSRel (capitalize (ct !! 2)))   (map toDRSRef (take 2 ct))          : etc
          | pfx == "named"  = Rel     (DRSRel (capitalize (ct !! 1)))   [toDRSRef (head ct)]                : etc
          | pfx == "timex"  = Rel     (DRSRel (ct !! 1))                [toDRSRef (head ct)]                : etc
          | pfx == "card"   = Rel     (DRSRel ((ct !! 2) ++ (ct !! 1))) [toDRSRef (head ct)]                : etc
          | pfx == "eq"     = Rel     (DRSRel "=")                      (map toDRSRef ct)                   : etc
          | pfx == "duplex" = Rel     (DRSRel (head ct))                [toDRSRef (takeWhile (/= ',') c'),dref] 
                            : Prop    dref (DRS [] [Imp (plDRSToDRS d1) (plDRSToDRS d2)])                   : etc
          | otherwise      = error ("not a valid condition: " ++ pfx)
          where pfx = (reverse . takeWhile (/= ':'). reverse . takeWhile (/= '(')) cs
                c   = dropOuterBrackets $ takeUpToMatchingBracket Parentheses (dropWhile (/= '(') cs) 
                etc = parse ((drop (length c + 2) . dropWhile (/= '(')) cs)
                c'  = tail $ dropUpToMatchingBracket Parentheses (dropWhile (/= '(') c)
                ct  = splitOn ',' c
                capitalize :: String -> String
                capitalize []    = []
                capitalize (h:t) = toUpper h:t
                --tokid
                --  | tokid' == "" = []
                --  | otherwise    = [DRSRef tokid']
                --  where tokid' = (dropOuterBrackets . takeUpToMatchingBracket Square . dropWhile (/= '[')) cs
                dref = toDRSRef (takeWhile (/= ':') d1)
                d1  = tail $ dropWhile (/= ',') c
                d2  = tail $ dropWhile (/= ',') c'

---------------------------------------------------------------------------
-- | Converts a 'String' to a 'DRSRef', which may be a 'LambdaDRSRef'.
---------------------------------------------------------------------------
toDRSRef :: String -> DRSRef
toDRSRef r
  | "lambda(" `isPrefixOf` r = LambdaDRSRef ((takeWhile (/= ':') (drop 7 r),[]),read (dropWhile (/= ':') r) :: Int)
  | otherwise                = DRSRef r

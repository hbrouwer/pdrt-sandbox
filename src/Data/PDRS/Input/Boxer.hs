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

import Data.Char (isAlpha, isNumber, toUpper)
import Data.List (isPrefixOf, nub, union)
import Data.DRS.Input.Boxer
import Data.DRS.Input.String
import Data.PDRS.DataType

---------------------------------------------------------------------------
-- * Exported
---------------------------------------------------------------------------

---------------------------------------------------------------------------
-- | Converts Boxer's output into a 'PDRS'.
---------------------------------------------------------------------------
boxerToPDRS :: String -> PDRS
boxerToPDRS s@('s':'e':'m':'(':_) = bindPRefs (plPDRSToPDRS (replaceLambdas plpdrs 0)) []
    where plpdrs = tail $ dropUpToMatchingBracket Square (dropWhile (/= '[') s)
          --plpdrs' = convertPrologVars plpdrs []
boxerToPDRS _                     = error "infelicitous input string"

---------------------------------------------------------------------------
-- * Private
---------------------------------------------------------------------------

---------------------------------------------------------------------------
-- | Converts a 'PrologDRS' into a 'PDRS'.
---------------------------------------------------------------------------
plPDRSToPDRS :: PrologDRS -> PDRS
plPDRSToPDRS s
  | pdrsType == "drs"    = PDRS plLabel [] plPRefs plPCons
  | pdrsType == "merge"  = AMerge (plPDRSToPDRS pdrs) (plPDRSToPDRS pdrs')
  | pdrsType == "smerge" = AMerge (plPDRSToPDRS pdrs) (plPDRSToPDRS pdrs')
  | pdrsType == "alfa"   = PMerge (plPDRSToPDRS (tail (dropWhile (/= ',') pdrs))) (plPDRSToPDRS pdrs')
  | pdrsType == "lambda" = LambdaPDRS ((takeWhile (/= ':') pdrs,[]),        read (dropWhile (/= ':') pdrs) :: Int)
  | pdrsType == "app"    = LambdaPDRS ((takeWhile (/= ':') appl,[last sd]), read (tail (dropWhile (/= ':') (init appl))) :: Int)
  | pdrsType == "sdrs"   = plSDRSToPDRS (tail pdrs)
  | otherwise            = error ("not a valid PDRS" ++ pdrsType)
  where pdrsType = (reverse . takeWhile isAlpha . reverse . takeWhile (/= '(')) s
        pdrs     = dropOuterBrackets $ takeUpToMatchingBracket Parentheses (dropWhile (/= '(') s)
        pdrs'    = tail (dropUpToMatchingBracket Parentheses (dropWhile (/= '(') pdrs))
        plLabel  = read ((filter isNumber . takeWhile (/= ':')) s) :: Int
        plPRefs  = parsePlRefs pdrs
        plPCons  = parsePlCons (tail (dropUpToMatchingBracket Square pdrs))
        appl     = tail (dropWhile (/= '(') (head sd))
        sd       = splitOn ',' pdrs

---------------------------------------------------------------------------
-- | Converts a 'PrologDRS' of type sdrs into a 'PDRS'.
-- 
-- XXX SDRSs are currently translated to PDRSs with same accessibility
-- and spacial properties as SDRSs:
-- 
-- * coordinated relation  -> AMerge
--
-- * subordinated relation -> Propositional conditions + MAP-constraint
---------------------------------------------------------------------------
plSDRSToPDRS :: String -> PDRS
plSDRSToPDRS k
    | (sdrsType == "lab") && head (postBrackets k) == ',' = segToPDRS k           -- last coordinated SDRS
    |  sdrsType == "lab" = AMerge (segToPDRS k) (plSDRSToPDRS (postBrackets k))   -- coordinated SDRS relation
    |  sdrsType == "sub" = PDRS subLab subMAPs subPRefs (subPCons ++ subRelation) -- subordinated SDRS relation
    | otherwise          = error "not a valid SDRS"
    where sdrsType     = takeWhile (/= '(') k
          inBrackets   = dropOuterBrackets . takeUpToMatchingBracket Parentheses . dropWhile (/= '(')
          postBrackets = tail . dropUpToMatchingBracket Parentheses . dropWhile (/= '(')
          segToPDRS    = plPDRSToPDRS . tail . dropWhile (/= ',') . inBrackets
          subLab       = read (show m1 ++ show m0) :: PVar
              where (m0,m1) = head subMAPs
          subMAPs      = [(snd (subPCTuples !! 1), snd (head subPCTuples))]
          subPRefs     = map (PRef subLab . fst) subPCTuples
          subPCTuples  = map propToTuples subPCons
              where propToTuples :: PCon -> (PDRSRef,PVar)
                    propToTuples (PCon _ (Prop r (PDRS l _ _ _)))            = (r,l)
                    propToTuples (PCon _ (Prop r (AMerge (PDRS l _ _ _) _))) = (r,l)
                    propToTuples (PCon _ (Prop r (PMerge (PDRS l _ _ _) _))) = (r,l)
                    propToTuples _                                           = error "not a valid SDRS segment"
          subPCons     = [toProp (inBrackets k), toProp (postBrackets (inBrackets k))]
              where toProp :: String -> PCon
                    toProp s = PCon subLab (Prop ((toPDRSRef . takeWhile (/= ',') . inBrackets) s) (segToPDRS s))
          subRelation  = [PCon subLab (Rel (findRel (dropWhile (/= ':') (postBrackets k))) rs)]
              where rs = map fst subPCTuples
                    findRel :: String -> PDRSRel
                    findRel (':':'r':'e':'l':rel)
                        | map toPDRSRef (init r) == rs = PDRSRel (last r)
                        | otherwise                    = findRel (dropWhile (/= ':') rel)
                        where r = splitOn ',' (inBrackets rel)
                    findRel _                          = PDRSRel "subordinated"

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
          | pfx == "not"    = PCon lab (Neg     (plPDRSToPDRS c))                                                         : etc
          | pfx == "imp"    = PCon lab (Imp     (plPDRSToPDRS c) (plPDRSToPDRS c'))                                       : etc
          | pfx == "or"     = PCon lab (Or      (plPDRSToPDRS c) (plPDRSToPDRS c'))                                       : etc
          | pfx == "pos"    = PCon lab (Diamond (plPDRSToPDRS c))                                                         : etc
          | pfx == "nec"    = PCon lab (Box     (plPDRSToPDRS c))                                                         : etc
          | pfx == "prop"   = PCon lab (Prop    (toPDRSRef (takeWhile (/= ',') c)) (plPDRSToPDRS (dropWhile (/= ',') c))) : etc
          | pfx == "pred"   = PCon lab (Rel     (PDRSRel (ct !! 1))                [toPDRSRef (head ct)])                 : etc
          | pfx == "rel"    = PCon lab (Rel     (PDRSRel (ct !! 2))                (map toPDRSRef (take 2 ct)))           : etc
          | pfx == "role"   = PCon lab (Rel     (PDRSRel (capitalize (ct !! 2)))   (map toPDRSRef (take 2 ct)))           : etc
          | pfx == "named"  = PCon lab (Rel     (PDRSRel (capitalize (ct !! 1)))   [toPDRSRef (head ct)])                 : etc
          | pfx == "timex"  = PCon lab (Rel     (PDRSRel (ct !! 1))                [toPDRSRef (head ct)])                 : etc
          | pfx == "card"   = PCon lab (Rel     (PDRSRel ((ct !! 2) ++ (ct !! 1))) [toPDRSRef (head ct)])                 : etc
          | pfx == "eq"     = PCon lab (Rel     (PDRSRel "=")                      (map toPDRSRef ct))                    : etc
          | pfx == "duplex" = PCon lab (Rel     (PDRSRel (head ct))                [toPDRSRef (takeWhile (/= ',') c'),dr])
                            : PCon lab (Prop    dr (PDRS nl [] [] [PCon nl (Imp (plPDRSToPDRS dp1) (plPDRSToPDRS dp2))])) : etc
          | otherwise       = error ("not a valid condition " ++ pfx)
          where pfx = (reverse . takeWhile (/= ':'). reverse . takeWhile (/= '(')) cs
                lab = read ((filter isNumber . takeWhile (/= ':')) cs) :: Int
                c   = dropOuterBrackets $ takeUpToMatchingBracket Parentheses (dropWhile (/= '(') cs)
                c'  = tail $ dropUpToMatchingBracket Parentheses (dropWhile (/= '(') c)
                etc = parse ((drop (length c + 2) . dropWhile (/= '(')) cs)
                ct  = splitOn ',' c
                capitalize :: String -> String
                capitalize []    = []
                capitalize (h:t) = toUpper h:t
                --tokid
                --  | tokid' == "" = []
                --  | otherwise    = [toPDRSRef tokid']
                --  where tokid' = (dropOuterBrackets . takeUpToMatchingBracket Square . dropWhile (/= '[')) cs
                -- ^ For duplex conditions
                dr  = toPDRSRef (takeWhile (/= ':') dp1)
                dp1 = tail $ dropWhile (/= ',') c
                dp2 = tail $ dropWhile (/= ',') c'
                nl  = read (filter isNumber (takeWhile (/= ':') dp1 ++ takeWhile (/= ':') dp2)) :: Int

---------------------------------------------------------------------------
-- | Converts a 'String' to a 'PDRSRef', which may be a 'LambdaPDRSRef'.
---------------------------------------------------------------------------
toPDRSRef :: String -> PDRSRef
toPDRSRef r
  | "lambda(" `isPrefixOf` r = LambdaPDRSRef ((takeWhile (/= ':') (drop 7 r),[]),read (dropWhile (/= ':') r) :: Int)
  | otherwise                = PDRSRef r

---------------------------------------------------------------------------
-- | Makes sure PDRS derived from Boxer does not contain free PRefs by
-- adding MAPs where necessary.
-- | XXX this function assumes that Boxer is right!
---------------------------------------------------------------------------
bindPRefs :: PDRS -> [PRef] -> PDRS
bindPRefs lp@(LambdaPDRS _)   _      = lp
bindPRefs (AMerge p1 p2) universes = AMerge (bindPRefs p1 universes) (bindPRefs p2 universes)
bindPRefs (PMerge p1 p2) universes = PMerge (bindPRefs p1 universes) (bindPRefs p2 universes)
bindPRefs (PDRS l m u c) universes = PDRS l (nub $ filter (uncurry (/=)) m') u c'
  where m'       = m ++ map (\(PRef p _) -> (l,p)) u ++ map (\(PCon p _) -> (l,p)) c ++ m''
        (c',m'') = bindPRefsPCons c (u `union` universes)
        bindPRefsPCons :: [PCon] -> [PRef]-> ([PCon],[MAP])
        bindPRefsPCons [] _                       = ([],[])
        bindPRefsPCons [pc@(PCon p (Rel _ r))] us = ([pc],map (verifyBinding us . PRef p) r)
        bindPRefsPCons [PCon p (Neg k1)]       us = ([PCon p (Neg     (bindPRefs k1 us))],[])
        bindPRefsPCons [PCon p (Imp k1 k2)]    us = ([PCon p (Imp     (bindPRefs k1 us) (bindPRefs k2 (getU k1 `union` us)))],[])
        bindPRefsPCons [PCon p (Or k1 k2)]     us = ([PCon p (Or      (bindPRefs k1 us) (bindPRefs k2 us))],[])
        bindPRefsPCons [PCon p (Prop r k1)]    us = ([PCon p (Prop r  (bindPRefs k1 us))],[verifyBinding us (PRef p r)])
        bindPRefsPCons [PCon p (Diamond k1)]   us = ([PCon p (Diamond (bindPRefs k1 us))],[])
        bindPRefsPCons [PCon p (Box k1)]       us = ([PCon p (Box     (bindPRefs k1 us))],[])
        bindPRefsPCons (pc:pcns)               us = (c1 ++ c2, m1 ++ m2)
          where (c1,m1) = bindPRefsPCons [pc] us
                (c2,m2) = bindPRefsPCons pcns us
        verifyBinding :: [PRef] -> PRef -> MAP
        verifyBinding [] (PRef p _) = (p,p)
        verifyBinding (PRef p r:prs) pref@(PRef p' r')
          | r == r' && p /= p'  = (p',p)
          | otherwise           = verifyBinding prs pref
        getU :: PDRS -> [PRef]
        getU (LambdaPDRS _)   = []
        getU (AMerge mp1 mp2) = getU mp1 `union` getU mp2
        getU (PMerge mp1 mp2) = getU mp1 `union` getU mp2
        getU (PDRS _ _ d _)   = d

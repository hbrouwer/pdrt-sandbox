-- This is a tutorial for creating and manipulating PDRSs with PDRT-SANDBOX.

import Data.PDRS

--------------------------------------------------------------------------------
-- * Creating a PDRS
--------------------------------------------------------------------------------

--------------------------------------------------------------------------------
-- | A Projected Discourse Representation Structure (PDRS) consists of a PDRS
-- label and three sets: a set of MAPs, a set of projected discourse
-- referents and a set of projected conditions. The first example shows an
-- empty PDRS. The second example shows a PDRS containing one (non-projected)
-- referent and a two simple (non-projected) conditions.  Just like in DRT,
-- predicates and relations are always referred to as 'Rel', independent of
-- their arity.  
--
-- Pointers of referents and conditions can indicate projection, and the set
-- of MAPs can indicate constraints on projection: (1,2) means that 2 is an
-- accessible context from 1, i.e., context 1 is weakly subordinate to 2 ("1
-- ≤ 2"). Equivalence between two contexts ("1 = 2") can be represented by
-- introducing a reciprocal accessibility relation: (1,2) and (2,1).
-- Finally, strict subordination between contexts ("1 < 2") can be
-- represented by introducing a negative edge from 2 to 1: (2,-1) (negative
-- pointers are used to represent negative edges).
--
--------------------------------------------------------------------------------

-- | empty PDRS (labelled 1)
examplePDRS1 = PDRS 1 [] [] []

-- | "A man is happy."
examplePDRS2a = PDRS 1 [] [PRef 1 (PDRSRef "x")] 
                  [PCon 1 (Rel (PDRSRel "man") [PDRSRef "x"])
                  ,PCon 1 (Rel (PDRSRel "happy") [PDRSRef "x"])]

-- | "The man is happy."
examplePDRS2b = PDRS 1 [(1,2)] [PRef 2 (PDRSRef "x")] 
                  [PCon 2 (Rel (PDRSRel "man") [PDRSRef "x"])
                  ,PCon 1 (Rel (PDRSRel "happy") [PDRSRef "x"])]

-- | "The man is happy."
examplePDRS2c = PDRS 1 [(2,-1)] [PRef 2 (PDRSRef "x")] 
                  [PCon 2 (Rel (PDRSRel "man") [PDRSRef "x"])
                  ,PCon 1 (Rel (PDRSRel "happy") [PDRSRef "x"])]

--------------------------------------------------------------------------------
-- | A 'Rel' condition takes two arguments: the name of the
-- predicate/relation, and a set of PDRS referents. There are six other
-- conditions, called complex conditions, all of which take one or more PDRSs
-- as arguments:
--
-- * unary complex conditions: negation ('Neg'), modal possibility
--   ('Diamond'), modal necessity ('Box');
--
-- * binary complex conditions: implication ('Imp') and disjunction ('Or');
--
-- * mixed complex condition: propositional condition ('Prop').
--
-- Below we show an example from each of these.
--------------------------------------------------------------------------------

-- | "It's not the case that a woman is happy."
examplePDRS3a = PDRS 1 [] [] 
                  [PCon 1 (Neg (PDRS 2 [] [PRef 2 (PDRSRef "y")]
                    [PCon 2 (Rel (PDRSRel "woman") [PDRSRef "y"])
                    ,PCon 2 (Rel (PDRSRel "happy") [PDRSRef "y"])]))]

-- | "It's not the case that the woman is happy."
examplePDRS3b = PDRS 1 [] [] 
                  [PCon 1 (Neg (PDRS 2 [(2,3)] [PRef 3 (PDRSRef "y")]
                    [PCon 3 (Rel (PDRSRel "woman") [PDRSRef "y"])
                    ,PCon 2 (Rel (PDRSRel "happy") [PDRSRef "y"])]))]

-- | "Maybe John is not sad." 
examplePDRS3c = (PDRS 1 [] [] 
                    [PCon 1 (Diamond (PDRS 2 [] [] 
                     [PCon 2 (Neg (PDRS 3 [(3,4)] [PRef 4 (PDRSRef "x")] 
                      [PCon 4 (Rel (PDRSRel "John") [PDRSRef "x"])
                      ,PCon 3 (Rel (PDRSRel "sad") [PDRSRef "x"])]))]))])

-- | "If a farmer owns a donkey, he feeds it."
examplePDRS4 = PDRS 1 [] []
                  [PCon 1 (Imp 
                    (PDRS 2 [] [PRef 2 (PDRSRef "x"),PRef 2 (PDRSRef "y")]
                      [PCon 2 (Rel (PDRSRel "farmer") [PDRSRef "x"])
                      ,PCon 2 (Rel (PDRSRel "donkey") [PDRSRef "y"])
                      ,PCon 2 (Rel (PDRSRel "owns") [PDRSRef "x",PDRSRef "y"])])
                    (PDRS 3 [] [] 
                      [PCon 3 (Rel (PDRSRel "feeds") [PDRSRef "x",PDRSRef "y"])]))]

-- | "A man believes he loves a woman."
examplePDRS5 = PDRS 1 [] [PRef 1 (PDRSRef "x"),PRef 1 (PDRSRef "p")]
                  [PCon 1 (Rel (PDRSRel "man") [PDRSRef "x"])
                  ,PCon 1 (Rel (PDRSRel "believes") [PDRSRef "x",PDRSRef "p"])
                  ,PCon 1 (Prop (PDRSRef "p") 
                    (PDRS 2 [(2,3)] [PRef 3 (PDRSRef "y")]
                      [PCon 3 (Rel (PDRSRel "woman") [PDRSRef "x"])
                      ,PCon 2 (Rel (PDRSRel "loves") [PDRSRef "x",PDRSRef "y"])]))]

--------------------------------------------------------------------------------
-- | Besides directly defining a PDRS using the PDRS syntax, it is also
-- possible to use a set-theoretical string input format directly.
--
-- The following names can be used for different operators (these are all
-- case insensitive):
-- 
-- * Negation operators: !, not, neg
-- * Implication operators (infix): imp, ->, =>, then
-- * Disjuction operators (infix): v, or
-- * Box operators: b, box, necessary
-- * Diamond operators: d, diamond, maybe.
--------------------------------------------------------------------------------

-- | "The man is not happy."
examplePDRS6 = stringToPDRS "<1,{},{ (1,not <5,{(2,x)},{(2,man(x)),(5,happy(x))},{(5,2)}>) },{}>"

--------------------------------------------------------------------------------
-- | The default format for showing PDRSs is the Boxes output format.
-- However, in PDRT-SANDBOX different output formats can be used:
--
-- * Box-representations (default): 'Boxes'
-- * Linear notation: 'Linear'
-- * Set-theoretic notation: 'Set'
-- * PDRT-SANDBOX syntax output: 'Debug'
--------------------------------------------------------------------------------

examplePDRS7a = Boxes examplePDRS4
examplePDRS7b = Linear examplePDRS4
examplePDRS7c = Set examplePDRS4
examplePDRS7d = Debug examplePDRS4

--------------------------------------------------------------------------------
-- * Combining PDRSs
--------------------------------------------------------------------------------

--------------------------------------------------------------------------------
-- | Using the PDRS syntax defined above, we can now combine two PDRSs with
-- the one of the two merge operations: /assertive merge/ between PDRS p1 and
-- p2 results in a PDRS in which all asserted content of p1 (and p2) remains
-- asserted (i.e., pointers are bound locally). On the other hand,
-- a /projective merge/ between p1 and p2 results in a PDRS in which all
-- asserted content from p1 becomes projected (via the weak subordination
-- constraint). 
-- 
-- Just like in DRT, asserted and projected merge can be realized via
-- a constructor ('AMerge' and 'PMerge'), the merge operator ('pdrsAMerge'
-- and 'pdrsPMerge'), or the infix merge operator ('<<+>>' and '<<*>>').
-- Finally, it is also possible to visualize the entire merge equation
-- (using 'printAMerge' and 'printPMerge').
--------------------------------------------------------------------------------

-- | "The man is happy and it's not the case that the woman is happy."
examplePDRSMerge1a = pdrsResolveMerges $ AMerge examplePDRS2b examplePDRS3b

examplePDRSMerge1b = pdrsResolveMerges $ PMerge 
                      (PDRS 1 [] [PRef 1 (PDRSRef "x")] 
                        [PCon 1 (Rel (PDRSRel "man") [PDRSRef "x"])])
                      (PDRS 1 [] []
                        [PCon 1 (Rel (PDRSRel "happy") [PDRSRef "x"])])

-- | "A man is happy."
examplePDRSMerge2a = pdrsAMerge man happy  
examplePDRSMerge2b = man <<+>> happy
examplePDRSMerge2c = printAMerge man happy

-- | "The man is happy."
examplePDRSMerge3a = pdrsPMerge man happy
examplePDRSMerge3b = man <<*>> happy
examplePDRSMerge3c = printPMerge man happy

man   = PDRS 1 [] [PRef 1 (PDRSRef "x")] 
          [PCon 1 (Rel (PDRSRel "man") [PDRSRef "x"])]
happy = PDRS 1 [] [] [PCon 1 (Rel (PDRSRel "happy") [PDRSRef "x"])]

--------------------------------------------------------------------------------
-- | Unresolved structures can simply be defined as Haskell functions.
-- Unresolved PDRSs can be combined by means of function
-- application. This can be done directly, or via one of the available
-- functions for showing the complete equation for Lambda-resolution
-- ('printPDRSRefBetaReduct' and 'printPDRSBetaReduct').
--------------------------------------------------------------------------------

-- | λx.happy(x)
examplePDRSLambda1 x = PDRS 1 [] [] [PCon 1 (Rel (PDRSRel "happy") [x])]

-- | λx.happy(x) ("harm") = happy(harm)
examplePDRSLambda1a = examplePDRSLambda1 (PDRSRef "harm")
examplePDRSLambda1b = printPDRSRefBetaReduct examplePDRSLambda1 (PDRSRef "harm")
examplePDRSLambda1c = pdrsResolveMerges $ PMerge 
                        (PDRS 1 [] [PRef 1 (PDRSRef "x")] 
                          [PCon 1 (Rel (PDRSRel "Harm") [PDRSRef "x"])]) 
                        (examplePDRSLambda1 (PDRSRef "x"))

-- | λK.Ǝx(man(x) ∧ happy(x) ∧ K)
examplePDRSLambda2 k = pdrsAMerge (PDRS 4 [] [PRef 4 (PDRSRef "x")]
                        [PCon 4 (Rel (PDRSRel "man") [PDRSRef "x"])
                        ,PCon 4 (Rel (PDRSRel "happy") [PDRSRef "x"])])
                        (k)

-- | λK.Ǝx(man(x) ∧ happy(x) ∧ K) (Ǝy woman(y) ∧ ¬happy(y))) 
--    = Ǝx(man(x) ∧ happy(x) ∧ Ǝy(woman(y) ∧ ¬happy(y)))
examplePDRSLambda2a = examplePDRSLambda2 examplePDRS3a
examplePDRSLambda2b = printPDRSBetaReduct examplePDRSLambda2 examplePDRS3a

-- | λP.Ǝx(man(x) ∧ P(x))
examplePDRSLambda3 p = AMerge 
                        (PDRS 1 [] [PRef 1 (PDRSRef "x")] 
                          [PCon 1 (Rel (PDRSRel "man") [PDRSRef "x"])])
                        (p (PDRSRef "x"))

-- | λP.Ǝx(man(x) ∧ P(x)) (λx.happy(x)) = Ǝx(man(x) ∧ happy(x))
examplePDRSLambda3a = pdrsResolveMerges $ examplePDRSLambda3 examplePDRSLambda1

--------------------------------------------------------------------------------
-- * Translations
--------------------------------------------------------------------------------

--------------------------------------------------------------------------------
-- | Each (resolved) PDRS can be translated into a DRS or a First Order Logic
-- formula. Translation into a DRS here implies that all projected content is
-- accommodated to the highest possible context. The FOL formulas will always
-- be quantified relative to a world 'w', in order to account for the modal
-- operators.
--------------------------------------------------------------------------------

examplePDRStoDRS = pdrsToDRS examplePDRS3c
examplePDRStoFOL = pdrsToFOL examplePDRS3c

--------------------------------------------------------------------------------
-- | PDRSs can also be translated into a projection table (a 'PTable').
-- A PTable contains the same information as a PDRS, but has the advantage of
-- explicitly separating information about content and form, and providing
-- a /flat/ (i.e., non-recursive) representation.
--------------------------------------------------------------------------------

examplePDRStoPTable = pdrsToPTable examplePDRS3c

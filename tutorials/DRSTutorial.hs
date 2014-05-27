-- This is a tutorial for creating and manipulating DRSs with PDRT-SANDBOX.

import Data.DRS

--------------------------------------------------------------------------------
-- * Creating a DRS
--------------------------------------------------------------------------------

--------------------------------------------------------------------------------
-- | A Discourse Representation Structure (DRS) consists of two sets: the
-- first set contains the DRS referents, and the second set contains the DRS
-- conditions.  The first example shows an empty DRS. The second example
-- shows a DRS containing one referent and a two simple conditions (the
-- predicate "man", and the predicate "happy").  Independent of their arity,
-- predicates and relations are always referred to as 'Rel'.
--------------------------------------------------------------------------------

-- | empty DRS
exampleDRS1 = DRS [] []

-- | "A man is happy."
exampleDRS2 = DRS [DRSRef "x"] 
                  [Rel (DRSRel "man") [DRSRef "x"]
                  ,Rel (DRSRel "happy") [DRSRef "x"]]

--------------------------------------------------------------------------------
-- | A 'Rel' condition takes two arguments: the name of the
-- predicate/relation, and a set of DRS referents. There are six other
-- conditions, called complex conditions, all of which take one or more DRSs
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

-- | "A man is not happy."
exampleDRS3 = DRS [DRSRef "x"] 
                  [Rel (DRSRel "man") [DRSRef "x"]
                  ,Neg (DRS [] [Rel (DRSRel "happy") [DRSRef "x"]])]

-- | "If a farmer owns a donkey, he feeds it."
exampleDRS4 = DRS []
                  [Imp 
                    (DRS [DRSRef "x",DRSRef "y"]
                         [Rel (DRSRel "farmer") [DRSRef "x"]
                         ,Rel (DRSRel "donkey") [DRSRef "y"]
                         ,Rel (DRSRel "owns") [DRSRef "x",DRSRef "y"]])
                    (DRS [] [Rel (DRSRel "feeds") [DRSRef "x",DRSRef "y"]])]

-- | "A man believes he loves a woman."
exampleDRS5 = DRS [DRSRef "x",DRSRef "y",DRSRef "p"]
                  [Rel (DRSRel "man") [DRSRef "x"]
                  ,Rel (DRSRel "woman") [DRSRef "y"]
                  ,Rel (DRSRel "believes") [DRSRef "x",DRSRef "p"]
                  ,Prop (DRSRef "p") (DRS []
                      [Rel (DRSRel "loves") [DRSRef "x",DRSRef "y"]])]

--------------------------------------------------------------------------------
-- | Besides directly defining a DRS using the DRS syntax, it is also
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

-- | "A man is happy and not sad."
exampleDRS6 = stringToDRS "<{x },  {man(x), happy(x), not <{},{sad(x)}> }>"

--------------------------------------------------------------------------------
-- * Showing DRSs
--------------------------------------------------------------------------------

--------------------------------------------------------------------------------
-- | The default format for showing DRSs is the Boxes output format.
-- However, in PDRT-SANDBOX different output formats can be used:
--
-- * Box-representations (default): 'Boxes'
-- * Linear notation: 'Linear'
-- * Set-theoretic notation: 'Set'
-- * PDRT-SANDBOX syntax output: 'Debug'
--------------------------------------------------------------------------------

exampleDRS7a = Boxes exampleDRS4
exampleDRS7b = Linear exampleDRS4
exampleDRS7c = Set exampleDRS4
exampleDRS7d = Debug exampleDRS4

--------------------------------------------------------------------------------
-- * Combining DRSs
--------------------------------------------------------------------------------

--------------------------------------------------------------------------------
-- | Using the DRS syntax defined above, we can now combine two DRSs with
-- the merge operation, using the 'Merge' constructor, the merge operator
-- ('drsMerge'), or the infix merge operator ('<<+>>'). Finally, it is also
-- possible to visualize the entire merge equation (using 'printMerge').
--------------------------------------------------------------------------------

-- | "A man is happy and a man is not happy."
exampleDRSMerge1 = drsResolveMerges $ Merge exampleDRS2 exampleDRS3

-- | "A man is not happy. He is sad."
exampleDRSMerge2a = drsMerge exampleDRS3   (DRS [] [Rel (DRSRel "sad") [DRSRef "x"]])
exampleDRSMerge2b = exampleDRS3 <<+>>      (DRS [] [Rel (DRSRel "sad") [DRSRef "x"]])
exampleDRSMerge2c = printMerge exampleDRS3 (DRS [] [Rel (DRSRel "sad") [DRSRef "x"]])

--------------------------------------------------------------------------------
-- | Unresolved structures can simply be defined as Haskell functions.
-- Unresolved DRSs can be combined by means of function application. This can
-- be done directly, or via one of the available functions for showing the
-- complete equation for Lambda-resolution ('printDRSRefBetaReduct' and
-- 'printDRSBetaReduct').
--------------------------------------------------------------------------------

-- | λx.happy(x)
exampleDRSLambda1 x = DRS [] [Rel (DRSRel "happy") [x]]

-- | λx.happy(x) ("harm") = happy(harm)
exampleDRSLambda1a = exampleDRSLambda1 (DRSRef "harm")
exampleDRSLambda1b = printDRSRefBetaReduct exampleDRSLambda1 (DRSRef "harm")

-- | λK.Ǝx(man(x) ∧ happy(x) ∧ K)
exampleDRSLambda2 k = Merge (DRS [DRSRef "x"] 
                        [Rel (DRSRel "man") [DRSRef "x"]
                        ,Rel (DRSRel "happy") [DRSRef "x"]])
                        (k)

-- | λK.Ǝx(man(x) ∧ happy(x) ∧ K) (Ǝx(man(x) ∧ ¬happy(x))) 
--    = Ǝx(man(x) ∧ happy(x) ∧ Ǝx'(man(x') ∧ ¬happy(x')))
exampleDRSLambda2a = exampleDRSLambda2 exampleDRS3
exampleDRSLambda2b = printDRSBetaReduct exampleDRSLambda2 exampleDRS3

-- | λP.Ǝx(man(x) ∧ P(x))
exampleDRSLambda3 p = Merge 
                        (DRS [DRSRef "x"] [Rel (DRSRel "man") [DRSRef "x"]])
                        (p (DRSRef "x"))

-- | λP.Ǝx(man(x) ∧ P(x)) (λx.happy(x)) = Ǝx(man(x) ∧ happy(x))
exampleDRSLambda3a = exampleDRSLambda3 exampleDRSLambda1

--------------------------------------------------------------------------------
-- * Translate to FOL
--------------------------------------------------------------------------------

--------------------------------------------------------------------------------
-- | Each (resolved) DRS can be translated into a First Order Logic formula.
-- These FOL formulas will always be quantified relative to a world 'w', in
-- order to account for the modal operators.
--------------------------------------------------------------------------------

-- | "Maybe John is not happy." (NB. here, the proper name "John" is
-- described as a constant, but see the PDRT tutorial for a better
-- treatment of proper names.)
exampleDRSFOL = drsToFOL (DRS [] [Diamond (DRS [] 
                  [Neg (DRS [] [Rel (DRSRel "happy") [DRSRef "john"]])])])

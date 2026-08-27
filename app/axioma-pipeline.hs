{-# LANGUAGE DataKinds #-}
{-# LANGUAGE ScopedTypeVariables #-}

-- | Pipeline oracle for Markov-category separator tests.
--
-- This executable holds the research-stage checks that grew out of the
-- affine/linear excavation: finite-separator oracles for 'Prob', the
-- 'FinRel'/'Prob' contrast case, and the 'squareKBool' premonoidal witness.
-- Split off from 'axioma.hs' because that file had become unwieldy.
module Main where

import Circuit.Axioma.Test
  ( allBoolFns,
    approx,
    check,
    pairBoolFns,
    pairDoubleFns,
  )
import Circuit.Bimonoid (Copy (..), Discard (..))
import Circuit.Category (id, (.), (.>))
import Circuit.FinRel
import Circuit.Markov (copyNatural, deterministic, discardNatural)
import Circuit.Prob (Prob (..), choiceBy, copyP, discardP, embed, fromWeighted, parFG, parGF, score)
import Circuit.Tensor (Tensor (..))
import ProbOracles
  ( probCopySep,
    probCopySepDouble,
    probDiscardSep,
    probEqDoubleOver,
    probEqOver,
  )
import Prelude hiding (curry, id, uncurry, (.))

type N1 = FinObj 1

-- | Equality oracle with an explicit input list instead of 'Bounded'/'Enum'
-- constraints.  Useful when the input type is a pair whose 'Enum' instance is
-- not available.
probEqOver' ::
  forall a b r.
  (Eq r) =>
  [a] ->
  [b -> r] ->
  Prob (->) r a b ->
  Prob (->) r a b ->
  Bool
probEqOver' as ks (Prob p) (Prob q) =
  and
    [ p (\((), b) -> k b) ((), a) == q (\((), b) -> k b) ((), a)
    | k <- ks,
      a <- as
    ]

-- | Centrality check for the premonoidal 'Prob' base: @f@ is central when
-- the two parallel nestings agree on a supplied set of probe morphisms.
centralP ::
  (Eq r) =>
  [(a, c)] ->
  [(b, d) -> r] ->
  (Prob (->) r a b -> Prob (->) r c d -> Prob (->) r (a, c) (b, d)) ->
  (Prob (->) r a b -> Prob (->) r c d -> Prob (->) r (a, c) (b, d)) ->
  Prob (->) r a b ->
  [Prob (->) r c d] ->
  Bool
centralP inputs ks parN1 parN2 f =
  all (\g -> probEqOver' inputs ks (parN1 f g) (parN2 f g))

-- | Copy-naturality check for the premonoidal 'Prob' base, which has no
-- canonical 'Tensor' instance.  The caller supplies the nesting ('parFG' or
-- 'parGF') to test.
copyNaturalP ::
  (Prob (->) r a (b, b) -> Prob (->) r a (b, b) -> Bool) ->
  (forall c d. Prob (->) r c d -> Prob (->) r c d -> Prob (->) r (c, c) (d, d)) ->
  Prob (->) r a b ->
  Bool
copyNaturalP eq parF f = eq (copyP . f) (parF f f . copyP)

-- | Discard-naturality check for the premonoidal 'Prob' base.
discardNaturalP ::
  (Prob (->) r a () -> Prob (->) r a () -> Bool) ->
  Prob (->) r a b ->
  Bool
discardNaturalP eq f = eq (discardP . f) discardP

-- | A non-deterministic Bool kernel analogous to 'squareK' over 'Double'.
--
-- 'squareK' squares the continuation with scalar multiplication; over 'Bool'
-- that multiplication is '(/=)' (XOR) on the Boolean ring.  The kernel
-- queries the continuation at both truth values, so it is non-linear.
--
-- Centrality is one-directional here: continuation-linear maps are central,
-- but the converse fails.  'squareKBool' is central against symmetric probes
-- because XOR is associative and commutative; an asymmetric probe is needed
-- to witness the failure.
squareKBool :: Prob (->) Bool Bool Bool
squareKBool = choiceBy (/=) (embed id) (embed not)

-- | Another non-linear Bool kernel: ANDs the continuation at both truth values.
--
-- Used as an asymmetric probe to show that 'squareKBool' is not central.
andKBool :: Prob (->) Bool Bool Bool
andKBool = choiceBy (&&) (embed id) (embed not)

-- | Boolean-valued probe morphisms for centrality tests.
boolProbes :: [Prob (->) Bool Bool Bool]
boolProbes = [embed id, embed not, squareKBool, andKBool]

-- | Double-valued probe morphisms for centrality tests.
doubleProbes :: [Prob (->) Double Bool Bool]
doubleProbes = [embed id, embed not]

-- | Inputs for centrality tests where both components are 'Bool'.
boolInputs :: [(Bool, Bool)]
boolInputs = [(a, c) | a <- [False, True], c <- [False, True]]

-- | Inputs for centrality tests where the first component is unit.
unitBoolInputs :: [((), Bool)]
unitBoolInputs = [((), c) | c <- [False, True]]

-- | Boolean-valued pair continuations.
continuationsBool :: [(Bool, Bool) -> Bool]
continuationsBool = pairBoolFns [False, True]

-- | {0,1}-valued Double pair continuations.
continuationsDouble :: [(Bool, Bool) -> Double]
continuationsDouble = pairDoubleFns [False, True]

-- ---------------------------------------------------------------------------
-- Markov-category examples over FinRel Bool (GF(2))
-- ---------------------------------------------------------------------------

-- | Identity relation on N1 — deterministic.
finRelId :: FinRel N1 N1
finRelId = FinRel 1 1 [[True, True]]

-- | Zero map on N1 — deterministic.
finRelZeroMap :: FinRel N1 N1
finRelZeroMap = FinRel 1 1 [[True, False]]

-- | Total relation on N1 — total but not a function.
finRelTotal :: FinRel N1 N1
finRelTotal = FinRel 1 1 [[True, False], [False, True]]

-- | Neither total nor functional: relates 0 to both 0 and 1.
finRelNeither :: FinRel N1 N1
finRelNeither = FinRel 1 1 [[False, True]]

-- | The empty relation on N1 — copy-natural but not total.
--
-- This is the relevant corner of the FinRel square: it has a valid
-- diagonal (copy) but no total weakening (discard).
finRelEmpty :: FinRel N1 N1
finRelEmpty = FinRel 1 1 []

-- FinRel-specific Markov oracles: 'FinRel' no longer has unconstrained
-- 'Category'/'Tensor' instances, so we use the named constrained combinators.
finRelCopyNatural :: FinRel N1 N1 -> Bool
finRelCopyNatural f = copy1 `compFinRel` f == parFinRel f f `compFinRel` copy1
  where
    copy1 = copy :: FinRel N1 (N1, N1)

finRelDiscardNatural :: FinRel N1 N1 -> Bool
finRelDiscardNatural f = discard1 `compFinRel` f == discard1
  where
    discard1 = discard :: FinRel N1 ()

finRelDeterministic :: FinRel N1 N1 -> Bool
finRelDeterministic f = finRelCopyNatural f && finRelDiscardNatural f

-- ---------------------------------------------------------------------------
-- Prob examples
-- ---------------------------------------------------------------------------

-- | Fair coin with total mass 1.
coin :: Prob (->) Double () Bool
coin = fromWeighted [(True, 0.25), (False, 0.75)]

-- | Mass-zero kernel — copy-natural but not discard-natural.
--
-- This is the relevant corner of the Prob square: duplication of a zero
-- measure is still zero, but discard expects mass 1.
massZero :: Prob (->) Double () Bool
massZero = fromWeighted []

-- ---------------------------------------------------------------------------
-- Pipeline
-- ---------------------------------------------------------------------------

main :: IO ()
main = do
  results <-
    sequence
      [ -- Markov-category oracles (Ex9): copy/discard naturality is morphism-level
        check "FinRel finRelId is deterministic" $
          finRelDeterministic finRelId,
        check "FinRel finRelZeroMap is deterministic" $
          finRelDeterministic finRelZeroMap,
        check "FinRel finRelTotal is discard-natural but not copy-natural" $
          finRelDiscardNatural finRelTotal && not (finRelCopyNatural finRelTotal),
        check "FinRel finRelNeither is neither copy- nor discard-natural" $
          not (finRelCopyNatural finRelNeither) && not (finRelDiscardNatural finRelNeither),
        check "FinRel finRelEmpty is copy-natural but not discard-natural (relevant corner)" $
          finRelCopyNatural finRelEmpty && not (finRelDiscardNatural finRelEmpty),
        -- Copy/discards naturality via finite separators
        check "Prob copy natural for embed (deterministic fragment, FG nesting)" $
          copyNaturalP probCopySep parFG (embed not :: Prob (->) Bool Bool Bool),
        check "Prob copy natural for embed (deterministic fragment, GF nesting)" $
          copyNaturalP probCopySep parGF (embed not :: Prob (->) Bool Bool Bool),
        check "Prob copy NOT natural for coin (correlation vs independence, FG)" $
          not (copyNaturalP probCopySepDouble parFG coin),
        check "Prob copy NOT natural for coin (correlation vs independence, GF)" $
          not (copyNaturalP probCopySepDouble parGF coin),
        check "Prob squareKBool is copy-natural with neither nesting" $
          not (copyNaturalP probCopySep parFG squareKBool)
            && not (copyNaturalP probCopySep parGF squareKBool),
        check "Prob massZero is copy-natural but not discard-natural (relevant corner)" $
          copyNaturalP probCopySepDouble parFG massZero
            && not (discardNaturalP probDiscardSep massZero),
        -- Discard on the mass-1 fragment
        check "Prob discard natural for coin (mass-1 fragment)" $
          discardNaturalP probDiscardSep coin,
        check "Prob discard fails for unnormalised score (*2) . coin" $
          not (discardNaturalP probDiscardSep (score (* 2) . coin)),
        -- Centrality in the premonoidal centre: deterministic ⊊ central ⊊ all
        check "Prob embed not is central (linear in continuation)" $
          centralP boolInputs continuationsBool parFG parGF (embed not :: Prob (->) Bool Bool Bool) boolProbes,
        check "Prob coin is central (linear in continuation)" $
          centralP unitBoolInputs continuationsDouble parFG parGF coin doubleProbes,
        check "Prob score (*2) is central (linear in continuation)" $
          centralP boolInputs continuationsDouble parFG parGF (score (* 2) :: Prob (->) Double Bool Bool) doubleProbes,
        check "Prob squareKBool is NOT central (non-linear in continuation)" $
          not (centralP boolInputs continuationsBool parFG parGF squareKBool boolProbes),
        -- score (*2) fails copy-naturality: it multiplies once, duplication multiplies twice
        check "Prob score (*2) is NOT copy-natural" $
          not (copyNaturalP probCopySepDouble parFG (score (* 2) :: Prob (->) Double Bool Bool))
      ]
  if and results
    then putStrLn "\nAll pipeline tests passed."
    else error "Some pipeline tests failed."

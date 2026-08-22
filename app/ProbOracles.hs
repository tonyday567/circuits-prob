{-# LANGUAGE DataKinds #-}
{-# LANGUAGE ScopedTypeVariables #-}

-- | Prob separator oracles for the @circuits-axioma-pipeline@ executable.
module ProbOracles
  ( probEqOver,
    probEqDoubleOver,
    probCopySep,
    probCopySepDouble,
    probDiscardSep,
  )
where

import Circuit.Prob (Prob (..))
import Circuit.Tools.Test (approx, pairBoolFns, pairDoubleFns)
import Prelude hiding (curry, id, uncurry, (.))

-- | Equality oracle for @Prob (->) r a b@ using a supplied input set and
-- continuation set.
probEqOver ::
  forall a b r.
  (Bounded a, Enum a, Eq r) =>
  [b -> r] ->
  Prob (->) r a b ->
  Prob (->) r a b ->
  Bool
probEqOver ks (Prob p) (Prob q) =
  and
    [ p (\((), b) -> k b) ((), a) == q (\((), b) -> k b) ((), a)
    | k <- ks,
      a <- [minBound .. maxBound :: a]
    ]

-- | Equality oracle for @Prob (->) Double a b@ using a supplied input set and
-- {0,1}-valued continuation set.
probEqDoubleOver ::
  forall a b.
  (Bounded a, Enum a) =>
  [b -> Double] ->
  Prob (->) Double a b ->
  Prob (->) Double a b ->
  Bool
probEqDoubleOver ks (Prob p) (Prob q) =
  and
    [ approx (p (\((), b) -> k b) ((), a)) (q (\((), b) -> k b) ((), a))
    | k <- ks,
      a <- [minBound .. maxBound :: a]
    ]

-- | Separator predicate for copy-naturality with a 'Bool' scalar.
probCopySep ::
  forall a b.
  (Bounded a, Enum a, Bounded b, Enum b) =>
  Prob (->) Bool a (b, b) ->
  Prob (->) Bool a (b, b) ->
  Bool
probCopySep =
  probEqOver (pairBoolFns bs)
  where
    bs = [minBound .. maxBound :: b]

-- | Separator predicate for copy-naturality with a 'Double' scalar.
probCopySepDouble ::
  forall a b.
  (Bounded a, Enum a, Bounded b, Enum b) =>
  Prob (->) Double a (b, b) ->
  Prob (->) Double a (b, b) ->
  Bool
probCopySepDouble =
  probEqDoubleOver (map toDoubleFn (pairBoolFns bs))
  where
    bs = [minBound .. maxBound :: b]
    toDoubleFn k (b1, b2) = if k (b1, b2) then 1 else 0 :: Double

-- | Separator predicate for discard-naturality with a 'Double' scalar.
probDiscardSep ::
  forall a.
  (Bounded a, Enum a) =>
  Prob (->) Double a () ->
  Prob (->) Double a () ->
  Bool
probDiscardSep =
  probEqDoubleOver [const 0, const 1]

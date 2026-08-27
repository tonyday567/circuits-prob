-- | Metric equipment optics over the tropical semiring.
--
-- In @Prof@ enriched over @[0,∞]@ the distance between two spans is the
-- directed Hausdorff end/co-end.  For finite spans and the tropical semiring
-- this collapses to a directly computable sup/inf formula.
module Circuit.Prob.Metric
  ( -- * Metric spaces
    MetricSpace (..),

    -- * Tropical Hausdorff distance between spans
    spanDistanceTropical,
  )
where

import Circuit.Prob (Semiring (..), Tropical (..))
import Circuit.Span (Span, spanDistance)
import Prelude

-- $setup
-- >>> import Circuit.Prob.Metric
-- >>> import Circuit.Span (Span (..))

-- | A metric space valued in the tropical semiring.
--
-- The tropical order is @≥@, so the additive unit is positive infinity
-- ('sZero') and the multiplicative unit is zero ('sOne').
class MetricSpace a where
  -- | Tropical distance between two points.
  distance :: a -> a -> Tropical

-- | 'Int' equipped with tropical absolute difference.
--
-- >>> distance (3 :: Int) (7 :: Int)
-- Tropical {getTropical = 4.0}
--
-- >>> distance (5 :: Int) (5 :: Int)
-- Tropical {getTropical = 0.0}
instance MetricSpace Int where
  distance x y = Tropical (abs (fromIntegral x - fromIntegral y))

-- | Directed tropical Hausdorff distance between two finite spans.
--
-- This is 'Circuit.Span.spanDistance' specialised to the tropical semiring
-- and a 'MetricSpace' boundary.
--
-- >>> let spanA = Span [0 :: Int, 1] id id
-- >>> let spanB = Span [0 :: Int] id id
-- >>> spanDistanceTropical spanA spanB
-- Tropical {getTropical = 2.0}
--
-- The empty codomain apex is at infinity:
--
-- >>> spanDistanceTropical (Span [0 :: Int] id id) (Span [] id id)
-- Tropical {getTropical = Infinity}
spanDistanceTropical ::
  (MetricSpace a, MetricSpace b) =>
  Span a b ->
  Span a b ->
  Tropical
spanDistanceTropical = spanDistance sOne sZero sMul distance distance

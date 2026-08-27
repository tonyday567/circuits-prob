{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE UndecidableInstances #-}
{-# OPTIONS_GHC -Wno-redundant-constraints #-}

-- | Probability as a double-dual continuation category.
--
-- A morphism @Prob arr r a b@ is an expectation transformer: it turns a
-- continuation @arr (x, b) r@ (a "test" on the output) into a continuation
-- @arr (x, a) r@ (a test on the input).  The rank-2 quantification over @x@
-- is the cost of arrow-polymorphism — the same move used by 'Circuit.Poles'.
--
-- This is the categorical substrate for probability, conditioning, and
-- verification: choosing the dualizing object @r@ picks the semantics.
--
-- * @r = Log Double@ over @(->)@ gives expectation transformers / measures.
-- * @r = Bool@ over @(->)@ gives Dijkstra's weakest-precondition semantics.
-- * @r = Min Double@ (tropical) gives Bellman / Viterbi / MAP semantics.
--
-- This module currently provides structural instances for the function arrow
-- @(->)@.  Effectful variants (e.g. @Kleisli m@) follow the same pattern but
-- need scalar-lifting plumbing; the function case is where the design is
-- easiest to validate.
--
-- The tensor action on @Prob@ is /premonoidal/ in general: two valid nestings
-- ('parFG' and 'parGF') agree only on the linear (commutative) fragment.  We
-- therefore do not provide a canonical 'Circuit.Tensor.Tensor' instance; use
-- the explicit nesting you mean.
module Circuit.Prob
  ( -- * Double-dual probability arrow
    Prob (..),

    -- * Primitive constructors
    embed,
    fromWeighted,
    score,
    mass,

    -- * Cartesian copy/discard (deterministic)
    copyP,
    discardP,

    -- * Choice combined by a scalar operation
    choiceBy,
    orP,

    -- * Parallel nestings (Fubini on the linear fragment)
    parFG,
    parGF,

    -- * Traced Either (explicit, computability varies by scalar)
    traceE,
    traceEN,

    -- * Semiring scalars
    Semiring (..),
    Tropical (..),
  )
where

import Circuit.Category (Category (..))
import Circuit.Channel (Channel (..), Strength (..))
import Data.Bifunctor (second)
import Prelude hiding (id, (.))
import Prelude qualified

-- $setup
-- >>> import Circuit.Prob
-- >>> import Prelude hiding (id, (.))

-- | A semiring: an additive monoid and a multiplicative monoid, with
-- multiplication distributing over addition.
--
-- This class is intentionally minimal. It captures the scalar structure
-- needed by 'Circuit.Prob' without pulling in a full numeric prelude.
class Semiring r where
  sAdd :: r -> r -> r
  sMul :: r -> r -> r
  sZero :: r
  sOne :: r

-- | Min-plus tropical semiring over 'Double'.
--
-- Addition is 'min', multiplication is ordinary addition, the additive unit
-- is positive infinity, and the multiplicative unit is zero.
newtype Tropical = Tropical {getTropical :: Double}
  deriving (Eq, Ord, Show)

instance Semiring Tropical where
  sAdd (Tropical a) (Tropical b) = Tropical (Prelude.min a b)
  sMul (Tropical a) (Tropical b) = Tropical (a + b)
  sZero = Tropical (1 / 0)
  sOne = Tropical 0

-- | 'Double' is the usual probability semiring.
instance Semiring Double where
  sAdd = (+)
  sMul = (*)
  sZero = 0
  sOne = 1

-- | 'Bool' is the reachability / model-checking semiring.
instance Semiring Bool where
  sAdd = (||)
  sMul = (&&)
  sZero = False
  sOne = True

-- | Double-dual embedding of @arr@ with respect to dualizing object @r@.
--
-- A value @Prob arr r a b@ reads an output-continuation @arr (x, b) r@ and
-- produces an input-continuation @arr (x, a) r@.  Composition is continuation
-- composition (contravariant in the middle type).
newtype Prob arr r a b = Prob
  { runProb :: forall x. arr (x, b) r -> arr (x, a) r
  }

-- ---------------------------------------------------------------------------
-- Category
-- ---------------------------------------------------------------------------

-- | Identity and composition are arrow-polymorphic: they only manipulate the
-- continuation function, never the base arrow.  This is why 'Category' costs
-- nothing from @arr@.
instance (Category arr) => Category (Prob arr r) where
  id :: Prob arr r a a
  id = Prob Prelude.id
  {-# INLINE id #-}

  (.) ::
    Prob arr r b c ->
    Prob arr r a b ->
    Prob arr r a c
  Prob f . Prob g = Prob $ \k -> g (f k)
  {-# INLINE (.) #-}

-- ---------------------------------------------------------------------------
-- Primitives (function arrow)
-- ---------------------------------------------------------------------------

-- | Embed a deterministic function as a probability morphism.
--
-- The continuation is applied to the transformed output, with the context
-- wire carried along unchanged.
embed :: (a -> b) -> Prob (->) r a b
embed h = Prob $ \k -> k . second h
{-# INLINE embed #-}

-- | Build a probability morphism from a finite weighted table.
--
-- This is the bridge to 'Circuit.Parser.Weighted' and the entry point for
-- genuine measures in the linear fragment: every entry contributes linearly
-- to the expectation.
fromWeighted :: (Semiring r) => [(b, r)] -> Prob (->) r () b
fromWeighted xs = Prob $ \k (x, ()) -> foldr sAdd sZero [sMul w (k (x, b)) | (b, w) <- xs]
{-# INLINE fromWeighted #-}

-- | Scale the result of a continuation.
--
-- With endomorphisms @r -> r@ this is a /modality/, not necessarily a scalar
-- multiplication.  The definitional law is the anti-homomorphism
-- @score w . score v = score (v . w)@; commutativity holds only when the
-- endos commute.  For the probabilistic sub-case @score (w *)@, the usual
-- multiplicative law is recovered.
score :: (r -> r) -> Prob (->) r a a
score scale = Prob $ \k (x, a) -> scale (k (x, a))
{-# INLINE score #-}

-- | Compute the total mass of an unnormalised morphism against the unit
-- continuation.
mass :: (Semiring r) => Prob (->) r a b -> a -> r
mass (Prob f) a = f (const sOne) ((), a)
{-# INLINE mass #-}

-- | Deterministic copy.  Naturality of this morphism characterises the
-- deterministic fragment: @copyP . embed h == parFG (embed h) (embed h) . copyP@.
copyP :: Prob (->) r a (a, a)
copyP = embed (\a -> (a, a))
{-# INLINE copyP #-}

-- | Deterministic discard.  On the mass-1 fragment @f . discardP == discardP@;
-- unnormalised morphisms fail this equation.
discardP :: Prob (->) r a ()
discardP = embed (const ())
{-# INLINE discardP #-}

-- | Binary choice combined by a scalar operation.  This one combinator covers
-- several rows of the instance table:
--
-- * @choiceBy (||)@ — angelic / reachability (Bool).
-- * @choiceBy (&&)@ — demonic / refutation (Bool).
-- * @choiceBy (+)@  — sum of weighted alternatives (Num r).
-- * @choiceBy min@  — tropical / Viterbi choice (Ord r).
choiceBy :: (r -> r -> r) -> Prob (->) r a b -> Prob (->) r a b -> Prob (->) r a b
choiceBy (<+>) (Prob f) (Prob g) = Prob $ \k p -> f k p <+> g k p
{-# INLINE choiceBy #-}

-- | Angelic choice for @r = Bool@ (weakest-precondition / reachability
-- semantics).  Succeeds if either branch can; short-circuiting of @(||)@
-- gives the trace on this scalar for free.
orP :: Prob (->) Bool a b -> Prob (->) Bool a b -> Prob (->) Bool a b
orP = choiceBy (||)
{-# INLINE orP #-}

-- ---------------------------------------------------------------------------
-- Structural instances (cartesian tensor, function arrow)
-- ---------------------------------------------------------------------------

-- | The cartesian structural morphisms are deterministic, so they are just
-- 'embed's of the base-arrow associators and braiding.  'strength' is the
-- non-trivial one: it instantiates the rank-2 context @x@ at @(x, s)@,
-- which is exactly why the universally quantified context is the honest cost
-- of the tensor.
instance Channel (,) (Prob (->) r) where
  assoc = embed assoc
  {-# INLINE assoc #-}

  assoc' = embed assoc'
  {-# INLINE assoc' #-}

  slide = embed slide
  {-# INLINE slide #-}

instance Strength (,) (Prob (->) r) where
  strength (Prob f) = Prob $ \k -> f (k . assoc) . assoc'
  {-# INLINE strength #-}

-- ---------------------------------------------------------------------------
-- Parallel nestings (Fubini on the linear fragment)
-- ---------------------------------------------------------------------------

-- | Parallel composition: @g@ runs at context @(x, b)@, @f@ runs at context
-- @(x, c)@.  This is one of two lawful nestings; it agrees with 'parGF' on
-- the linear/commutative fragment.
parFG ::
  Prob (->) r a b ->
  Prob (->) r c d ->
  Prob (->) r (a, c) (b, d)
parFG (Prob f) (Prob g) = Prob $ \k ->
  let kg ((ctx, b), d) = k (ctx, (b, d))
      gc = g kg
      kf ((ctx, c), b) = gc ((ctx, b), c)
      fa = f kf
   in \(ctx, (a, c)) -> fa ((ctx, c), a)
{-# INLINE parFG #-}

-- | Parallel composition: @f@ runs at context @(x, d)@, @g@ runs at context
-- @(x, a)@.  The other nesting; agrees with 'parFG' on the linear fragment.
parGF ::
  Prob (->) r a b ->
  Prob (->) r c d ->
  Prob (->) r (a, c) (b, d)
parGF (Prob f) (Prob g) = Prob $ \k ->
  let kf ((ctx, d), b) = k (ctx, (b, d))
      fa = f kf
      kg ((ctx, a), d) = fa ((ctx, d), a)
      gb = g kg
   in \(ctx, (a, c)) -> gb ((ctx, a), c)
{-# INLINE parGF #-}

-- ---------------------------------------------------------------------------
-- Traced Either (explicit, not a canonical instance)
-- ---------------------------------------------------------------------------

-- | Least-fixpoint trace over the 'Either' tensor.
--
-- This is the denotationally correct definition: @Right@ values feed back into
-- the body, @Left@ values escape.  For genuinely cyclic bodies and strict
-- numeric scalars (e.g. @r = Double@) it diverges — the geometric series
-- exists but strict @(+)@ never reaches it.  Use 'traceEN' for a computable
-- approximation, or switch to a scalar whose lattice structure supplies the
-- fixpoint (e.g. @r = Bool@, where @(||)@ short-circuits) or to an effectful
-- base arrow where sampling terminates almost surely.
--
-- We do not provide a @Traced Either (Prob (->) r)@ instance because the
-- canonical trace is only available on a fragment; 'traceE' and 'traceEN' are
-- exported as explicit choices.
traceE ::
  Prob (->) r (Either a s) (Either b s) ->
  Prob (->) r a b
traceE (Prob f) = Prob $ \k ->
  let step (x, Left b) = k (x, b)
      step (x, Right s) = f step (x, Right s)
   in \(x, a) -> f step (x, Left a)
{-# INLINE traceE #-}

-- | Fuel-bounded variant of 'traceE'.  After the fuel is exhausted, re-entries
-- contribute the supplied @zero@ value.  This converges to the least fixpoint
-- with error proportional to the probability of not having terminated by the
-- fuel limit.
traceEN ::
  r ->
  Int ->
  Prob (->) r (Either a s) (Either b s) ->
  Prob (->) r a b
traceEN zero n0 (Prob f) = Prob $ \k ->
  let step _ (x, Left b) = k (x, b)
      step n (x, Right s)
        | n <= 0 = zero
        | otherwise = f (step (n - 1)) (x, Right s)
   in \(x, a) -> f (step n0) (x, Left a)
{-# INLINE traceEN #-}

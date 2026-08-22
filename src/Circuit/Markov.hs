{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE UndecidableInstances #-}

-- | Markov-category tests for affine structural morphisms.
--
-- A Markov category is a semicartesian symmetric monoidal category in which
-- every object carries a distinguished commutative comonoid (copy, discard)
-- and the monoidal unit is terminal.  In our setting the structural morphisms
-- are explicit capabilities ('Copy' / 'Discard'), so this module provides
-- /law tests/ rather than a bundled class.
--
-- The key observation from the excavation (Ex9) is that copyability and
-- discardability are morphism-level properties, not object-level modalities:
--
-- * A map @f :: a -> b@ is /discard-natural/ when
--   @discard . f = discard@.  In 'Prob' this is exactly the mass-1 fragment;
--   in 'FinRel' it is the total relations.
-- * A map @f :: a -> b@ is /copy-natural/ when
--   @copy . f = par f f . copy@.  These are the deterministic maps: partial
--   functions in 'FinRel', embedded functions in 'Prob'.
--
-- The copy-natural maps form a cartesian subcategory; the discard-natural
-- maps form a semicartesian one.
module Circuit.Markov
  ( -- * Naturality tests
    copyNatural,
    discardNatural,

    -- * Deterministic centre
    deterministic,
  )
where

import Circuit.Category (Category (..))
import Circuit.Bimonoid (Copy (..), Discard (..))
import Circuit.Tensor (Tensor (..))
import Prelude hiding (id, (.))

-- | Test whether @f@ is a homomorphism from the copy comonoid on @a@ to the
-- copy comonoid on @b@.
--
-- > copy . f == par f f . copy
--
-- The equality predicate is supplied by the caller because many bases
-- (notably 'Prob') do not admit decidable equality of morphisms.  A finite
-- /separator/ — a set of continuations and inputs — is the usual way to
-- produce this predicate for such bases.
copyNatural ::
  (Tensor (,) arr, Copy arr a, Copy arr b) =>
  (arr a (b, b) -> arr a (b, b) -> Bool) ->
  arr a b ->
  Bool
copyNatural eq f = eq (copy . f) (par f f . copy)
{-# INLINE copyNatural #-}

-- | Test whether @f@ is a homomorphism from the discard comonoid on @a@ to
-- the discard comonoid on @b@.
--
-- > discard . f == discard
--
-- The equality predicate is supplied by the caller for the same reason as
-- 'copyNatural'.
discardNatural ::
  (Category arr, Discard arr a, Discard arr b) =>
  (arr a () -> arr a () -> Bool) ->
  arr a b ->
  Bool
discardNatural eq f = eq (discard . f) discard
{-# INLINE discardNatural #-}

-- | A map is deterministic precisely when it is both copy-natural and
-- discard-natural: it preserves the full cartesian comonoid.
deterministic ::
  ( Tensor (,) arr,
    Copy arr a,
    Copy arr b,
    Discard arr a,
    Discard arr b
  ) =>
  (arr a (b, b) -> arr a (b, b) -> Bool) ->
  (arr a () -> arr a () -> Bool) ->
  arr a b ->
  Bool
deterministic eqCopy eqDiscard f = copyNatural eqCopy f && discardNatural eqDiscard f
{-# INLINE deterministic #-}

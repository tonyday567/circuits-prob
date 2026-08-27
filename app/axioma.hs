{-# LANGUAGE DataKinds #-}

-- | Probability oracles for the double-dual arrow.
--
-- These checks exercise 'Circuit.Prob' and 'Circuit.Markov' (via the pipeline
-- executable) in isolation from the core wiring substrate.  They live here
-- because the core @circuits@ package no longer depends on probability
-- semantics.
module Main where

import Circuit.Category (K (..), id, (.))
import Circuit.Optic (Optic, composeOptic, identityOptic, opticUpdate)
import Circuit.Poly (Mono)
import Circuit.Prob
  ( Prob (..),
    Semiring (..),
    Tropical (..),
    embed,
    fromWeighted,
    mass,
    orP,
    parFG,
    parGF,
    score,
    traceE,
    traceEN,
  )
import Circuit.Span (Span (..), spanDistance)
import Circuit.System (System, monoIn, runSystem, system)
import Circuit.Tools.Test (approx, check)
import Control.Monad (replicateM_)
import Data.IORef (IORef, modifyIORef', newIORef, readIORef, writeIORef)
import Data.List (foldl', replicate)
import Prelude hiding (id, (.))
import Prelude qualified as Pre

-- | 'check' for assertions that live in 'IO'.
checkIO :: String -> IO Bool -> IO Bool
checkIO name act = do
  ok <- act
  putStrLn $ (if ok then "PASS " else "FAIL ") ++ name
  pure ok

-- ---------------------------------------------------------------------------
-- Prob helpers for fragment oracles
-- ---------------------------------------------------------------------------

-- | Fair coin with total mass 1.
coin :: Prob (->) Double () Bool
coin = fromWeighted [(True, 0.25), (False, 0.75)]

-- | Unnormalised weighted measure with total mass 1.5.
unnorm :: Prob (->) Double () Bool
unnorm = fromWeighted [(True, 0.5), (False, 1.0)]

-- | A deliberately non-linear inhabitant: squares its continuation.
squareK :: Prob (->) Double a a
squareK = Prob $ \k p -> k p * k p

-- | Evaluate a measure-free morphism against a continuation on the output.
ev :: Prob (->) Double () b -> ((b -> Double) -> Double)
ev (Prob f) k = f (\((), b) -> k b) ((), ())

-- | Geometric trial body: state counts flips; heads escapes with the count.
geomBody :: Double -> Prob (->) Double (Either () Int) (Either Int Int)
geomBody p = Prob $ \k (x, e) ->
  let n = case e of Left () -> 0; Right m -> m
   in p * k (x, Left (n + 1)) + (1 - p) * k (x, Right (n + 1))

-- | A three-state walk on 'Int': from s, either exit with s (Left) or move to
-- s+1 (Right). Used for the Bool trace reachability oracle.
walkBody :: Prob (->) Bool (Either Int Int) (Either Int Int)
walkBody = orP (embed exit) (embed stepR)
  where
    exit e = Left (either id id e)
    stepR e = Right (either id id e + 1)

-- | Reachability test via the Bool least-fixpoint trace.
reach :: Int -> Bool
reach target = runProb (traceE walkBody) (\((), s) -> s == target) ((), 0)

-- ---------------------------------------------------------------------------
-- Metric equipment optics
--
-- In [0,∞]-enriched Prof the distance between two spans (s,t) and (a,b) is
--
-- @
--   d((s,t),(a,b)) = sup_x inf_y [ d(s x, a y) + d(b y, t x) ]
-- @
--
-- For finite spans over a tropical scalar this is directly computable.  The
-- residual is remembered on the nose (Circuit.Span), so the sup/inf range over
-- the apex enumerations.
-- ---------------------------------------------------------------------------

-- | Tropical absolute difference between two 'Int'-valued points.
tropicalDist :: Int -> Int -> Tropical
tropicalDist x y = Tropical (abs (fromIntegral x - fromIntegral y))

-- | Directed Hausdorff-style distance between two finite spans.
--
-- This is 'Circuit.Span.spanDistance' specialised to the tropical semiring.
--
-- The tropical order is @≥@, so the @sup@ (empty-domain value) is the least
-- element @0@ and the @inf@ (empty-codomain value) is the greatest element
-- @+∞@.  In 'Semiring' terms that is 'sOne' (multiplicative unit, ordinary 0)
-- and 'sZero' (additive unit, infinity).
metricSpanDistance ::
  (a -> a -> Tropical) ->
  (b -> b -> Tropical) ->
  Span a b ->
  Span a b ->
  Tropical
metricSpanDistance = spanDistance sOne sZero sMul

-- ---------------------------------------------------------------------------
-- Keystone: System (Prob (->) r) s (Mono i o)
--
-- The stochastic Moore machine, stepped by expectation. The scalar @r@ selects
-- the semantics: @Double@ for probability, @Tropical@ for min-plus / Viterbi.
-- ---------------------------------------------------------------------------

-- | Run a finite-state stochastic Moore machine by expectation.
--
-- Given an enumeration of the state space, the machine, a list of inputs, a
-- query on the final state, and an initial state, return the expected query
-- value.
--
-- For @r = Double@ this is ordinary expectation over the final state
-- distribution. For @r = Tropical@ it is the min-plus cost of the cheapest
-- final state.
expectSystem ::
  (Eq s, Semiring r) =>
  [s] ->
  System (Prob (->) r) s (Mono i o) ->
  [i] ->
  (s -> r) ->
  s ->
  r
expectSystem states sys is q s0 =
  foldl' sAdd sZero [q s `sMul` distFinal s | s <- states]
  where
    distFinal = foldl' step initDist is
    initDist s = if s == s0 then sOne else sZero
    step dist i s' =
      foldl' sAdd sZero [dist s `sMul` pTrans s i s' | s <- states]
    pTrans s i s' =
      runProb
        (runSystem sys)
        (\((), (s'', _)) -> if s' == s'' then sOne else sZero)
        ((), (s, monoIn i))

-- | Three-state chain for the keystone doctests.
data S3 = S0 | S1 | S2
  deriving (Eq, Show, Enum, Bounded)

-- | Probability semantics: a lazy random walk on three states.
--
-- From each state, stay with probability 0.5 and move to the next state
-- (cyclically) with probability 0.5.
chain3Prob :: System (Prob (->) Double) S3 (Mono () ())
chain3Prob = system $ Prob $ \k (x, (s, _)) ->
  let next = case s of
        S0 -> [(S0, 0.5), (S1, 0.5)]
        S1 -> [(S1, 0.5), (S2, 0.5)]
        S2 -> [(S2, 0.5), (S0, 0.5)]
   in foldl' (+) 0 [p * k (x, (s', ((), ()))) | (s', p) <- next]

-- | Tropical semantics: the same graph with transition costs.
--
-- Staying costs 1, moving costs 2. The cheapest n-step path to a state is the
-- Viterbi value.
chain3Tropical :: System (Prob (->) Tropical) S3 (Mono () ())
chain3Tropical = system $ Prob $ \k (x, (s, _)) ->
  let next = case s of
        S0 -> [(S0, Tropical 1), (S1, Tropical 2)]
        S1 -> [(S1, Tropical 1), (S2, Tropical 2)]
        S2 -> [(S2, Tropical 1), (S0, Tropical 2)]
   in foldl' sAdd sZero [c `sMul` k (x, (s', ((), ()))) | (s', c) <- next]

-- | Exact occupancy probabilities for the 3-state chain after @n@ steps,
-- starting from @S0@.
--
-- >>> occupancyProb 0
-- [1.0,0.0,0.0]
--
-- >>> occupancyProb 1
-- [0.5,0.5,0.0]
--
-- >>> occupancyProb 2
-- [0.25,0.5,0.25]
--
-- >>> occupancyProb 3
-- [0.25,0.375,0.375]
occupancyProb :: Int -> [Double]
occupancyProb n =
  [getMass s | s <- [S0, S1, S2]]
  where
    getMass s = expectSystem [S0, S1, S2] chain3Prob (replicate n ()) (\s' -> if s' == s then 1 else 0) S0

-- | Tropical (Viterbi) cost to be in each state after @n@ steps, starting from
-- @S0@.
--
-- >>> viterbiCost 0
-- [0.0,Infinity,Infinity]
--
-- >>> viterbiCost 1
-- [1.0,2.0,Infinity]
--
-- >>> viterbiCost 2
-- [2.0,3.0,4.0]
viterbiCost :: Int -> [Double]
viterbiCost n =
  [getTropical (expectSystem [S0, S1, S2] chain3Tropical (replicate n ()) (\s' -> if s' == s then sOne else sZero) S0) | s <- [S0, S1, S2]]

-- | Cyclic successor on the three-state chain.
nextS :: S3 -> S3
nextS S0 = S1
nextS S1 = S2
nextS S2 = S0

-- | Boolean semantics: from each state, staying and moving are both possible.
--
-- This is the reachability / model-checking row:
-- @expectSystem@ with @r = Bool@ answers "is there a path from @s0@ to a state
-- satisfying @q@ in exactly @n@ steps?"
chain3Bool :: System (Prob (->) Bool) S3 (Mono () ())
chain3Bool = system $ Prob $ \k (x, (s, _)) ->
  let next = case s of
        S0 -> [S0, S1]
        S1 -> [S1, S2]
        S2 -> [S2, S0]
   in foldl' sAdd sZero [k (x, (s', ((), ()))) | s' <- next]

-- | States reachable from @S0@ in exactly @n@ steps under the Boolean
-- transition relation.
--
-- >>> reachable 0
-- [S0]
--
-- >>> reachable 1
-- [S0,S1]
--
-- >>> reachable 2
-- [S0,S1,S2]
reachable :: Int -> [S3]
reachable n = filter (\s -> expectSystem [S0, S1, S2] chain3Bool (replicate n ()) (== s) S0) [S0, S1, S2]

-- ---------------------------------------------------------------------------
-- Keystone row: K IO (Monte Carlo rollout)
--
-- The scalar axis lists @Log Double@ for this row; the executable uses plain
-- @Double@ for normalized sampling.  The @Log Double@ variant is the same
-- structure accumulating log importance weights.
-- ---------------------------------------------------------------------------

-- | Tiny deterministic RNG so the Monte Carlo axioms are reproducible without
-- adding a dependency.
newtype RNG = RNG {rngState :: Int}

-- | Linear congruential generator step, returning a value in @[0,1)@.
stepRNG :: RNG -> (Double, RNG)
stepRNG (RNG s) =
  let modulus = 2 ^ (31 :: Int) :: Int
      s' = (1103515245 * s + 12345) `Pre.rem` modulus
   in (fromIntegral s' / fromIntegral modulus, RNG s')

sampleDouble :: IORef RNG -> IO Double
sampleDouble ref = do
  rng <- readIORef ref
  let (u, rng') = stepRNG rng
  writeIORef ref rng'
  pure u

-- | Monte Carlo version of the three-state chain: sample a successor rather
-- than enumerating the expectation.
chain3IO :: IORef RNG -> System (Prob (K IO) Double) S3 (Mono () ())
chain3IO ref = system $ Prob $ \k -> K $ \(x, (s, _)) -> do
  u <- sampleDouble ref
  let s' = if u < 0.5 then s else nextS s
  runK k (x, (s', ((), ())))

-- | Run one @K IO@ trajectory for @n@ steps, returning the final state.
--
-- The continuation passed to 'runProb' returns a dummy scalar and writes the
-- sampled next state into a fresh 'IORef'; this is how we extract the state
-- from an expectation transformer.
runTrajectoryIO :: System (Prob (K IO) Double) S3 (Mono () ()) -> Int -> S3 -> IO S3
runTrajectoryIO sys = go
  where
    go 0 s = pure s
    go m s = step s >>= go (m - 1)
    step s = do
      nextRef <- newIORef s
      let cont = K $ \(_, (s', ((), ()))) -> writeIORef nextRef s' >> pure 0
      _ <- runK (runProb (runSystem sys) cont) ((), (s, monoIn ()))
      readIORef nextRef

-- | Empirical occupancy probabilities after @nSteps@, estimated from
-- @nTrials@ trajectories starting at @s0@.
mcOccupancy :: System (Prob (K IO) Double) S3 (Mono () ()) -> Int -> Int -> S3 -> IO [Double]
mcOccupancy sys nTrials nSteps s0 = do
  counts <- newIORef (0 :: Int, 0, 0)
  let trial = do
        s <- runTrajectoryIO sys nSteps s0
        modifyIORef' counts $ \(c0, c1, c2) -> case s of
          S0 -> (c0 + 1, c1, c2)
          S1 -> (c0, c1 + 1, c2)
          S2 -> (c0, c1, c2 + 1)
  replicateM_ nTrials trial
  (c0, c1, c2) <- readIORef counts
  let total = fromIntegral nTrials :: Double
  let toDouble :: Int -> Double
      toDouble = fromIntegral
  pure [toDouble c0 / total, toDouble c1 / total, toDouble c2 / total]

main :: IO ()
main = do
  results <-
    sequence
      [ -- Deterministic fragment
        check "Prob embed preserves identity" $
          let k ((), b) = fromIntegral b :: Double
           in runProb (embed id) k ((), 5 :: Int) == k ((), 5 :: Int),
        check "Prob embed preserves composition" $
          let f = (+ 10) :: Int -> Int
              g = (* 3) :: Int -> Int
              k ((), c) = fromIntegral c :: Double
           in runProb (embed (f Pre.. g)) k ((), 5)
                == runProb (embed f . embed g) k ((), 5),
        -- Score modality structure
        check "Prob score anti-homomorphism" $
          let w = (* 2.0) :: Double -> Double
              v = (+ 3.0) :: Double -> Double
              k ((), _) = 1.0 :: Double
           in runProb (score w . score v) k ((), 5 :: Int)
                == runProb (score (v Pre.. w)) k ((), 5 :: Int),
        check "Prob score endos need not commute" $
          let w = (* 2.0) :: Double -> Double
              v = (+ 3.0) :: Double -> Double
              k ((), _) = 1.0 :: Double
           in runProb (score w . score v) k ((), 5 :: Int)
                /= runProb (score v . score w) k ((), 5 :: Int),
        -- Linear fragment: multiplicative endos central against real measures
        check "Prob centrality of (*2) vs coin (linear fragment)" $
          approx
            (ev (score (* 2) . coin) (\b -> if b then 10 else 1))
            (ev (coin . score (* 2)) (\b -> if b then 10 else 1)),
        -- Affine/Markov fragment: affine endos central exactly on mass-1
        check "Prob centrality of (+3) vs coin (mass 1, affine fragment)" $
          approx
            (ev (score (+ 3) . coin) (\b -> if b then 10 else 1))
            (ev (coin . score (+ 3)) (\b -> if b then 10 else 1)),
        check "Prob centrality of (+3) fails off mass-1 fragment" $
          not
            ( approx
                (ev (score (+ 3) . unnorm) (\b -> if b then 10 else 1))
                (ev (unnorm . score (+ 3)) (\b -> if b then 10 else 1))
            ),
        -- Outside the linear fragment even normalised measures fail centrality
        check "Prob centrality of (^2) fails vs coin" $
          not
            ( approx
                (ev (score (^ (2 :: Int)) . coin) (\b -> if b then 10 else 1))
                (ev (coin . score (^ (2 :: Int))) (\b -> if b then 10 else 1))
            ),
        -- Fubini on the linear fragment
        check "Prob parFG == parGF on coin x coin (Fubini)" $
          let k ((), (b, d)) = (if b then 10 else 1) * (if d then 100 else 1) :: Double
           in approx
                (runProb (parFG coin coin) k ((), ((), ())))
                (runProb (parGF coin coin) k ((), ((), ()))),
        check "Prob parFG != parGF with squareK x coin (premonoidal)" $
          let k ((), (b, d)) = b + (if d then 10 else 1) :: Double
           in not
                ( approx
                    (runProb (parFG squareK coin) k ((), (2.0, ())))
                    (runProb (parGF squareK coin) k ((), (2.0, ())))
                ),
        -- Mass detects affineness / discardability
        check "Prob mass detects score breaking affineness" $
          approx (mass (score (* 2) . coin) ()) 2.0
            && approx (mass coin ()) 1.0,
        -- Traced Either: computability graded by scalar
        check "Prob traceEN converges to 1/p for geometric (error ~ q^fuel)" $
          let e n = ev (traceEN 0 n (geomBody 0.5)) fromIntegral
           in approx (e 60) 2.0 && e 5 < e 20 && e 20 < e 60,
        check "Prob Bool trace reachability via lazy (||)" $
          reach 2,
        -- Keystone: System (Prob (->) r) s (Mono i o)
        check "Keystone: System (Prob Double) S3 (Mono () ()) typechecks" $
          length (occupancyProb 0) == 3,
        check "Keystone: exact occupancy after 2 steps" $
          occupancyProb 2 == [0.25, 0.5, 0.25],
        check "Keystone: exact occupancy after 3 steps" $
          let probs = occupancyProb 3
              (p0, p1, p2) = case probs of
                [p0', p1', p2'] -> (p0', p1', p2')
                _ -> error "unreachable" -- occupancyProb 3 returns exactly three probabilities
           in approx p0 0.25 && approx p1 0.375 && approx p2 0.375,
        check "Keystone: System (Prob Tropical) S3 (Mono () ()) typechecks" $
          length (viterbiCost 0) == 3,
        check "Keystone: tropical Viterbi cost after 2 steps" $
          viterbiCost 2 == [2.0, 3.0, 4.0],
        check "Keystone: tropical Viterbi cost after 3 steps" $
          viterbiCost 3 == [3.0, 4.0, 5.0],
        -- Bool reachability row
        check "Keystone: System (Prob Bool) S3 (Mono () ()) typechecks" $
          length (reachable 0) == 1,
        check "Keystone: reachability after 1 step" $
          reachable 1 == [S0, S1],
        check "Keystone: reachability after 2 steps" $
          reachable 2 == [S0, S1, S2],
        -- K IO Monte Carlo row
        checkIO "Keystone: System (Prob (K IO) Double) S3 (Mono () ()) typechecks" $ do
          ref <- newIORef (RNG 0)
          occ <- mcOccupancy (chain3IO ref) 10000 2 S0
          pure $ length occ == 3,
        checkIO "Keystone: Monte Carlo occupancy after 2 steps" $ do
          ref <- newIORef (RNG 0)
          [p0, p1, p2] <- mcOccupancy (chain3IO ref) 10000 2 S0
          pure $ abs (p0 - 0.25) < 0.02 && abs (p1 - 0.5) < 0.02 && abs (p2 - 0.25) < 0.02,
        -- Metric equipment optics: directed Hausdorff distance between spans
        check "Metric optic: tropical distance between identical spans is zero" $
          let spanA = Span [0 :: Int] id id :: Span Int Int
           in metricSpanDistance tropicalDist tropicalDist spanA spanA == Tropical 0,
        check "Metric optic: distance is asymmetric and residual-aware" $
          let spanA = Span [0, 1] id id :: Span Int Int
              spanB = Span [0] id id :: Span Int Int
              d = metricSpanDistance tropicalDist tropicalDist spanA spanB
           in d == Tropical 2,
        check "Metric optic: empty codomain apex is distance Infinity" $
          let spanA = Span [0 :: Int] id id
              spanEmpty = Span ([] :: [Int]) id id
           in metricSpanDistance tropicalDist tropicalDist spanA spanEmpty == sZero,
        check "Metric optic: empty domain apex is distance 0" $
          let spanA = Span [0 :: Int] id id
              spanEmpty = Span ([] :: [Int]) id id
           in metricSpanDistance tropicalDist tropicalDist spanEmpty spanA == sOne,
        check "Metric optic: triangle inequality holds" $
          let spanA = Span [0, 1] id id :: Span Int Int
              spanB = Span [0] id id :: Span Int Int
              spanC = Span [1] id id :: Span Int Int
              dAB = metricSpanDistance tropicalDist tropicalDist spanA spanB
              dBC = metricSpanDistance tropicalDist tropicalDist spanB spanC
              dAC = metricSpanDistance tropicalDist tropicalDist spanA spanC
           in getTropical dAC <= getTropical (dAB `sMul` dBC),
        -- The Unital/Tensor split lets optics exist over premonoidal Prob:
        -- identity and composition need only Strength, and identity needs only
        -- the deterministic unitors.
        check "Optic over Prob Tropical: identity optic updates agree" $
          let m = score (sMul (Tropical 2)) :: Prob (->) Tropical () ()
              o = identityOptic :: Optic (,) (Prob (->) Tropical) () () () () ()
           in mass (opticUpdate o m) () == mass m (),
        check "Optic over Prob Tropical: composed identity is identity" $
          let m = score (sMul (Tropical 2)) :: Prob (->) Tropical () ()
              o = identityOptic :: Optic (,) (Prob (->) Tropical) () () () () ()
           in mass (opticUpdate (composeOptic o o) m) () == mass m ()
      ]
  if and results
    then putStrLn "\nAll tests passed."
    else error "Some tests failed."

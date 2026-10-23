/- 
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Proof.PrimeClassDeletion.GreedyPrimeAsymptotics
import PrimeFactorOscillations.Proof.PrimeClassDeletion.PrimeReturnWave

/-!
# A uniform frozen square horizon forces a constant square-root envelope

The premise is imposed at every pre-prime frame in the indicated prefix.
This is stronger than the existence of a cofinal sequence of good frames.
No quiet-window estimate or prime oscillation theorem is assumed implicitly.
-/

set_option autoImplicit false
set_option Elab.async false

namespace PrimeFactorOscillations.PrimeClassDeletion

open PrimeFactorUnimodality
open PrimeFactorOscillations.PrimeClassSampling

/-- A greedy clock cannot jump far above a monotone rejection ceiling when
every state above that ceiling is required to be accepted. -/
theorem clockDeletedMass_le_rejection_barrier
    (e w b : Nat -> Real) (hw0 : 0 <= w 0) (hb0 : 0 <= b 0)
    (hw : Monotone w) (hb : Monotone b) (N : Nat) :
    (forall i : Nat, i <= N ->
      b i <= clockDeletedMass e w i -> e i <= clockDeletedMass e w i) ->
    clockDeletedMass e w (N + 1) <= b N + w N := by
  classical
  induction N with
  | zero =>
      intro _
      change deletionStep (e 0) (w 0) 0 <= b 0 + w 0
      unfold deletionStep
      by_cases h : e 0 <= 0
      case pos =>
        rw [ite_eq_left h]
        exact add_nonneg hb0 hw0
      case neg =>
        rw [ite_eq_right h]
        linarith only [hb0]
  | succ N ih =>
      intro hhold
      have hprev := ih (fun i hi => hhold i (hi.trans (Nat.le_succ N)))
      have hbnext := hb (Nat.le_succ N)
      have hwnext := hw (Nat.le_succ N)
      change deletionStep (e (N + 1)) (w (N + 1))
        (clockDeletedMass e w (N + 1)) <= b (N + 1) + w (N + 1)
      unfold deletionStep
      by_cases h : e (N + 1) <= clockDeletedMass e w (N + 1)
      case pos =>
        rw [ite_eq_left h]
        linarith only [hprev, hbnext, hwnext]
      case neg =>
        rw [ite_eq_right h]
        have hbelow : clockDeletedMass e w (N + 1) < b (N + 1) := by
          apply lt_of_not_ge
          intro hbarrier
          exact h (hhold (N + 1) (Nat.le_refl _) hbarrier)
        linarith only [hbelow]

/-- The all-frame square-horizon premise already forces the stronger
constant square-root theta bound on this finite prime prefix. -/
theorem primeClock_square_horizon_forces_root_bound
    (n : Nat)
    (hquiet : forall i : Nat, i <= n ->
      (primeAt i : Real) <= (clockDeletedMass primeClockError primeLogWeight i) ^ 2 ->
      primeClockError i <= clockDeletedMass primeClockError primeLogWeight i) :
    Chebyshev.theta (primeAt n : Real) - (primeAt n : Real) <=
      Real.sqrt (primeAt n : Real) + Real.log (primeAt n : Real) := by
  have hb : Monotone (fun i : Nat => Real.sqrt (primeAt i : Real)) := by
    intro i j hij
    exact Real.sqrt_le_sqrt (Nat.cast_le.mpr (primeAt_strictMono.monotone hij))
  have hbound := clockDeletedMass_le_rejection_barrier
    primeClockError primeLogWeight (fun i => Real.sqrt (primeAt i : Real))
    (primeLogWeight_nonneg 0) (Real.sqrt_nonneg _) primeLogWeight_monotone hb n
    (by
      intro i hi hroot
      have hroot0 : 0 <= Real.sqrt (primeAt i : Real) := Real.sqrt_nonneg _
      have hmass0 : 0 <= clockDeletedMass primeClockError primeLogWeight i :=
        hroot0.trans hroot
      have hproduct := mul_nonneg (sub_nonneg.mpr hroot)
        (add_nonneg hmass0 hroot0)
      have hsquare := Real.sq_sqrt (Nat.cast_nonneg (primeAt i) : (0 : Real) <= _)
      apply hquiet i hi
      nlinarith only [hproduct, hsquare])
  have hrecord := clockDeletedMass_record_bounds primeClockError primeLogWeight
    (primeLogWeight_nonneg 0) primeLogWeight_monotone primeClockError_initial
    primeClockError_increment (n + 1)
  have herror := (clockRecord_contains primeClockError n).trans hrecord.1
  have htheta : primeClockError n =
      Chebyshev.theta (primeAt n : Real) - (primeAt n : Real) := by
    rw [primeClockError_eq_theta, primeClassTheta_univ_eq_chebyshev]
  rw [htheta] at herror
  change clockDeletedMass primeClockError primeLogWeight (n + 1) <=
    Real.sqrt (primeAt n : Real) + Real.log (primeAt n : Real) at hbound
  exact herror.trans hbound

/-- A crest above the constant root envelope forces an actual rejected
pre-prime frame whose own square horizon already contains that rejection.
The witness lies in the same finite prefix. -/
theorem primeClock_square_horizon_failure_of_large_crest
    (n : Nat)
    (hcrest : Real.sqrt (primeAt n : Real) + Real.log (primeAt n : Real) <
      Chebyshev.theta (primeAt n : Real) - (primeAt n : Real)) :
    exists i : Nat, And (i <= n)
      (And ((primeAt i : Real) <=
        (clockDeletedMass primeClockError primeLogWeight i) ^ 2)
        (clockDeletedMass primeClockError primeLogWeight i < primeClockError i)) := by
  classical
  by_contra hnone
  have hquiet : forall i : Nat, i <= n ->
      (primeAt i : Real) <= (clockDeletedMass primeClockError primeLogWeight i) ^ 2 ->
      primeClockError i <= clockDeletedMass primeClockError primeLogWeight i := by
    intro i hi hsquare
    apply le_of_not_gt
    intro hreject
    exact hnone (Exists.intro i (And.intro hi (And.intro hsquare hreject)))
  have hbound := primeClock_square_horizon_forces_root_bound n hquiet
  exact (not_lt_of_ge hbound) hcrest

/-- The actual retained class contributes nonnegative headroom, but
the complete deleted mass must be subtracted from its signed readout. -/
theorem primeWave_square_retained_decomposition (N : Nat) :
    Finset.sum (Finset.range N)
      (fun j => (1 - Real.log ((j + 1 : Nat) : Real) +
          primeReturnLogWeight (j + 1)) ^ 2 -
        (primeWaveBirth (j + 1)) ^ 2 + 1) =
      2 * ((N : Real) - primeClassTheta greedyPrimeClass N) -
        2 * primeClassTheta greedyDeletedPrimeClass N := by
  rw [primeWave_compensated_square_readout]
  have hpartition := greedyPrimeClass_theta_partition N
  rw [primeClassTheta_univ_eq_chebyshev] at hpartition
  unfold primeWaveHeadroom
  linarith only [hpartition]

/-- Freezing the deletion mass requires more than nonnegative retained
headroom: that headroom must pay for every subsequent deletion. -/
theorem primeWave_square_frozen_bound_iff (N : Nat) (h : Real) :
    (-2 * h <= Finset.sum (Finset.range N)
      (fun j => (1 - Real.log ((j + 1 : Nat) : Real) +
          primeReturnLogWeight (j + 1)) ^ 2 -
        (primeWaveBirth (j + 1)) ^ 2 + 1)) <->
      primeClassTheta greedyDeletedPrimeClass N - h <=
        (N : Real) - primeClassTheta greedyPrimeClass N := by
  rw [primeWave_square_retained_decomposition]
  constructor <;> intro hbound <;> linarith only [hbound]

/-- A large crest produces a failure of the full signed square bound,
with every return and the birth diagonal still present in its statement. -/
theorem primeWave_square_failure_of_large_crest
    (n : Nat)
    (hcrest : Real.sqrt (primeAt n : Real) + Real.log (primeAt n : Real) <
      Chebyshev.theta (primeAt n : Real) - (primeAt n : Real)) :
    exists i : Nat, And (i <= n)
      (And ((primeAt i : Real) <=
        (clockDeletedMass primeClockError primeLogWeight i) ^ 2)
        (Finset.sum (Finset.range (primeAt i))
          (fun j => (1 - Real.log ((j + 1 : Nat) : Real) +
              primeReturnLogWeight (j + 1)) ^ 2 -
            (primeWaveBirth (j + 1)) ^ 2 + 1) <
          -2 * clockDeletedMass primeClockError primeLogWeight i)) := by
  choose i hi using primeClock_square_horizon_failure_of_large_crest n hcrest
  refine Exists.intro i (And.intro hi.1 (And.intro hi.2.1 ?_))
  rw [primeWave_compensated_square_readout]
  have hbad := hi.2.2
  rw [primeClockError_eq_theta, primeClassTheta_univ_eq_chebyshev] at hbad
  unfold primeWaveHeadroom
  linarith only [hbad]

end PrimeFactorOscillations.PrimeClassDeletion


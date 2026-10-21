/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import Mathlib.MeasureTheory.Integral.Bochner.SumMeasure
import Mathlib.Tactic.Linarith
import PrimeFactorOscillations.Helpers.Robin1984.NicolasLandau.NicolasLandauFrontier

/-!
# Positive discrete transforms and analytic continuation

This converts the existing nonnegative exponential-transform continuation
principle into an explicit summability statement for positive discrete
coefficients. The prime-class deletion consumer uses log-integer locations
and a fixed absolutely summable Dirichlet anchor.
-/

set_option autoImplicit false
set_option Elab.async false

namespace PrimeFactorOscillations.PrimeClassDeletion

open Filter MeasureTheory ProbabilityTheory Set
open scoped ENNReal Topology

noncomputable section

def weightedAtomicMeasure (w : Nat -> Real) : Measure Nat :=
  Measure.sum (fun n => HSMul.hSMul (ENNReal.ofReal (w n)) (Measure.dirac n))

theorem integrable_exp_weightedAtomic_iff
    (w x : Nat -> Real) (hw : forall n, 0 <= w n) (t : Real) :
    Integrable (fun n => Real.exp (t * x n)) (weightedAtomicMeasure w) <->
      Summable (fun n => w n * Real.exp (t * x n)) := by
  have hc : forall n, Not (ENNReal.ofReal (w n) = Top.top) :=
    fun n => ENNReal.ofReal_ne_top
  simpa [weightedAtomicMeasure, ENNReal.toReal_ofReal, hw, Real.norm_eq_abs] using
    (integrable_sum_dirac_iff
      (x := fun n : Nat => n) (c := fun n => ENNReal.ofReal (w n))
      (f := fun n => Real.exp (t * x n)) hc)

theorem mgf_weightedAtomic_eq_tsum
    (w x : Nat -> Real) (hw : forall n, 0 <= w n) (t : Real) :
    mgf x (weightedAtomicMeasure w) t =
      tsum (fun n => w n * Real.exp (t * x n)) := by
  have hc : forall n, Not (ENNReal.ofReal (w n) = Top.top) :=
    fun n => ENNReal.ofReal_ne_top
  simpa [mgf, weightedAtomicMeasure, ENNReal.toReal_ofReal, hw, smul_eq_mul] using
    (integral_sum_dirac
      (x := fun n : Nat => n) (c := fun n => ENNReal.ofReal (w n))
      (f := fun n => Real.exp (t * x n)) hc)

/-- A regular continuation of a positive discrete transform forces actual summability. -/
theorem summable_exp_of_analyticContinuation
    (w x : Nat -> Real) (hw : forall n, 0 <= w n)
    (hSum : Summable w) (hx : forall n, 0 <= x n)
    {b : Real} {H : Real -> Real}
    (hH : forall t : Real, t < b -> AnalyticAt Real H t)
    (hEq : forall t : Real, t < 0 ->
      tsum (fun n => w n * Real.exp (t * x n)) = H t)
    (t : Real) (ht : t < b) :
    Summable (fun n => w n * Real.exp (t * x n)) := by
  let mu := weightedAtomicMeasure w
  have hNonpos : forall a : Real, a < 0 ->
      Integrable (fun n => Real.exp (a * x n)) mu := by
    intro a ha
    apply (integrable_exp_weightedAtomic_iff w x hw a).mpr
    apply Summable.of_nonneg_of_le
      (fun n => mul_nonneg (hw n) (Real.exp_nonneg _)) _ hSum
    intro n
    have he : Real.exp (a * x n) <= 1 := by
      apply Real.exp_le_one_iff.mpr
      exact mul_nonpos_of_nonpos_of_nonneg (le_of_lt ha) (hx n)
    simpa only [mul_one] using mul_le_mul_of_nonneg_left he (hw n)
  have hNeg : forall a : Real, a < 0 ->
      Membership.mem (interior (integrableExpSet x mu)) a := by
    intro a ha
    rw [mem_interior_iff_mem_nhds]
    apply Filter.mem_of_superset (Iio_mem_nhds ha)
    intro y hy
    change Integrable (fun n => Real.exp (y * x n)) mu
    exact hNonpos y hy
  have hX : Filter.Eventually (fun n => 0 <= x n) (ae mu) :=
    Filter.Eventually.of_forall hx
  have hEqNeg : forall a : Real, a < 0 -> mgf x mu a = H a := by
    intro a ha
    exact (mgf_weightedAtomic_eq_tsum w x hw a).trans (hEq a ha)
  have hFront :=
    Robin1984.Iio_subset_interior_integrableExpSet_of_analyticContinuation
      hX hNeg hH hEqNeg
  have hi := interior_subset (hFront ht)
  change Integrable (fun n => Real.exp (t * x n)) mu at hi
  exact (integrable_exp_weightedAtomic_iff w x hw t).mp hi

def positiveDirichletTerm (a : Nat -> Real) (s : Real) (n : Nat) : Real :=
  a n * ((n + 1 : Nat) : Real) ^ (-s)

theorem positiveDirichletTerm_exp_shift (a : Nat -> Real) (c t : Real) (n : Nat) :
    positiveDirichletTerm a c n *
        Real.exp (t * Real.log ((n + 1 : Nat) : Real)) =
      positiveDirichletTerm a (c - t) n := by
  have hp : 0 < ((n + 1 : Nat) : Real) :=
    Nat.cast_pos.mpr (Nat.zero_lt_succ n)
  have he : -c + t = -(c - t) := by linarith
  unfold positiveDirichletTerm
  calc
    a n * ((n + 1 : Nat) : Real) ^ (-c) *
        Real.exp (t * Real.log ((n + 1 : Nat) : Real)) =
      a n * (((n + 1 : Nat) : Real) ^ (-c) *
        ((n + 1 : Nat) : Real) ^ t) := by
          rw [Real.rpow_def_of_pos hp t]
          rw [mul_comm (Real.log ((n + 1 : Nat) : Real)) t]
          exact mul_assoc _ _ _
    _ = a n * ((n + 1 : Nat) : Real) ^ (-c + t) := by
      rw [Real.rpow_add hp]
    _ = a n * ((n + 1 : Nat) : Real) ^ (-(c - t)) := by rw [he]

/-- Positive Dirichlet coefficients cannot converge only to the right of a regular continuation. -/
theorem summable_positiveDirichlet_of_analyticContinuation
    (a : Nat -> Real) (ha : forall n, 0 <= a n) (c alpha : Real)
    (hAnchor : Summable (positiveDirichletTerm a c))
    {F : Real -> Real}
    (hF : forall sigma : Real, alpha < sigma -> AnalyticAt Real F sigma)
    (hEq : forall sigma : Real, c < sigma ->
      tsum (positiveDirichletTerm a sigma) = F sigma)
    (sigma : Real) (hSigma : alpha < sigma) :
    Summable (positiveDirichletTerm a sigma) := by
  let w := positiveDirichletTerm a c
  let x := fun n : Nat => Real.log ((n + 1 : Nat) : Real)
  let H := fun t : Real => F (c - t)
  have hw : forall n, 0 <= w n := by
    intro n
    exact mul_nonneg (ha n) (Real.rpow_nonneg (Nat.cast_nonneg _) _)
  have hx : forall n, 0 <= x n := fun n => Real.log_natCast_nonneg (n + 1)
  have hH : forall t : Real, t < c - alpha -> AnalyticAt Real H t := by
    intro t ht
    have hReg := hF (c - t) (by linarith)
    have hLinear : AnalyticAt Real (fun y : Real => c - y) t :=
      analyticAt_const.sub analyticAt_id
    exact hReg.comp hLinear
  have hEqH : forall t : Real, t < 0 ->
      tsum (fun n => w n * Real.exp (t * x n)) = H t := by
    intro t ht
    calc
      tsum (fun n => w n * Real.exp (t * x n)) =
          tsum (positiveDirichletTerm a (c - t)) :=
        tsum_congr (fun n => positiveDirichletTerm_exp_shift a c t n)
      _ = H t := hEq (c - t) (by linarith)
  have hs := summable_exp_of_analyticContinuation w x hw hAnchor hx
    hH hEqH (c - sigma) (by linarith)
  apply hs.congr
  intro n
  have he : c - (c - sigma) = sigma := by linarith
  simpa only [he] using positiveDirichletTerm_exp_shift a c (c - sigma) n

end

end PrimeFactorOscillations.PrimeClassDeletion

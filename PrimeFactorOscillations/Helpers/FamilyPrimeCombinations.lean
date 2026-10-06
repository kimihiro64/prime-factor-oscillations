/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.QuadraticPrimeCriterion

/-!
# Finite combinations of different family profiles

Every fixed finite combination retains one explicit multiple of the Nicolas
signal. Canceling that coefficient leaves an inverse-cutoff remainder. No
uniformity over growing or infinite collections is asserted.
-/

set_option autoImplicit false
set_option Elab.async false

namespace PrimeFactorOscillations

open Filter Robin1984

theorem family_log_combination_bound {I : Type*} (s : Finset I)
    (laws : I -> QuadraticPrimeLaw) (a z : I -> Real)
    (hz : forall i, Membership.mem s i -> 0 <= z i)
    (N : Nat) (hN : 1 <= N) (hTheta : 1 < Chebyshev.theta (N : Real)) :
    abs (s.sum (fun i => a i * (laws i).logError N (z i)) -
      (s.sum (fun i => a i * ((laws i).nu * z i))) * nicolasLogMertensOscillation (N : Real)) <=
      (s.sum (fun i => abs (a i) * (2 * (laws i).logTailConstant (z i)))) / N := by
  classical
  have hBound : forall i, Membership.mem s i ->
      abs (a i * ((laws i).logError N (z i) -
        (laws i).nu * z i * nicolasLogMertensOscillation (N : Real))) <=
      abs (a i) * (2 * (laws i).logTailConstant (z i) / N) := by
    intro i hi
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_left ((laws i).logError_bound N hN (z i) (hz i hi) hTheta)
      (abs_nonneg _)
  have hEq : s.sum (fun i => a i * ((laws i).logError N (z i) -
      (laws i).nu * z i * nicolasLogMertensOscillation (N : Real))) =
      s.sum (fun i => a i * (laws i).logError N (z i)) -
        (s.sum (fun i => a i * ((laws i).nu * z i))) *
          nicolasLogMertensOscillation (N : Real) := by
    calc
      _ = s.sum (fun i => a i * (laws i).logError N (z i) -
          (a i * ((laws i).nu * z i)) * nicolasLogMertensOscillation (N : Real)) := by
        apply Finset.sum_congr rfl
        intro i _
        ring
      _ = _ := by rw [Finset.sum_sub_distrib, Finset.sum_mul]
  rw [<- hEq]
  calc
    _ <= s.sum (fun i => abs (a i * ((laws i).logError N (z i) -
        (laws i).nu * z i * nicolasLogMertensOscillation (N : Real)))) :=
      Finset.abs_sum_le_sum_abs _ _
    _ <= s.sum (fun i => abs (a i) * (2 * (laws i).logTailConstant (z i) / N)) :=
      Finset.sum_le_sum hBound
    _ = _ := by simp only [mul_div_assoc, Finset.sum_div]

theorem family_log_combination_bound_of_cancelled {I : Type*} (s : Finset I)
    (laws : I -> QuadraticPrimeLaw) (a z : I -> Real)
    (hz : forall i, Membership.mem s i -> 0 <= z i)
    (hCancel : s.sum (fun i => a i * ((laws i).nu * z i)) = 0)
    (N : Nat) (hN : 1 <= N) (hTheta : 1 < Chebyshev.theta (N : Real)) :
    abs (s.sum (fun i => a i * (laws i).logError N (z i))) <=
      (s.sum (fun i => abs (a i) * (2 * (laws i).logTailConstant (z i)))) / N := by
  simpa only [hCancel, zero_mul, sub_zero] using family_log_combination_bound s laws a z hz N hN hTheta

theorem riemannHypothesis_iff_eventually_family_log_combination_neg
    {I : Type*} (s : Finset I) (laws : I -> QuadraticPrimeLaw) (a z : I -> Real)
    (hz : forall i, Membership.mem s i -> 0 <= z i)
    (hSignal : 0 < s.sum (fun i => a i * ((laws i).nu * z i))) :
    RiemannHypothesis <-> Filter.Eventually (fun N : Nat =>
      s.sum (fun i => a i * (laws i).logError N (z i)) < 0) atTop := by
  let C := s.sum (fun i => abs (a i) * (2 * (laws i).logTailConstant (z i)))
  have hC : 0 <= C := Finset.sum_nonneg (fun i hi => mul_nonneg (abs_nonneg _)
    (mul_nonneg (by norm_num) ((laws i).logTailConstant_nonneg (z i) (hz i hi))))
  apply riemannHypothesis_iff_eventually_familyError_neg _
    (s.sum (fun i => a i * ((laws i).nu * z i))) C hSignal hC
  filter_upwards [eventually_ge_atTop (1 : Nat),
    tendsto_primeProfile_theta_atTop.eventually_gt_atTop (1 : Real)] with N hN hTheta
  have h := family_log_combination_bound s laws a z hz N hN hTheta
  have hExtra : 0 <= s.sum (fun i => a i * ((laws i).nu * z i)) / 2 *
      abs (nicolasLogMertensOscillation (N : Real)) := by positivity
  exact h.trans (by change C / (N : Real) <= _; linarith only [hExtra])

end PrimeFactorOscillations

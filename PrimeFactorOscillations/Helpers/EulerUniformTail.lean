/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.EulerRealHalfIntegerBounds

/-! # A height-independent tail for a finite signed Euler packet -/

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 5000000

noncomputable section
namespace PrimeFactorOscillations

open MeasureTheory
open scoped Interval Topology BigOperators ComplexOrder

def eulerUniformTail (N : Nat) : Real :=
  ((2 / 3) * Real.log (N : Real) + 4 / 9) / ((N : Real) * Real.sqrt (N : Real))

theorem eulerUniformTail_eq_primitive (N : Nat) :
    eulerUniformTail N = -eulerLogPrimitive (N : Real) := by
  rw [eulerUniformTail, eulerLogPrimitive, neg_neg,
    eulerThreeHalfPower_eq (N : Real) (Nat.cast_nonneg N)]
  ring

theorem eulerLogProfile_summable : Summable (fun n : Nat => eulerLogProfile n) := by
  have hlog := LSeriesSummable_logMul_of_lt_re
    (f := (1 : Nat -> Complex)) (s := (5 / 2 : Complex))
    (by rw [LSeries.abscissaOfAbsConv_one]; norm_num;
        exact_mod_cast (by norm_num : (1 : Real) < 5 / 2))
  have hcoeff : LSeries.logMul (1 : Nat -> Complex) = (fun n : Nat => Complex.log n) := by
    funext n
    simp [LSeries.logMul]
  rw [hcoeff] at hlog
  exact hlog.norm.congr eulerLogProfile_term_norm

theorem eulerLogProfile_sum_tail_from (N M : Nat) (hN : 6 <= N) :
    Finset.sum (Finset.range M) (fun n : Nat => eulerLogProfile (n + (N + 1) : Nat)) <=
      -eulerLogPrimitive (N : Real) := by
  have hNr : (6 : Real) <= (N : Real) := by exact_mod_cast hN
  have hNpos : 0 < (N : Real) := by linarith only [hNr]
  have ha : AntitoneOn eulerLogProfile (Set.Icc (N : Real) ((N : Real) + (M : Real))) :=
    eulerLogProfile_antitone.mono (fun _ hx => le_trans hNr hx.1)
  have hc := ha.sum_le_integral
  have hNM : (N : Real) <= (N : Real) + (M : Real) := by
    have hm : (0 : Real) <= (M : Real) := Nat.cast_nonneg M
    linarith only [hm]
  have hd : forall x : Real,
      Membership.mem (Set.uIcc (N : Real) ((N : Real) + (M : Real))) x ->
      HasDerivAt eulerLogPrimitive (eulerLogProfile x) x := by
    intro x hx
    have hh : And ((N : Real) <= x) (x <= (N : Real) + (M : Real)) := by
      simpa only [Set.uIcc_of_le hNM, Set.mem_Icc] using hx
    exact eulerLogPrimitive_hasDerivAt x (by linarith only [hh.1, hNpos])
  have hi : IntervalIntegrable eulerLogProfile volume (N : Real) ((N : Real) + (M : Real)) := by
    apply ContinuousOn.intervalIntegrable
    intro x hx
    have hh : And ((N : Real) <= x) (x <= (N : Real) + (M : Real)) := by
      simpa only [Set.uIcc_of_le hNM, Set.mem_Icc] using hx
    exact (eulerLogProfile_hasDerivAt x (by linarith only [hh.1, hNpos])).continuousAt.continuousWithinAt
  have hv := intervalIntegral.integral_eq_sub_of_hasDerivAt hd hi
  have hn : eulerLogPrimitive ((N : Real) + (M : Real)) <= 0 := by
    dsimp only [eulerLogPrimitive]
    have hl : 0 <= Real.log ((N : Real) + (M : Real)) :=
      Real.log_nonneg (by linarith only [hNr, hNM])
    have hp := Real.rpow_nonneg (by linarith only [hNpos, hNM] :
      (0 : Real) <= (N : Real) + (M : Real)) (-(3 / 2) : Real)
    nlinarith only [hl, hp]
  rw [hv] at hc
  have hsum : Finset.sum (Finset.range M)
      (fun n : Nat => eulerLogProfile (n + (N + 1) : Nat)) =
      Finset.sum (Finset.range M)
        (fun n : Nat => eulerLogProfile ((N : Real) + ((n + 1 : Nat) : Real))) := by
    apply Finset.sum_congr rfl
    intro n _
    congr 1
    push_cast
    ring
  rw [hsum]
  linarith only [hc, hn]

theorem eulerLogProfile_tsum_tail_from (N : Nat) (hN : 6 <= N) :
    tsum (fun n : Nat => eulerLogProfile (n + (N + 1) : Nat)) <= eulerUniformTail N := by
  have ht : Summable (fun n : Nat => eulerLogProfile (n + (N + 1) : Nat)) :=
    eulerLogProfile_summable.comp_injective (fun _ _ h => Nat.add_right_cancel h)
  rw [eulerUniformTail_eq_primitive]
  exact le_of_tendsto ht.hasSum.tendsto_sum_nat
    (Filter.Eventually.of_forall (fun M => eulerLogProfile_sum_tail_from N M hN))

theorem eulerUniformTail_hundred : eulerUniformTail 100 < 1 / 250 := by
  have h5 := Real.log_le_sub_one_of_pos (by norm_num : (0 : Real) < 5 / 6)
  rw [Real.log_div (by norm_num) (by norm_num)] at h5
  have h6 : Real.log 6 < 9 / 5 := by
    rw [show (6 : Real) = 2 * 3 by norm_num, Real.log_mul (by norm_num) (by norm_num)]
    linarith only [Real.log_two_lt_d9, Real.log_three_lt_d9]
  have h2 := Real.log_two_lt_d9
  have he10 : Real.log 10 = Real.log 2 + Real.log 5 := by
    rw [show (10 : Real) = 2 * 5 by norm_num, Real.log_mul (by norm_num) (by norm_num)]
  have he100 : Real.log 100 = 2 * Real.log 10 := by
    rw [show (100 : Real) = 10 ^ (2 : Nat) by norm_num, Real.log_pow]
    norm_num
  have hl : Real.log 100 < 5 := by linarith only [h5, h6, h2, he10, he100]
  have hs : Real.sqrt (100 : Real) = 10 := by
    nlinarith only [Real.sq_sqrt (by norm_num : (0 : Real) <= 100),
      Real.sqrt_nonneg (100 : Real)]
  dsimp only [eulerUniformTail]
  norm_num only [Nat.cast_ofNat]
  rw [hs]
  linarith only [hl]

end PrimeFactorOscillations

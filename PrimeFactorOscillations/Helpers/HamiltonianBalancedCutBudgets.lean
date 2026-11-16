/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.HamiltonianActualCutScaling
import PrimeFactorOscillations.Helpers.HamiltonianLogMomentChoice

/-! # One explicit log-fifth budget discharges all actual cut-repair losses

The constants depend only on the fixed gap and requested failure exponent.
The complete entry-cap range is retained; no bound on N times the cap is
assumed beyond the necessary probability-row lower bound.
-/

set_option autoImplicit false
set_option Elab.async false

noncomputable section

namespace PrimeFactorOscillations

def hamiltonianBalancedCutAllowance (delta : Real) : Real :=
  min (delta / 128)
    (min (hamiltonianNormalizedScalingSmall (delta / 2) / 8)
      (delta / (16 * (hamiltonianNormalizedScalingCost (delta / 2) + 1))))

def hamiltonianBalancedCutBudget (delta A : Real) : Real :=
  hamiltonianBalancedCutAllowance delta ^ 2 / (8 * (A + 6))

theorem hamiltonian_balanced_cut_allowance_positive
    (delta : Real) (hd0 : 0 < delta) (hd1 : delta <= 1) :
    0 < hamiltonianBalancedCutAllowance delta := by
  have hC := hamiltonian_normalized_scaling_constants_positive (delta / 2)
    (by linarith only [hd0]) (by linarith only [hd1])
  have hS : 0 < hamiltonianNormalizedScalingSmall (delta / 2) := hC.1
  have hK : 0 < hamiltonianNormalizedScalingCost (delta / 2) := hC.2
  exact lt_min (by positivity) (lt_min (by positivity) (by positivity))

theorem hamiltonian_balanced_cut_budget_positive
    (delta A : Real) (hd0 : 0 < delta) (hd1 : delta <= 1) (hA : 0 < A) :
    0 < hamiltonianBalancedCutBudget delta A := by
  have h := hamiltonian_balanced_cut_allowance_positive delta hd0 hd1
  unfold hamiltonianBalancedCutBudget
  positivity

theorem hamiltonian_balanced_cut_all_budgets
    (n alpha A delta : Real) (hn : 2 <= n) (ha0 : 0 <= alpha) (ha1 : alpha <= 1)
    (hMass : 1 <= n * alpha) (hA : 0 < A) (hd0 : 0 < delta) (hd1 : delta <= 1)
    (hBudget : alpha * Real.log (2 * n) ^ 5 <= hamiltonianBalancedCutBudget delta A) :
    let eps := Real.sqrt (8 * (A + 6) * alpha * Real.log (2 * n))
    Real.sqrt (2 * (A + 6) * alpha * Real.log (2 * n)) <= delta / 128 /\
      64 * eps <= delta /\
      eps <= 1 / 2 /\
      eps * Real.log (4 * (n * alpha)) ^ 2 <=
        hamiltonianNormalizedScalingSmall (delta / 2) /\
      hamiltonianNormalizedScalingCost (delta / 2) *
        eps * Real.log (4 * (n * alpha)) <= delta / 4 := by
  let L := Real.log (2 * n)
  let ell := Real.log (4 * (n * alpha))
  let eps := Real.sqrt (8 * (A + 6) * alpha * L)
  let eta := hamiltonianBalancedCutAllowance delta
  let K := hamiltonianNormalizedScalingCost (delta / 2)
  let S := hamiltonianNormalizedScalingSmall (delta / 2)
  have hn0 : 0 <= n := by linarith only [hn]
  have hL : 1 <= L := hamiltonian_log_four_lower.trans
    (Real.log_le_log (by norm_num) (by linarith only [hn]))
  have hL0 : 0 <= L := by linarith only [hL]
  have hell0 : 0 <= ell := Real.log_nonneg (by linarith only [hMass])
  have hC := hamiltonian_normalized_scaling_constants_positive (delta / 2)
    (by linarith only [hd0]) (by linarith only [hd1])
  have hK : 0 < K := hC.2
  have hS : 0 < S := hC.1
  have hEta : 0 < eta := hamiltonian_balanced_cut_allowance_positive delta hd0 hd1
  have he : 0 <= eps := Real.sqrt_nonneg _
  have hRad : 0 <= 8 * (A + 6) * alpha * L := by positivity
  have heSq : eps ^ 2 = 8 * (A + 6) * alpha * L := Real.sq_sqrt hRad
  have hDen : 0 < 8 * (A + 6) := by linarith only [hA]
  have hBudgetScaled : (alpha * L ^ 5) * (8 * (A + 6)) <= eta ^ 2 := by
    have h := mul_le_mul_of_nonneg_right hBudget hDen.le
    have hCancel : (eta ^ 2 / (8 * (A + 6))) * (8 * (A + 6)) = eta ^ 2 := by
      field_simp [ne_of_gt hDen]
    exact h.trans_eq hCancel
  have hSquare : (eps * L ^ 2) ^ 2 = 8 * (A + 6) * (alpha * L ^ 5) := by
    rw [mul_pow, heSq]
    ring
  have hWeighted : eps * L ^ 2 <= eta := by
    nlinarith only [hSquare, hBudgetScaled, hEta, mul_nonneg he (sq_nonneg L)]
  have hEtaDelta : eta <= delta / 128 := min_le_left _ _
  have hEtaSmall : eta <= S / 8 := (min_le_right _ _).trans (min_le_left _ _)
  have hEtaCost : eta <= delta / (16 * (K + 1)) :=
    (min_le_right _ _).trans (min_le_right _ _)
  have hEtaCostDen : 0 < 16 * (K + 1) := by linarith only [hK]
  have hEtaCostScaled : eta * (16 * (K + 1)) <= delta := by
    have h := mul_le_mul_of_nonneg_right hEtaCost hEtaCostDen.le
    have hCancel : (delta / (16 * (K + 1))) * (16 * (K + 1)) = delta := by
      field_simp [ne_of_gt hEtaCostDen]
    exact h.trans_eq hCancel
  have hL2 : 1 <= L ^ 2 := by nlinarith only [hL]
  have heWeighted : eps <= eps * L ^ 2 := by
    simpa only [mul_one] using mul_le_mul_of_nonneg_left hL2 he
  have heEta : eps <= eta := heWeighted.trans hWeighted
  have hCov : Real.sqrt (2 * (A + 6) * alpha * L) <= eps := by
    apply Real.sqrt_le_sqrt
    have hBase : 0 <= (A + 6) * alpha * L := by positivity
    nlinarith only [hBase]
  have hMargin : 64 * eps <= delta := by
    linarith only [heEta, hEtaDelta, hd0]
  have heHalf : eps <= 1 / 2 := by
    linarith only [heEta, hEtaDelta, hd1]
  have hNA : n * alpha <= n := by
    simpa only [mul_one] using mul_le_mul_of_nonneg_left ha1 hn0
  have hNN : n <= n ^ 2 := by nlinarith only [hn]
  have hLogArg : 4 * (n * alpha) <= (2 * n) ^ 2 := by
    nlinarith only [hNA, hNN]
  have hLog := Real.log_le_log (by linarith only [hMass] : 0 < 4 * (n * alpha)) hLogArg
  rw [Real.log_pow] at hLog
  have hell : ell <= 2 * L := by
    simpa only [Nat.cast_ofNat] using hLog
  have hellSquare : ell ^ 2 <= 4 * L ^ 2 := by
    nlinarith only [hell, hell0, hL0]
  have hSmallScaled := mul_le_mul_of_nonneg_left hellSquare he
  have hSmall : eps * ell ^ 2 <= S := by
    nlinarith only [hSmallScaled, hWeighted, hEtaSmall, hS]
  have hLL : L <= L ^ 2 := by nlinarith only [hL]
  have hEL := mul_le_mul_of_nonneg_left hLL he
  have hCost1 := mul_le_mul_of_nonneg_left hell (mul_nonneg hK.le he)
  have hCost2 := mul_le_mul_of_nonneg_left hEL hK.le
  have hCost3 := mul_le_mul_of_nonneg_left hWeighted hK.le
  have hKEta : 0 <= K * eta := mul_nonneg hK.le hEta.le
  have hCost : K * eps * ell <= delta / 4 := by
    nlinarith only [hCost1, hCost2, hCost3, hEtaCostScaled, hEta.le, hKEta]
  exact And.intro (hCov.trans (heEta.trans hEtaDelta))
    (And.intro hMargin (And.intro heHalf (And.intro hSmall hCost)))

end PrimeFactorOscillations

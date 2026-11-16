/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.HamiltonianDiffuseJacobianInverse

/-! # Dimension-only constants for normalized spectral scaling -/

set_option autoImplicit false
set_option Elab.async false

noncomputable section

namespace PrimeFactorOscillations

def hamiltonianScalingOrderCost (rho : Real) : Real :=
  4 / (-Real.log rho) + (6 + 1 / (1 - rho)) / Real.log 4

def hamiltonianScalingOrderSmall (rho : Real) : Real :=
  min (((1 - rho) / 14) * (Real.log 4) ^ 2)
    (1 / (256 * hamiltonianScalingOrderCost rho ^ 2))

theorem hamiltonian_scaling_order_cost_positive (rho : Real)
    (hr0 : 0 < rho) (hr1 : rho < 1) :
    0 < hamiltonianScalingOrderCost rho := by
  have hDen : 0 < -Real.log rho := neg_pos.mpr (Real.log_neg hr0 hr1)
  have hFour : 0 < Real.log 4 := Real.log_pos (by norm_num)
  have hGap : 0 < 1 - rho := sub_pos.mpr hr1
  unfold hamiltonianScalingOrderCost
  positivity

theorem hamiltonian_scaling_order_small_positive (rho : Real)
    (hr0 : 0 < rho) (hr1 : rho < 1) :
    0 < hamiltonianScalingOrderSmall rho := by
  have hG := hamiltonian_scaling_order_cost_positive rho hr0 hr1
  have hFour : 0 < Real.log 4 := Real.log_pos (by norm_num)
  have hGap : 0 < 1 - rho := sub_pos.mpr hr1
  unfold hamiltonianScalingOrderSmall
  apply lt_min <;> positivity

theorem hamiltonian_diffuse_inverse_order_bound
    (n a eps rho : Real) (hn : 1 <= n) (ha : 1 <= a)
    (he0 : 0 <= eps) (he1 : eps <= 1 / 2)
    (hA : a <= (1 + eps) * n) (hr0 : 0 < rho) (hr1 : rho < 1) :
    hamiltonianDiffuseInverseBudget (a + 9 * eps) rho <=
      hamiltonianScalingOrderCost rho * Real.log (4 * n) := by
  let L := Real.log (4 * n)
  let K := 6 + 1 / (1 - rho)
  have hDen : 0 < -Real.log rho := neg_pos.mpr (Real.log_neg hr0 hr1)
  have hFour : 0 < Real.log 4 := Real.log_pos (by norm_num)
  have hGap : 0 < 1 - rho := sub_pos.mpr hr1
  have hK : 0 <= K := by dsimp [K]; positivity
  have hL : Real.log 4 <= L :=
    Real.log_le_log (by norm_num) (by linarith only [hn])
  have hEN := mul_le_mul_of_nonneg_right he1 (by linarith only [hn] : 0 <= n)
  have hArg : 2 * (a + 9 * eps) <= 12 * n := by nlinarith only [hA, hEN, he1, hn]
  have hSquare : 12 * n <= (4 * n) ^ 2 := by nlinarith only [hn, sq_nonneg (n - 1)]
  have hLog := Real.log_le_log (by linarith only [ha, he0] : 0 < 2 * (a + 9 * eps))
    (hArg.trans hSquare)
  rw [Real.log_pow] at hLog
  change Real.log (2 * (a + 9 * eps)) <= 2 * L at hLog
  have hDiv := div_le_div_of_nonneg_right hLog hDen.le
  have hScale := mul_le_mul_of_nonneg_left hL
    (div_nonneg hK hFour.le)
  have hCancel : (K / Real.log 4) * Real.log 4 = K := by field_simp [ne_of_gt hFour]
  rw [hCancel] at hScale
  calc
    _ = 2 * (Real.log (2 * (a + 9 * eps)) / (-Real.log rho)) + K := by
      dsimp [hamiltonianDiffuseInverseBudget, K]
      ring
    _ <= 2 * ((2 * L) / (-Real.log rho)) + K := by linarith only [hDiv]
    _ = (4 * L) / (-Real.log rho) + K := by ring
    _ <= (4 * L) / (-Real.log rho) + (K / Real.log 4) * L := by linarith only [hScale]
    _ = hamiltonianScalingOrderCost rho * Real.log (4 * n) := by
      dsimp [hamiltonianScalingOrderCost, L, K]
      ring

theorem hamiltonian_scaling_order_all_budgets
    (n a eps rho : Real) (hn : 1 <= n) (ha : 1 <= a)
    (he0 : 0 <= eps) (he1 : eps <= 1 / 2)
    (hA : a <= (1 + eps) * n) (hr0 : 0 < rho) (hr1 : rho < 1)
    (hSmall : eps * Real.log (4 * n) ^ 2 <= hamiltonianScalingOrderSmall rho) :
    let g := hamiltonianDiffuseInverseBudget (a + 9 * eps) rho
    let R := 4 * g * eps
    (28 * eps <= 2 * (1 - rho)) /\
    (eps * g ^ 2 <= 1 / 256) /\
    (R <= 4 * hamiltonianScalingOrderCost rho * eps * Real.log (4 * n)) /\
    ((2 * R + R ^ 2) * (1 + eps) <=
      20 * hamiltonianScalingOrderCost rho * eps * Real.log (4 * n)) := by
  let L := Real.log (4 * n)
  let G := hamiltonianScalingOrderCost rho
  let g := hamiltonianDiffuseInverseBudget (a + 9 * eps) rho
  let R := 4 * g * eps
  have hFour : 0 < Real.log 4 := Real.log_pos (by norm_num)
  have hL : Real.log 4 <= L :=
    Real.log_le_log (by norm_num) (by linarith only [hn])
  have hL0 : 0 <= L := hFour.le.trans hL
  have hL2 : (Real.log 4) ^ 2 <= L ^ 2 := by nlinarith only [hL, hL0, hFour]
  have hG : 0 < G := hamiltonian_scaling_order_cost_positive rho hr0 hr1
  have hg : 1 <= g := hamiltonian_diffuse_inverse_budget_positive (a + 9 * eps) rho
    (by linarith only [ha, he0]) hr0 hr1
  have hg0 : 0 <= g := (by norm_num : (0 : Real) <= 1).trans hg
  have hGL0 : 0 <= G * L := mul_nonneg hG.le hL0
  have hBound : g <= G * L :=
    hamiltonian_diffuse_inverse_order_bound n a eps rho hn ha he0 he1 hA hr0 hr1
  have hScale := mul_le_mul_of_nonneg_left hL2 he0
  have hSmallGap : eps * (Real.log 4) ^ 2 <=
      ((1 - rho) / 14) * (Real.log 4) ^ 2 :=
    hScale.trans (hSmall.trans (min_le_left _ _))
  have hEps : eps <= (1 - rho) / 14 := by
    by_contra h
    have hStrict := mul_lt_mul_of_pos_right (lt_of_not_ge h)
      (sq_pos_of_pos hFour)
    exact (not_lt_of_ge hSmallGap) hStrict
  have hMargin : 28 * eps <= 2 * (1 - rho) := by linarith only [hEps]
  have hSmallSq : eps * L ^ 2 <= 1 / (256 * G ^ 2) :=
    hSmall.trans (min_le_right _ _)
  have hSquare := mul_le_mul hBound hBound hg0 hGL0
  have hBudget : eps * g ^ 2 <= 1 / 256 := by
    calc
      _ <= eps * (G * L) ^ 2 := by
        have h := mul_le_mul_of_nonneg_left hSquare he0
        simpa only [pow_two] using h
      _ = G ^ 2 * (eps * L ^ 2) := by ring
      _ <= G ^ 2 * (1 / (256 * G ^ 2)) :=
        mul_le_mul_of_nonneg_left hSmallSq (sq_nonneg G)
      _ = _ := by field_simp [ne_of_gt hG]
  have hRadius : R <= 4 * G * eps * L := by
    have h := mul_le_mul_of_nonneg_left hBound (by positivity : 0 <= 4 * eps)
    dsimp [R]
    nlinarith only [h]
  have hgSquare : g <= g ^ 2 := by nlinarith only [hg]
  have hProduct : eps * g <= 1 / 256 :=
    (mul_le_mul_of_nonneg_left hgSquare he0).trans hBudget
  have hR0 : 0 <= R := by dsimp [R]; positivity
  have hR1 : R <= 1 / 64 := by dsimp [R]; nlinarith only [hProduct]
  have hQuadratic : 2 * R + R ^ 2 <= 3 * R := by nlinarith only [hR0, hR1]
  have hOperator : (2 * R + R ^ 2) * (1 + eps) <= 5 * R := by
    calc
      _ <= (3 * R) * (3 / 2) := mul_le_mul hQuadratic
        (by linarith only [he1]) (by positivity) (by positivity)
      _ <= _ := by linarith only [hR0]
  refine And.intro hMargin (And.intro hBudget (And.intro hRadius ?_))
  calc
    _ <= 5 * R := hOperator
    _ <= 5 * (4 * G * eps * L) := mul_le_mul_of_nonneg_left hRadius (by norm_num)
    _ = _ := by ring

end PrimeFactorOscillations

/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.HamiltonianDiffuseScaling
import PrimeFactorOscillations.Helpers.HamiltonianPrimeCrossBlock

/-! # The repair smallness window at the actual logarithmic prime density -/

set_option autoImplicit false
set_option Elab.async false

open scoped Matrix.Norms.L2Operator

noncomputable section

namespace PrimeFactorOscillations

def hamiltonianPrimeScalingLogConstant : Real :=
  2 / (-Real.log (2 / 3 : Real)) * (1 + Real.log 2) + 9

theorem hamiltonian_prime_scaling_log_constant_positive :
    0 < hamiltonianPrimeScalingLogConstant := by
  have hd : 0 < -Real.log (2 / 3 : Real) := by
    have h := Real.log_neg (by norm_num : (0 : Real) < 2 / 3)
      (by norm_num : (2 / 3 : Real) < 1)
    linarith only [h]
  have h2 : 0 <= Real.log (2 : Real) := Real.log_nonneg (by norm_num)
  unfold hamiltonianPrimeScalingLogConstant
  positivity

theorem hamiltonian_prime_scaling_log_budget (L eps : Real)
    (hL : 64 <= L) (hLog : 1 <= Real.log L)
    (hEps : 0 < eps) (hSmall : eps <= 1 / 100) :
    hamiltonianDiffuseInverseBudget (L / 2 + 9 * eps) (2 / 3) <=
      hamiltonianPrimeScalingLogConstant * Real.log L := by
  let d := -Real.log (2 / 3 : Real)
  have hd : 0 < d := by
    have h := Real.log_neg (by norm_num : (0 : Real) < 2 / 3)
      (by norm_num : (2 / 3 : Real) < 1)
    dsimp only [d]
    linarith only [h]
  have h2 : 0 <= Real.log (2 : Real) := Real.log_nonneg (by norm_num)
  have hArg : 2 * (L / 2 + 9 * eps) <= 2 * L := by linarith only [hL, hSmall]
  have hPos : 0 < 2 * (L / 2 + 9 * eps) := by linarith only [hL, hEps]
  have hLogs : Real.log (2 * (L / 2 + 9 * eps)) <= Real.log 2 + Real.log L := by
    have h := Real.log_le_log hPos hArg
    rwa [Real.log_mul (by norm_num : Not ((2 : Real) = 0))
      (ne_of_gt (by linarith only [hL] : 0 < L))] at h
  have hDivide := div_le_div_of_nonneg_right hLogs hd.le
  have hCoeff : 0 <= 2 / d * Real.log 2 := mul_nonneg (div_nonneg (by norm_num) hd.le) h2
  have hAbsorb := mul_le_mul_of_nonneg_left hLog hCoeff
  calc
    _ = 2 * (Real.log (2 * (L / 2 + 9 * eps)) / d + 3) + 3 := by
      norm_num [hamiltonianDiffuseInverseBudget, d]
    _ <= 2 * ((Real.log 2 + Real.log L) / d + 3) + 3 := by linarith only [hDivide]
    _ <= hamiltonianPrimeScalingLogConstant * Real.log L := by
      unfold hamiltonianPrimeScalingLogConstant
      change _ <= (2 / d * (1 + Real.log 2) + 9) * Real.log L
      have hRest : 0 <= (2 / d * Real.log 2 + 9) * (Real.log L - 1) :=
        mul_nonneg (by linarith only [hCoeff]) (sub_nonneg.mpr hLog)
      calc
        _ = (2 / d * (1 + Real.log 2) + 9) * Real.log L -
          (2 / d * Real.log 2 + 9) * (Real.log L - 1) := by ring
        _ <= _ := sub_le_self _ hRest

theorem hamiltonian_prime_scaling_real_window (B t : Real) (hB : 0 < B) (ht : 0 < t) :
    exists L0 : Real, And (64 <= L0)
      (forall L : Real, L0 <= L ->
        let eps := B / Real.sqrt L
        let g := hamiltonianDiffuseInverseBudget (L / 2 + 9 * eps) (2 / 3)
        And (0 < eps) (And (eps <= 1 / 100) (eps * g ^ 2 <= t))) := by
  let K := hamiltonianPrimeScalingLogConstant
  have hK : 0 < K := hamiltonian_prime_scaling_log_constant_positive
  have hDen : 0 < B * K ^ 2 := mul_pos hB (sq_pos_of_pos hK)
  have hRatio := (tendsto_log_pow_div_sqrt 1).eventually_lt_const (div_pos ht hDen)
  choose L1 hL1 using Filter.eventually_atTop.mp hRatio
  let L0 := max 64 (max (Real.exp 1) (max ((100 * B) ^ 2) L1))
  have hL0 : 64 <= L0 := le_max_left _ _
  refine Exists.intro L0 (And.intro hL0 ?_)
  intro L hLarge
  have hL : 64 <= L := hL0.trans hLarge
  have hExp : Real.exp 1 <= L := by dsimp only [L0] at hLarge; exact (le_max_left _ _).trans ((le_max_right _ _).trans hLarge)
  have hSquare : (100 * B) ^ 2 <= L := by
    dsimp only [L0] at hLarge
    exact (le_max_left _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans hLarge))
  have hLL : L1 <= L := by dsimp only [L0] at hLarge; exact (le_max_right _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans hLarge))
  have hLpos : 0 < L := by linarith only [hL]
  have hSqrt : 0 < Real.sqrt L := Real.sqrt_pos.mpr hLpos
  have hSqrtLower : 100 * B <= Real.sqrt L := by
    nlinarith only [hSquare, Real.sq_sqrt hLpos.le, hB, Real.sqrt_nonneg L]
  have hEps : 0 < B / Real.sqrt L := div_pos hB hSqrt
  have hEpsSmall : B / Real.sqrt L <= 1 / 100 := by
    have h := div_le_div_of_nonneg_left hB.le (by positivity : 0 < 100 * B) hSqrtLower
    have heq : B / (100 * B) = (1 / 100 : Real) := by field_simp [ne_of_gt hB]
    exact h.trans (le_of_eq heq)
  have hLog : 1 <= Real.log L := by
    have h := Real.log_le_log (Real.exp_pos 1) hExp
    simpa only [Real.log_exp] using h
  let g := hamiltonianDiffuseInverseBudget (L / 2 + 9 * (B / Real.sqrt L)) (2 / 3)
  have hg : 1 <= g := hamiltonian_diffuse_inverse_budget_positive _ _ (by linarith only [hL, hEps]) (by norm_num) (by norm_num)
  have hgUpper : g <= K * Real.log L :=
    hamiltonian_prime_scaling_log_budget L (B / Real.sqrt L) hL hLog hEps hEpsSmall
  have hgSq : g ^ 2 <= (K * Real.log L) ^ 2 := by
    nlinarith only [hgUpper, hg, mul_pos hK (by linarith only [hLog] : 0 < Real.log L)]
  have hFinal : B / Real.sqrt L * g ^ 2 <= t := by
    calc
      _ <= B / Real.sqrt L * (K * Real.log L) ^ 2 :=
        mul_le_mul_of_nonneg_left hgSq hEps.le
      _ = (B * K ^ 2) * (Real.log L ^ 2 / Real.sqrt L) := by ring
      _ <= (B * K ^ 2) * (t / (B * K ^ 2)) :=
        mul_le_mul_of_nonneg_left (by simpa only [show (1 : Nat) + 1 = 2 from rfl] using (hL1 L hLL).le) hDen.le
      _ = t := by field_simp [ne_of_gt hDen]
  exact And.intro hEps (And.intro hEpsSmall hFinal)

end PrimeFactorOscillations

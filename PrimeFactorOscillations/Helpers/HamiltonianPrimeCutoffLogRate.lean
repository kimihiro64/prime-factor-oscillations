/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.HamiltonianLogMomentChoice
import PrimeFactorOscillations.Helpers.HamiltonianPrimeCutoffSelection

/-! # Arbitrary logarithmic accuracy of the actual moving prime cutoff -/

set_option autoImplicit false
set_option Elab.async false

noncomputable section

namespace PrimeFactorOscillations.LPF

theorem hamiltonian_prime_cutoff_logarithmic_rate
    (b : Nat) (eps : Real) (hEps : 0 < eps) :
    exists M0 : Nat, 2 ^ 18 <= M0 /\
      forall M : Nat, M0 <= M ->
        ((1 + Real.log (2 * (M : Real))) ^ 5 /
          Real.sqrt (hamiltonianPrimeCutoff M : Real)) *
          (1 + Real.log (2 * (M : Real))) ^ b <= eps := by
  let k := 2 * (b + 5)
  let C : Real := (2 : Real) ^ (k + 1) / eps ^ 2
  have hC : 0 < C := by dsimp [C]; positivity
  choose A hA hRange using hamiltonian_prime_cutoff_admissible 1 (by norm_num)
  choose B hB hSmall using hamiltonian_log_power_dominated_uniform
    C hC k (1 / 160) (by norm_num)
  let M0 := max A B
  refine Exists.intro M0 (And.intro (hA.trans (le_max_left _ _)) ?_)
  intro M hM
  have hMA : A <= M := (le_max_left _ _).trans hM
  have hMB : B <= M := (le_max_right _ _).trans hM
  have hM256 : 256 <= M := hB.trans hMB
  have hMR : (1 : Real) <= (M : Real) := by exact_mod_cast (show 1 <= M by omega)
  let x : Real := (M : Real) ^ (1 / 160 : Real)
  let Q := hamiltonianPrimeCutoff M
  let ell : Real := 1 + Real.log (2 * (M : Real))
  have hQ4 : 4 <= Q := (hRange M hMA).1
  have hQR : (0 : Real) < (Q : Real) := by exact_mod_cast (show 0 < Q by omega)
  have hFloor : x < (Q : Real) + 1 := Nat.lt_floor_add_one x
  have hQLower : x <= 2 * (Q : Real) := by
    have hFour : (4 : Real) <= (Q : Real) := by exact_mod_cast hQ4
    linarith only [hFloor, hFour]
  have hLog : 1 <= Real.log (2 * (M : Real)) :=
    hamiltonian_log_four_lower.trans (Real.log_le_log (by norm_num)
      (by exact_mod_cast (show 4 <= 2 * M by omega)))
  have hEll : 0 <= ell := by dsimp [ell]; linarith only [hLog]
  have hEllLog : ell <= 2 * Real.log (2 * (M : Real)) := by
    dsimp [ell]
    linarith only [hLog]
  have hEllPower := wick_nonnegative_power_le _ _ hEll hEllLog k
  rw [mul_pow] at hEllPower
  have hBudget : 2 * ((2 : Real) ^ k * Real.log (2 * (M : Real)) ^ k) <= x * eps ^ 2 := by
    calc
      _ = (C * Real.log (2 * (M : Real)) ^ k) * eps ^ 2 := by
        dsimp [C]
        field_simp [ne_of_gt hEps]
        <;> rw [pow_succ]
        <;> ring
      _ <= x * eps ^ 2 := mul_le_mul_of_nonneg_right (hSmall M hMB) (sq_nonneg eps)
  have hQBudget := mul_le_mul_of_nonneg_right hQLower (sq_nonneg eps)
  have hEllBudget : ell ^ k <= eps ^ 2 * (Q : Real) := by
    nlinarith only [hEllPower, hBudget, hQBudget]
  have hSqrt : Real.sqrt (Q : Real) ^ 2 = (Q : Real) := Real.sq_sqrt hQR.le
  have hSqrtPos : 0 < Real.sqrt (Q : Real) := Real.sqrt_pos.mpr hQR
  have hCrossSquare : (ell ^ (b + 5)) ^ 2 <= (eps * Real.sqrt (Q : Real)) ^ 2 := by
    calc
      _ = ell ^ k := by dsimp [k]; rw [<- pow_mul]; congr 1 <;> omega
      _ <= eps ^ 2 * (Q : Real) := hEllBudget
      _ = _ := by rw [mul_pow, hSqrt]
  have hCross : ell ^ (b + 5) <= eps * Real.sqrt (Q : Real) := by
    have hLeft : 0 <= ell ^ (b + 5) := pow_nonneg hEll _
    have hRight : 0 <= eps * Real.sqrt (Q : Real) := mul_nonneg hEps.le hSqrtPos.le
    nlinarith only [hCrossSquare, hLeft, hRight]
  have hRatio : ell ^ (b + 5) / Real.sqrt (Q : Real) <= eps := by
    calc
      _ <= (eps * Real.sqrt (Q : Real)) / Real.sqrt (Q : Real) :=
        div_le_div_of_nonneg_right hCross hSqrtPos.le
      _ = _ := by field_simp [ne_of_gt hSqrtPos]
  change (ell ^ 5 / Real.sqrt (Q : Real)) * ell ^ b <= eps
  calc
    _ = ell ^ (b + 5) / Real.sqrt (Q : Real) := by rw [pow_add]; ring
    _ <= eps := hRatio

end PrimeFactorOscillations.LPF

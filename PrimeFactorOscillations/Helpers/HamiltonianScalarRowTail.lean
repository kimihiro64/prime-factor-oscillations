/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.HamiltonianColumnPolynomialTail
import PrimeFactorOscillations.Helpers.HamiltonianScalarRowMoments

/-! # Uniform finite signed-row tails

The moment and exceptional-set bounds cover the entire sign cube.
A logarithmic moment leaves five dimension powers for the all-row
union and the already verified balanced conditioning budgets.
-/

set_option autoImplicit false
set_option Elab.async false

noncomputable section

namespace PrimeFactorOscillations

variable {J : Type*} [Fintype J] [DecidableEq J]

def hamiltonianScalarBadSigns (w : J -> Real) (t : Real) : Finset (J -> Bool) := by
  classical
  exact Finset.univ.filter (fun e => t < abs (hamiltonianScalarSignSum w e))

theorem hamiltonian_mem_scalar_bad_signs (w : J -> Real) (t : Real) (e : J -> Bool) :
    Membership.mem (hamiltonianScalarBadSigns w t) e <->
      t < abs (hamiltonianScalarSignSum w e) := by
  classical
  simp [hamiltonianScalarBadSigns]

theorem hamiltonian_scalar_row_bad_count_bound
    (w : J -> Real) (alpha : Real)
    (hNonneg : forall j, 0 <= w j) (hCap : forall j, w j <= alpha)
    (hRow : Finset.univ.sum w = 1) (k : Nat) (t : Real) (ht : 0 < t) :
    ((hamiltonianScalarBadSigns w t).card : Real) * t ^ (2 * k) <=
      (Fintype.card (J -> Bool) : Real) * (2 * alpha * (k : Real)) ^ k := by
  classical
  let B := hamiltonianScalarBadSigns w t
  have hEven (e : J -> Bool) : 0 <= hamiltonianScalarSignSum w e ^ (2 * k) := by
    rw [pow_mul]
    exact pow_nonneg (sq_nonneg _) _
  have hSingle (e : J -> Bool) (he : Membership.mem B e) :
      t ^ (2 * k) <= hamiltonianScalarSignSum w e ^ (2 * k) := by
    have hBad := (hamiltonian_mem_scalar_bad_signs w t e).mp he
    have hPow : t ^ (2 * k) <= abs (hamiltonianScalarSignSum w e) ^ (2 * k) := by
      gcongr <;> exact hBad.le
    have hAbs : abs (hamiltonianScalarSignSum w e) ^ (2 * k) =
        hamiltonianScalarSignSum w e ^ (2 * k) := by
      rw [pow_mul, pow_mul, sq_abs]
    exact hPow.trans_eq hAbs
  calc
    _ = B.sum (fun _ => t ^ (2 * k)) := by
      change (B.card : Real) * t ^ (2 * k) = _
      simp only [Finset.sum_const, nsmul_eq_mul]
    _ <= B.sum (fun e => hamiltonianScalarSignSum w e ^ (2 * k)) :=
      Finset.sum_le_sum hSingle
    _ <= Finset.univ.sum (fun e => hamiltonianScalarSignSum w e ^ (2 * k)) :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ B) (fun e he hne => hEven e)
    _ = hamiltonianScalarSignMoment w k := rfl
    _ <= _ := hamiltonian_scalar_row_moment_power_bound w alpha hNonneg hCap hRow k

theorem hamiltonian_scalar_row_bad_proportion_bound
    (w : J -> Real) (alpha : Real)
    (hNonneg : forall j, 0 <= w j) (hCap : forall j, w j <= alpha)
    (hRow : Finset.univ.sum w = 1) (k : Nat) (t : Real) (ht : 0 < t) :
    ((hamiltonianScalarBadSigns w t).card : Real) / (Fintype.card (J -> Bool) : Real) <=
      (2 * alpha * (k : Real)) ^ k / t ^ (2 * k) := by
  have hMain := hamiltonian_scalar_row_bad_count_bound w alpha hNonneg hCap hRow k t ht
  have hCube : (0 : Real) < Fintype.card (J -> Bool) := Nat.cast_pos.mpr Fintype.card_pos
  have hPower : 0 < t ^ (2 * k) := pow_pos ht _
  have h := div_le_div_of_nonneg_right hMain (mul_nonneg hCube.le hPower.le)
  convert h using 1 <;> field_simp [ne_of_gt hCube, ne_of_gt hPower]

theorem hamiltonian_scalar_row_sqrt_moment_tail
    (w : J -> Real) (alpha : Real)
    (hNonneg : forall j, 0 <= w j) (hCap : forall j, w j <= alpha)
    (hRow : Finset.univ.sum w = 1) (k : Nat) (hk : 1 <= k) :
    ((hamiltonianScalarBadSigns w (Real.sqrt (8 * alpha * (k : Real)))).card : Real) /
      (Fintype.card (J -> Bool) : Real) <= (1 / 4 : Real) ^ k := by
  have hAlpha := hamiltonian_stochastic_row_cap_positive w alpha hNonneg hCap hRow
  have hkPos : (0 : Real) < k := Nat.cast_pos.mpr (by omega)
  have hBase : 0 < 8 * alpha * (k : Real) := by positivity
  have hSqrt : 0 < Real.sqrt (8 * alpha * (k : Real)) := Real.sqrt_pos.mpr hBase
  have hSquare := Real.sq_sqrt hBase.le
  have hMain := hamiltonian_scalar_row_bad_proportion_bound w alpha hNonneg hCap hRow
    k (Real.sqrt (8 * alpha * (k : Real))) hSqrt
  have hFrac : (2 * alpha * (k : Real)) ^ k /
      (Real.sqrt (8 * alpha * (k : Real))) ^ (2 * k) = (1 / 4 : Real) ^ k := by
    rw [pow_mul, hSquare, <- div_pow]
    have hRatio : (2 * alpha * (k : Real)) / (8 * alpha * (k : Real)) = 1 / 4 := by
      field_simp [ne_of_gt hAlpha, ne_of_gt hkPos]
      ring
    rw [hRatio]
  exact hMain.trans_eq hFrac

theorem hamiltonian_scalar_row_uniform_polynomial_tail
    (w : J -> Real) (alpha A : Real) (hA : 0 < A)
    (hNonneg : forall j, 0 <= w j) (hCap : forall j, w j <= alpha)
    (hRow : Finset.univ.sum w = 1) (hSize : 2 <= Fintype.card J) :
    ((hamiltonianScalarBadSigns w
      (Real.sqrt (8 * (A + 6) * alpha * Real.log (2 * (Fintype.card J : Real))))).card : Real) /
        (Fintype.card (J -> Bool) : Real) <= (Fintype.card J : Real) ^ (-(A + 5)) := by
  classical
  let n : Real := Fintype.card J
  let L := Real.log (2 * n)
  let t := Real.sqrt (8 * (A + 6) * alpha * L)
  let k := Nat.ceil ((A + 5) * L)
  have hn : 2 <= n := by dsimp only [n]; exact_mod_cast hSize
  have hnPos : 0 < n := by linarith only [hn]
  have hAlpha := hamiltonian_stochastic_row_cap_positive w alpha hNonneg hCap hRow
  have hL : 1 <= L := hamiltonian_log_four_lower.trans
    (Real.log_le_log (by norm_num) (by dsimp only [n]; linarith only [hn]))
  have hChoice0 : 0 <= (A + 5) * L := by positivity
  have hkLow : (A + 5) * L <= (k : Real) := Nat.le_ceil _
  have hkUpper : (k : Real) < (A + 5) * L + 1 := Nat.ceil_lt_add_one hChoice0
  have hkReal : 1 <= (k : Real) := by nlinarith only [hkLow, hL, hA]
  have hk : 1 <= k := by exact_mod_cast hkReal
  have hkBudget : (k : Real) <= (A + 6) * L := by nlinarith only [hkUpper, hL]
  have hThreshold : Real.sqrt (8 * alpha * (k : Real)) <= t := by
    apply Real.sqrt_le_sqrt
    have h := mul_le_mul_of_nonneg_left hkBudget (show (0 : Real) <= 8 * alpha by positivity)
    nlinarith only [h]
  have hSubset : hamiltonianScalarBadSigns w t <=
      hamiltonianScalarBadSigns w (Real.sqrt (8 * alpha * (k : Real))) := by
    intro e he
    apply (hamiltonian_mem_scalar_bad_signs w _ e).mpr
    exact hThreshold.trans_lt ((hamiltonian_mem_scalar_bad_signs w t e).mp he)
  have hCard : ((hamiltonianScalarBadSigns w t).card : Real) <=
      ((hamiltonianScalarBadSigns w (Real.sqrt (8 * alpha * (k : Real)))).card : Real) :=
    Nat.cast_le.mpr (Finset.card_le_card hSubset)
  have hTail := hamiltonian_scalar_row_sqrt_moment_tail w alpha hNonneg hCap hRow k hk
  have hLogN : Real.log n <= L := Real.log_le_log hnPos (by linarith only [hnPos])
  have hKLog : (A + 5) * Real.log n <= (k : Real) :=
    (mul_le_mul_of_nonneg_left hLogN (by linarith only [hA])).trans hkLow
  have hExp : Real.exp (-(k : Real)) <= n ^ (-(A + 5)) := by
    calc
      _ <= Real.exp (-(A + 5) * Real.log n) :=
        Real.exp_le_exp.mpr (by linarith only [hKLog])
      _ = Real.exp (Real.log n * (-(A + 5))) := by congr 1; ring
      _ = _ := (Real.rpow_def_of_pos hnPos _).symm
  change ((hamiltonianScalarBadSigns w t).card : Real) / _ <= n ^ (-(A + 5))
  exact (div_le_div_of_nonneg_right hCard (Nat.cast_nonneg _)).trans
    (hTail.trans ((hamiltonian_one_quarter_power_exponential k).trans hExp))

end PrimeFactorOscillations

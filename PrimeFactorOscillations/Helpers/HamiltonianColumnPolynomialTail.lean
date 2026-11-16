/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.HamiltonianLogMomentChoice
import PrimeFactorOscillations.Helpers.HamiltonianSignCubeTail

/-! # Uniform polynomial covariance tails from the full signed moments

The logarithmic moment is chosen explicitly. Every dimension at
least two, every positive target exponent and the zero-variance
case are included. The cap has no small-dimension-product restriction.
-/

set_option autoImplicit false
set_option Elab.async false

open scoped Matrix.Norms.L2Operator

noncomputable section

namespace PrimeFactorOscillations

variable {I : Type*} [Fintype I] [DecidableEq I]

theorem hamiltonian_one_quarter_power_exponential (k : Nat) :
    (1 / 4 : Real) ^ k <= Real.exp (-(k : Real)) := by
  have hLog : Real.log (1 / 4 : Real) <= -1 := by
    rw [one_div, Real.log_inv]
    linarith only [hamiltonian_log_four_lower]
  calc
    _ = (1 / 4 : Real) ^ (k : Real) := (Real.rpow_natCast _ _).symm
    _ = Real.exp (Real.log (1 / 4 : Real) * (k : Real)) :=
      Real.rpow_def_of_pos (by norm_num) _
    _ <= _ := Real.exp_le_exp.mpr
      (by simpa only [neg_one_mul] using
        mul_le_mul_of_nonneg_right hLog (Nat.cast_nonneg k))

theorem hamiltonian_column_sqrt_moment_tail
    (E : Matrix I I Real) (hE : E.IsHermitian)
    (alpha : Real) (hAlpha : 0 < alpha)
    (hColumn : forall j, hamiltonianColumnEnergy E j <= alpha)
    (hNorm : norm E <= 1) (k : Nat) (hk : 1 <= k) :
    ((hamiltonianColumnBadSigns E (Real.sqrt (2 * alpha * (k : Real)))).card : Real) /
      (Fintype.card (I -> Bool) : Real) <=
        (Fintype.card I : Real) * (1 / 4 : Real) ^ k := by
  have hkPos : (0 : Real) < k := Nat.cast_pos.mpr (by omega)
  have hBase : 0 < 2 * alpha * (k : Real) := by positivity
  have hSqrt : 0 < Real.sqrt (2 * alpha * (k : Real)) := Real.sqrt_pos.mpr hBase
  have hSquare := Real.sq_sqrt hBase.le
  have hMain := hamiltonian_column_bad_sign_proportion_bound E hE alpha hAlpha.le
    hColumn hNorm k hk (Real.sqrt (2 * alpha * (k : Real))) hSqrt
  have hFrac :
      ((Fintype.card I : Real) * (alpha * (k : Real) / 2) ^ k) /
        (Real.sqrt (2 * alpha * (k : Real))) ^ (2 * k) =
      (Fintype.card I : Real) * (1 / 4 : Real) ^ k := by
    rw [pow_mul, hSquare, mul_div_assoc, <- div_pow]
    have hRatio : (alpha * (k : Real) / 2) / (2 * alpha * (k : Real)) = 1 / 4 := by
      field_simp [ne_of_gt hAlpha, ne_of_gt hkPos]
      ring
    rw [hRatio]
  exact hMain.trans_eq hFrac

theorem hamiltonian_zero_column_sign_matrix
    (E : Matrix I I Real) (hColumn : forall j, hamiltonianColumnEnergy E j <= 0)
    (e : I -> Bool) :
    hamiltonianSignMatrix (hamiltonianColumnSummand E) e = 0 := by
  have hZero := hamiltonian_zero_column_energy_matrix E hColumn
  rw [hZero]
  ext i j
  simp only [hamiltonianSignMatrix, Matrix.sum_apply, hamiltonian_sign_smul_entry,
    hamiltonianColumnSummand, Matrix.zero_apply, mul_zero, Finset.sum_const_zero]

theorem hamiltonian_column_uniform_polynomial_tail
    (E : Matrix I I Real) (hE : E.IsHermitian)
    (alpha A : Real) (hAlpha : 0 <= alpha) (hA : 0 < A)
    (hColumn : forall j, hamiltonianColumnEnergy E j <= alpha)
    (hNorm : norm E <= 1) (hSize : 2 <= Fintype.card I) :
    ((hamiltonianColumnBadSigns E
        (Real.sqrt (2 * (A + 5) * alpha * Real.log (2 * (Fintype.card I : Real))))).card : Real) /
      (Fintype.card (I -> Bool) : Real) <=
        (Fintype.card I : Real) ^ (-(A + 3)) := by
  classical
  let n : Real := Fintype.card I
  let L := Real.log (2 * n)
  let t := Real.sqrt (2 * (A + 5) * alpha * L)
  have hn : 2 <= n := by dsimp only [n]; exact_mod_cast hSize
  have hnPos : 0 < n := by linarith only [hn]
  have hL : 1 <= L := hamiltonian_log_four_lower.trans
    (Real.log_le_log (by norm_num) (by dsimp only [n]; linarith only [hn]))
  by_cases hZero : alpha = 0
  case pos =>
    have hColumn0 : forall j, hamiltonianColumnEnergy E j <= 0 := by
      intro j
      simpa only [hZero] using hColumn j
    have hEmpty : hamiltonianColumnBadSigns E t = (EmptyCollection.emptyCollection : Finset (I -> Bool)) := by
      apply Finset.ext
      intro e
      constructor
      case mp =>
        intro he
        have hBad := (hamiltonian_mem_column_bad_signs E t e).mp he
        rw [hamiltonian_zero_column_sign_matrix E hColumn0 e, norm_zero] at hBad
        exact False.elim ((not_lt_of_ge (Real.sqrt_nonneg _)) hBad)
      case mpr =>
        intro he
        simp at he
    change ((hamiltonianColumnBadSigns E t).card : Real) / _ <= n ^ (-(A + 3))
    rw [hEmpty]
    simpa only [Finset.card_empty, Nat.cast_zero, zero_div] using
      Real.rpow_nonneg hnPos.le (-(A + 3))
  case neg =>
    have hAlphaPos : 0 < alpha := lt_of_le_of_ne hAlpha (Ne.symm hZero)
    let k := Nat.ceil ((A + 4) * L)
    have hChoice0 : 0 <= (A + 4) * L := by positivity
    have hkLow : (A + 4) * L <= (k : Real) := Nat.le_ceil _
    have hkUpper : (k : Real) < (A + 4) * L + 1 :=
      Nat.ceil_lt_add_one hChoice0
    have hkReal : 1 <= (k : Real) := by nlinarith only [hkLow, hL, hA]
    have hk : 1 <= k := by exact_mod_cast hkReal
    have hkBudget : (k : Real) <= (A + 5) * L := by nlinarith only [hkUpper, hL]
    have hThreshold : Real.sqrt (2 * alpha * (k : Real)) <= t := by
      apply Real.sqrt_le_sqrt
      have h := mul_le_mul_of_nonneg_left hkBudget
        (show (0 : Real) <= 2 * alpha by positivity)
      nlinarith only [h]
    have hSubset : hamiltonianColumnBadSigns E t <=
        hamiltonianColumnBadSigns E (Real.sqrt (2 * alpha * (k : Real))) := by
      intro e he
      apply (hamiltonian_mem_column_bad_signs E _ e).mpr
      exact hThreshold.trans_lt ((hamiltonian_mem_column_bad_signs E t e).mp he)
    have hCard : ((hamiltonianColumnBadSigns E t).card : Real) <=
        ((hamiltonianColumnBadSigns E (Real.sqrt (2 * alpha * (k : Real)))).card : Real) :=
      Nat.cast_le.mpr (Finset.card_le_card hSubset)
    have hTail := hamiltonian_column_sqrt_moment_tail E hE alpha hAlphaPos hColumn hNorm k hk
    have hLogN : Real.log n <= L :=
      Real.log_le_log hnPos (by linarith only [hnPos])
    have hKLog : (A + 4) * Real.log n <= (k : Real) :=
      (mul_le_mul_of_nonneg_left hLogN (by linarith only [hA])).trans hkLow
    have hExp : n * Real.exp (-(k : Real)) <= n ^ (-(A + 3)) := by
      calc
        _ <= n * Real.exp (-(A + 4) * Real.log n) :=
          mul_le_mul_of_nonneg_left
            (Real.exp_le_exp.mpr (by linarith only [hKLog])) hnPos.le
        _ = Real.exp (Real.log n + (-(A + 4) * Real.log n)) := by
          rw [Real.exp_add, Real.exp_log hnPos]
        _ = Real.exp (Real.log n * (-(A + 3))) := by congr 1; ring
        _ = _ := (Real.rpow_def_of_pos hnPos _).symm
    change ((hamiltonianColumnBadSigns E t).card : Real) / _ <= n ^ (-(A + 3))
    exact (div_le_div_of_nonneg_right hCard (Nat.cast_nonneg _)).trans
      (hTail.trans ((mul_le_mul_of_nonneg_left
        (hamiltonian_one_quarter_power_exponential k) hnPos.le).trans hExp))

end PrimeFactorOscillations

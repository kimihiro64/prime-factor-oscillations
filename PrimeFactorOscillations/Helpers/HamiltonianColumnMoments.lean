/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.HamiltonianColumnVariance

/-! # Uniform column moments at every order

The exact odd product is obtained from the signed recurrence,
then bounded by a single power. The full finite sign cube is
retained in the dimension factor; no selected sample is used.
-/

set_option autoImplicit false
set_option Elab.async false

open scoped Matrix.Norms.L2Operator

noncomputable section

namespace PrimeFactorOscillations

variable {I : Type*} [Fintype I] [DecidableEq I]

def hamiltonianOddMomentFactor (k : Nat) : Real :=
  (Finset.range k).prod (fun r => 2 * (r : Real) + 1)

def hamiltonianColumnMoment (E : Matrix I I Real) (k : Nat) : Real :=
  Finset.univ.sum (fun e => Matrix.trace
    (hamiltonianSignMatrix (hamiltonianColumnSummand E) e ^ (2 * k)))

theorem hamiltonian_odd_moment_factor_nonnegative (k : Nat) :
    0 <= hamiltonianOddMomentFactor k := by
  exact Finset.prod_nonneg (fun r hr => by positivity)

theorem hamiltonian_odd_moment_factor_successor (k : Nat) :
    hamiltonianOddMomentFactor (k + 1) =
      hamiltonianOddMomentFactor k * (2 * (k : Real) + 1) := by
  exact Finset.prod_range_succ _ _

theorem hamiltonian_odd_moment_factor_bound (k : Nat) :
    hamiltonianOddMomentFactor k <= (2 * (k : Real)) ^ k := by
  have hEach (r : Nat) (hr : Membership.mem (Finset.range k) r) :
      2 * (r : Real) + 1 <= 2 * (k : Real) := by
    have hrk := Finset.mem_range.mp hr
    exact_mod_cast (show 2 * r + 1 <= 2 * k by omega)
  have hPrefix : forall n : Nat, n <= k ->
      (Finset.range n).prod (fun r => 2 * (r : Real) + 1) <= (2 * (k : Real)) ^ n := by
    intro n
    induction n with
    | zero => intro hn; simp
    | succ n ih =>
        intro hn
        rw [Finset.prod_range_succ, pow_succ]
        apply mul_le_mul (ih (by omega)) (hEach n (Finset.mem_range.mpr (by omega)))
        all_goals positivity
  exact hPrefix k (le_refl k)

theorem hamiltonian_column_moment_zero (E : Matrix I I Real) :
    hamiltonianColumnMoment E 0 =
      (Fintype.card (I -> Bool) : Real) * (Fintype.card I : Real) := by
  have hTrace : Matrix.trace (1 : Matrix I I Real) = (Fintype.card I : Real) := by
    simp [Matrix.trace, Matrix.diag_apply]
  simp only [hamiltonianColumnMoment, Nat.mul_zero, pow_zero, hTrace,
    Finset.sum_const, Finset.card_univ, nsmul_eq_mul]

theorem hamiltonian_column_moment_odd_product
    (E : Matrix I I Real) (hE : E.IsHermitian)
    (alpha : Real) (hAlpha : 0 <= alpha)
    (hColumn : forall j, hamiltonianColumnEnergy E j <= alpha)
    (hNorm : norm E <= 1) (k : Nat) :
    hamiltonianColumnMoment E k <=
      (Fintype.card (I -> Bool) : Real) * (Fintype.card I : Real) *
        hamiltonianOddMomentFactor k * (alpha / 4) ^ k := by
  induction k with
  | zero =>
      rw [hamiltonian_column_moment_zero]
      simp [hamiltonianOddMomentFactor]
  | succ k ih =>
      have hEven : Even (2 * k) := Exists.intro k (by omega)
      have hRec := hamiltonian_column_sign_moment_recurrence
        E hE alpha hAlpha hColumn hNorm (2 * k) hEven
      have hPower : 2 * k + 2 = 2 * (k + 1) := by omega
      rw [hPower] at hRec
      change hamiltonianColumnMoment E (k + 1) <=
        (((2 * k + 1 : Nat) : Real) * (alpha / 4)) * hamiltonianColumnMoment E k at hRec
      have hC : 0 <= ((2 * k + 1 : Nat) : Real) * (alpha / 4) :=
        mul_nonneg (Nat.cast_nonneg _) (div_nonneg hAlpha (by norm_num))
      have h := hRec.trans (mul_le_mul_of_nonneg_left ih hC)
      rw [hamiltonian_odd_moment_factor_successor, pow_succ]
      convert h using 1 <;> norm_num only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat] <;> ring

theorem hamiltonian_column_moment_power_bound
    (E : Matrix I I Real) (hE : E.IsHermitian)
    (alpha : Real) (hAlpha : 0 <= alpha)
    (hColumn : forall j, hamiltonianColumnEnergy E j <= alpha)
    (hNorm : norm E <= 1) (k : Nat) :
    hamiltonianColumnMoment E k <=
      (Fintype.card (I -> Bool) : Real) * (Fintype.card I : Real) *
        (alpha * (k : Real) / 2) ^ k := by
  have hMain := hamiltonian_column_moment_odd_product E hE alpha hAlpha hColumn hNorm k
  have hC : 0 <= (Fintype.card (I -> Bool) : Real) * (Fintype.card I : Real) :=
    mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
  calc
    _ <= (Fintype.card (I -> Bool) : Real) * (Fintype.card I : Real) *
        ((2 * (k : Real)) ^ k) * (alpha / 4) ^ k := by
      exact hMain.trans (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left (hamiltonian_odd_moment_factor_bound k) hC)
        (pow_nonneg (div_nonneg hAlpha (by norm_num)) k))
    _ = _ := by
      rw [mul_assoc, <- mul_pow]
      congr 2
      ring

end PrimeFactorOscillations

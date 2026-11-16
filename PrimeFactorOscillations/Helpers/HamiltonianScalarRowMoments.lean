/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.HamiltonianMomentIteration
import PrimeFactorOscillations.Helpers.HamiltonianScalarSignMoments

/-! # All-order full-cube scalar row moments

The complete signed recurrence is iterated before the variance
cap is used. Every real weight is allowed in the first theorem;
stochastic rows consume only their independently proved variance.
-/

set_option autoImplicit false
set_option Elab.async false

noncomputable section

namespace PrimeFactorOscillations

variable {J : Type*} [Fintype J] [DecidableEq J]

def hamiltonianScalarSignMoment (w : J -> Real) (k : Nat) : Real :=
  Finset.univ.sum (fun e => hamiltonianScalarSignSum w e ^ (2 * k))

theorem hamiltonian_scalar_sign_moment_zero (w : J -> Real) :
    hamiltonianScalarSignMoment w 0 = (Fintype.card (J -> Bool) : Real) := by
  simp [hamiltonianScalarSignMoment]

theorem hamiltonian_scalar_sign_moment_power_bound (w : J -> Real) (k : Nat) :
    hamiltonianScalarSignMoment w k <= (Fintype.card (J -> Bool) : Real) *
      (2 * hamiltonianScalarSignVariance w * (k : Real)) ^ k := by
  have hV : 0 <= hamiltonianScalarSignVariance w :=
    Finset.sum_nonneg (fun j hj => sq_nonneg _)
  have hRec (r : Nat) :
      hamiltonianScalarSignMoment w (r + 1) <=
        (2 * (r : Real) + 1) * hamiltonianScalarSignVariance w *
          hamiltonianScalarSignMoment w r := by
    have hEven : Even (2 * r) := Exists.intro r (by omega)
    have h := hamiltonian_scalar_sign_even_moment_recurrence w (2 * r) hEven
    have hPower : 2 * r + 2 = 2 * (r + 1) := by omega
    rw [hPower] at h
    change hamiltonianScalarSignMoment w (r + 1) <=
      (((2 * r + 1 : Nat) : Real) * hamiltonianScalarSignVariance w) *
        hamiltonianScalarSignMoment w r at h
    norm_num only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat] at h
    exact h
  exact hamiltonian_moment_recurrence_power_bound (hamiltonianScalarSignMoment w)
    (hamiltonianScalarSignVariance w) (Fintype.card (J -> Bool) : Real) hV
    (Nat.cast_nonneg _) (hamiltonian_scalar_sign_moment_zero w).le hRec k

theorem hamiltonian_scalar_row_moment_power_bound
    (w : J -> Real) (alpha : Real)
    (hNonneg : forall j, 0 <= w j) (hCap : forall j, w j <= alpha)
    (hRow : Finset.univ.sum w = 1) (k : Nat) :
    hamiltonianScalarSignMoment w k <=
      (Fintype.card (J -> Bool) : Real) * (2 * alpha * (k : Real)) ^ k := by
  have hV := hamiltonian_scalar_row_variance_bound w alpha hNonneg hCap hRow
  have hV0 : 0 <= hamiltonianScalarSignVariance w :=
    Finset.sum_nonneg (fun j hj => sq_nonneg _)
  have hBase : 2 * hamiltonianScalarSignVariance w * (k : Real) <=
      2 * alpha * (k : Real) :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hV (by norm_num)) (Nat.cast_nonneg _)
  have hBase0 : 0 <= 2 * hamiltonianScalarSignVariance w * (k : Real) := by positivity
  have hPower : (2 * hamiltonianScalarSignVariance w * (k : Real)) ^ k <=
      (2 * alpha * (k : Real)) ^ k := by gcongr
  exact (hamiltonian_scalar_sign_moment_power_bound w k).trans
    (mul_le_mul_of_nonneg_left hPower (Nat.cast_nonneg _))

theorem hamiltonian_stochastic_row_cap_positive
    (w : J -> Real) (alpha : Real)
    (hNonneg : forall j, 0 <= w j) (hCap : forall j, w j <= alpha)
    (hRow : Finset.univ.sum w = 1) :
    0 < alpha := by
  by_contra hNot
  have hAlpha : alpha <= 0 := le_of_not_gt hNot
  have hZero (j : J) : w j = 0 := le_antisymm ((hCap j).trans hAlpha) (hNonneg j)
  have hSum : Finset.univ.sum w = 0 := by simp_rw [hZero]; simp
  rw [hRow] at hSum
  norm_num at hSum

end PrimeFactorOscillations

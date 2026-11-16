/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.HamiltonianComplementaryCovariance

/-! # Actual coordinate cuts with their complete shared covariance -/

set_option autoImplicit false
set_option Elab.async false

open scoped Classical Matrix.Norms.L2Operator

noncomputable section

namespace PrimeFactorOscillations

variable {I : Type*} [Fintype I] [DecidableEq I]

def hamiltonianCutProjection (D : Finset I) : Matrix I I Real :=
  Matrix.diagonal (fun i => if Membership.mem D i then 1 else 0)

theorem hamiltonian_cut_projection_transpose (D : Finset I) :
    (hamiltonianCutProjection D).transpose = hamiltonianCutProjection D := by
  ext i j
  simp only [hamiltonianCutProjection, Matrix.transpose_apply, Matrix.diagonal_apply]
  by_cases h : i = j
  case pos => subst j; rfl
  case neg => simp only [h, Ne.symm h, ite_false]

theorem hamiltonian_cut_projection_idempotent (D : Finset I) :
    hamiltonianCutProjection D * hamiltonianCutProjection D =
      hamiltonianCutProjection D := by
  ext i j
  by_cases hij : i = j
  case pos =>
    subst j
    by_cases hi : Membership.mem D i <;>
      simp [hamiltonianCutProjection, Matrix.diagonal_mul, hi]
  case neg =>
    simp [hamiltonianCutProjection, Matrix.diagonal_mul, Matrix.diagonal_apply, hij]

theorem hamiltonian_cut_projection_complement (D : Finset I) :
    hamiltonianCutProjection D +
      hamiltonianCutProjection (Compl.compl D : Finset I) = 1 := by
  ext i j
  by_cases hij : i = j
  case pos =>
    subst j
    by_cases hi : Membership.mem D i <;>
      simp [hamiltonianCutProjection, Matrix.diagonal_apply, hi]
  case neg =>
    simp [hamiltonianCutProjection, Matrix.diagonal_apply, Matrix.one_apply, hij]

theorem hamiltonian_cut_projection_norm (D : Finset I) :
    norm (hamiltonianCutProjection D) <= 1 := by
  unfold hamiltonianCutProjection
  rw [Matrix.l2_opNorm_diagonal]
  apply (pi_norm_le_iff_of_nonneg (by norm_num : (0 : Real) <= 1)).mpr
  intro i
  by_cases hi : Membership.mem D i <;> simp only [hi, ite_true, ite_false, norm_zero, norm_one]
  all_goals norm_num

theorem hamiltonian_cut_projection_kernel (E : Matrix I I Real) (D : Finset I) :
    (hamiltonianCutProjection D * E *
        hamiltonianCutProjection (Compl.compl D : Finset I)).submatrix
      (fun i : D => i.val) (fun j : (Compl.compl D : Finset I) => j.val) =
      E.submatrix (fun i : D => i.val)
        (fun j : (Compl.compl D : Finset I) => j.val) := by
  ext i j
  change (hamiltonianCutProjection D * E *
      hamiltonianCutProjection (Compl.compl D : Finset I)) i.val j.val = E i.val j.val
  simp only [hamiltonianCutProjection, Matrix.mul_diagonal, Matrix.diagonal_mul,
    i.property, j.property, ite_true, one_mul, mul_one]

theorem hamiltonian_actual_complementary_restriction_quarter
    (E : Matrix I I Real) (D : Finset I) (hE : E.transpose = E) :
    norm (E.submatrix (fun i : D => i.val)
        (fun j : (Compl.compl D : Finset I) => j.val)) ^ 2 <=
      norm E ^ 2 / 4 + (3 / 2 : Real) *
        norm (hamiltonianComplementaryCovariance E (hamiltonianCutProjection D)) := by
  let R := hamiltonianCutProjection D
  let S := hamiltonianCutProjection (Compl.compl D : Finset I)
  have hQuarter := hamiltonian_complementary_restriction_quarter E R S hE
    (hamiltonian_cut_projection_transpose D)
    (hamiltonian_cut_projection_transpose (Compl.compl D : Finset I))
    (hamiltonian_cut_projection_idempotent D)
    (hamiltonian_cut_projection_idempotent (Compl.compl D : Finset I))
    (hamiltonian_cut_projection_complement D)
    (hamiltonian_cut_projection_norm (Compl.compl D : Finset I))
  have hRestricted := hamiltonian_injective_submatrix_norm
    (fun i : D => i.val) (fun j : (Compl.compl D : Finset I) => j.val)
    Subtype.val_injective Subtype.val_injective (R * E * S)
  rw [hamiltonian_cut_projection_kernel] at hRestricted
  have hSquare := mul_le_mul hRestricted hRestricted
    (norm_nonneg (E.submatrix (fun i : D => i.val)
      (fun j : (Compl.compl D : Finset I) => j.val))) (norm_nonneg (R * E * S))
  nlinarith only [hQuarter, hSquare]

theorem hamiltonian_cut_covariance_entry (E : Matrix I I Real) (D : Finset I) (i j : I) :
    hamiltonianComplementaryCovariance E (hamiltonianCutProjection D) i j =
      Finset.univ.sum (fun k =>
        ((if Membership.mem D k then (1 : Real) else 0) - 1 / 2) * E i k * E k j) := by
  change Finset.univ.sum (fun k => (E * hamiltonianCutProjection D) i k * E k j) -
    (1 / 2 : Real) * Finset.univ.sum (fun k => E i k * E k j) = _
  simp only [hamiltonianCutProjection, Matrix.mul_diagonal]
  rw [Finset.mul_sum, <- Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro k hk
  ring

theorem hamiltonian_actual_complementary_cut_gap
    (E : Matrix I I Real) (D : Finset I) (delta : Real)
    (hSym : E.transpose = E) (hDelta : 0 < delta) (hDelta1 : delta <= 1)
    (hNorm : norm E <= 1 - delta)
    (hCov : norm (hamiltonianComplementaryCovariance E (hamiltonianCutProjection D)) <=
      delta / 128) :
    2 * norm (E.submatrix (fun i : D => i.val)
      (fun j : (Compl.compl D : Finset I) => j.val)) <= 1 - 3 * delta / 4 := by
  let B := E.submatrix (fun i : D => i.val)
    (fun j : (Compl.compl D : Finset I) => j.val)
  have hQuarter := hamiltonian_actual_complementary_restriction_quarter E D hSym
  have hE0 : 0 <= norm E := norm_nonneg E
  have hB0 : 0 <= norm B := norm_nonneg B
  have hOne : 0 <= 1 - delta := by linarith only [hDelta1]
  have hESquare := mul_le_mul hNorm hNorm hE0 hOne
  have hDeltaSquare : delta ^ 2 <= delta := by
    have h := mul_nonneg hDelta.le (sub_nonneg.mpr hDelta1)
    nlinarith only [h]
  have hTarget : 0 < 1 - 3 * delta / 4 := by linarith only [hDelta1]
  have hSquare : (2 * norm B) ^ 2 <= (1 - 3 * delta / 4) ^ 2 := by
    nlinarith only [hQuarter, hESquare, hCov, hDeltaSquare]
  nlinarith only [hSquare, hB0, hTarget]

end PrimeFactorOscillations

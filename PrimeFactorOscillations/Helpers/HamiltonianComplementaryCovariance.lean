/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import Mathlib.Tactic.Abel
import PrimeFactorOscillations.Helpers.HamiltonianFactorNormalization
import PrimeFactorOscillations.Helpers.HamiltonianInjectiveMatrixRestriction

/-! # The same signed covariance on complementary coordinate projections

The exact complementary identity is retained before either operator
estimate. The resulting quarter coefficient is the deterministic
consumer of the matrix concentration input in balanced-cut scaling.
-/

set_option autoImplicit false
set_option Elab.async false

open scoped Matrix.Norms.L2Operator

noncomputable section

namespace PrimeFactorOscillations

variable {I : Type*} [Fintype I] [DecidableEq I]

def hamiltonianComplementaryCovariance
    (E R : Matrix I I Real) : Matrix I I Real :=
  E * R * E - SMul.smul (1 / 2 : Real) (E * E)

theorem hamiltonian_complementary_covariance_split
    (E R S : Matrix I I Real) (hComp : R + S = 1) :
    E * S * E = SMul.smul (1 / 2 : Real) (E * E) -
      hamiltonianComplementaryCovariance E R := by
  have hSplit : E * R * E + E * S * E = E * E := by
    rw [<- Matrix.add_mul, <- Matrix.mul_add, hComp, Matrix.mul_one]
  have hHalf : SMul.smul (1 / 2 : Real) (E * E) +
      SMul.smul (1 / 2 : Real) (E * E) = E * E := by
    ext i j
    change (1 / 2 : Real) * (E * E) i j + (1 / 2 : Real) * (E * E) i j = (E * E) i j
    ring
  have hOther : E * S * E = E * E - E * R * E := by
    rw [add_comm] at hSplit
    exact eq_sub_of_add_eq hSplit
  unfold hamiltonianComplementaryCovariance
  calc
    _ = E * E - E * R * E := hOther
    _ = (SMul.smul (1 / 2 : Real) (E * E) +
        SMul.smul (1 / 2 : Real) (E * E)) - E * R * E := by rw [hHalf]
    _ = _ := by abel

theorem hamiltonian_complementary_covariance_symmetric
    (E R : Matrix I I Real) (hE : E.transpose = E) (hR : R.transpose = R) :
    (hamiltonianComplementaryCovariance E R).transpose =
      hamiltonianComplementaryCovariance E R := by
  unfold hamiltonianComplementaryCovariance
  have hScalar : (SMul.smul (1 / 2 : Real) (E * E)).transpose =
      SMul.smul (1 / 2 : Real) (E * E).transpose := by ext i j; rfl
  rw [Matrix.transpose_sub, hScalar]
  simp only [Matrix.transpose_mul, hE, hR, Matrix.mul_assoc]

theorem hamiltonian_complementary_restriction_quarter
    (E R S : Matrix I I Real)
    (hE : E.transpose = E) (hR : R.transpose = R) (hS : S.transpose = S)
    (hIdR : R * R = R) (hIdS : S * S = S)
    (hComp : R + S = 1) (hSNorm : norm S <= 1) :
    norm (R * E * S) ^ 2 <=
      norm E ^ 2 / 4 + (3 / 2 : Real) *
        norm (hamiltonianComplementaryCovariance E R) := by
  let F := hamiltonianComplementaryCovariance E R
  let C := R * E * S
  have hGram (M : Matrix I I Real) : norm (M.transpose * M) = norm M ^ 2 := by
    have hConj : M.conjTranspose = M.transpose := by ext i j; rfl
    have h := Matrix.l2_opNorm_conjTranspose_mul_self M
    rw [hConj] at h
    simpa only [pow_two] using h
  have hCoGram (M : Matrix I I Real) : norm (M * M.transpose) = norm M ^ 2 := by
    have h := hGram M.transpose
    rw [Matrix.transpose_transpose, hamiltonian_real_transpose_norm] at h
    exact h
  have hSelf : norm (E * E) = norm E ^ 2 := by
    have h := hGram E
    rw [hE] at h
    exact h
  have hCMatrix : C.transpose * C = S * (E * R * E) * S := by
    dsimp only [C]
    rw [Matrix.transpose_mul, Matrix.transpose_mul, hE, hR, hS]
    calc
      _ = S * E * (R * R) * E * S := by simp only [Matrix.mul_assoc]
      _ = _ := by rw [hIdR]; simp only [Matrix.mul_assoc]
  have hCGram : norm C ^ 2 = norm (S * (E * R * E) * S) :=
    (hGram C).symm.trans (congrArg norm hCMatrix)
  have hESMatrix : (E * S).transpose * (E * S) = S * (E * E) * S := by
    rw [Matrix.transpose_mul, hE, hS]
    simp only [Matrix.mul_assoc]
  have hESGram : norm (E * S) ^ 2 = norm (S * (E * E) * S) :=
    (hGram (E * S)).symm.trans (congrArg norm hESMatrix)
  have hESCoMatrix : (E * S) * (E * S).transpose = E * S * E := by
    rw [Matrix.transpose_mul, hE, hS]
    calc
      _ = E * (S * S) * E := by simp only [Matrix.mul_assoc]
      _ = _ := by rw [hIdS]
  have hESCoGram : norm (E * S) ^ 2 = norm (E * S * E) :=
    (hCoGram (E * S)).symm.trans (congrArg norm hESCoMatrix)
  have hHalfNorm (M : Matrix I I Real) :
      norm (SMul.smul (1 / 2 : Real) M) = (1 / 2 : Real) * norm M := by
    rw [hamiltonian_matrix_real_smul_norm]
    norm_num
  have hSandwich (M : Matrix I I Real) : norm (S * M * S) <= norm M := by
    have hLeft : norm (S * M) <= norm M := by
      calc
        _ <= norm S * norm M := Matrix.l2_opNorm_mul _ _
        _ <= 1 * norm M := mul_le_mul_of_nonneg_right hSNorm (norm_nonneg M)
        _ = _ := one_mul _
    calc
      _ <= norm (S * M) * norm S := Matrix.l2_opNorm_mul _ _
      _ <= norm (S * M) * 1 :=
        mul_le_mul_of_nonneg_left hSNorm (norm_nonneg (S * M))
      _ <= norm M := by simpa only [mul_one] using hLeft
  have hInner : E * R * E = SMul.smul (1 / 2 : Real) (E * E) + F := by
    dsimp only [F, hamiltonianComplementaryCovariance]
    abel
  have hSandwichSplit : S * (E * R * E) * S =
      SMul.smul (1 / 2 : Real) (S * (E * E) * S) + S * F * S := by
    have hLeft (M : Matrix I I Real) :
        S * SMul.smul (1 / 2 : Real) M = SMul.smul (1 / 2 : Real) (S * M) := by
      ext i j
      change Finset.univ.sum (fun k => S i k * ((1 / 2 : Real) * M k j)) =
        (1 / 2 : Real) * Finset.univ.sum (fun k => S i k * M k j)
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro k hk
      ring
    have hRight (M : Matrix I I Real) :
        SMul.smul (1 / 2 : Real) M * S = SMul.smul (1 / 2 : Real) (M * S) := by
      ext i j
      change Finset.univ.sum (fun k => ((1 / 2 : Real) * M i k) * S k j) =
        (1 / 2 : Real) * Finset.univ.sum (fun k => M i k * S k j)
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro k hk
      ring
    rw [hInner, Matrix.mul_add, Matrix.add_mul, hLeft, hRight]
  have hFirst : norm C ^ 2 <= (1 / 2 : Real) * norm (E * S) ^ 2 + norm F := by
    rw [hCGram, hSandwichSplit]
    calc
      _ <= norm (SMul.smul (1 / 2 : Real) (S * (E * E) * S)) + norm (S * F * S) :=
        norm_add_le _ _
      _ = (1 / 2 : Real) * norm (E * S) ^ 2 + norm (S * F * S) := by
        rw [hHalfNorm, <- hESGram]
      _ <= _ := by linarith only [hSandwich F]
  have hSecond : norm (E * S) ^ 2 <= (1 / 2 : Real) * norm E ^ 2 + norm F := by
    rw [hESCoGram, hamiltonian_complementary_covariance_split E R S hComp]
    calc
      _ <= norm (SMul.smul (1 / 2 : Real) (E * E)) +
          norm (hamiltonianComplementaryCovariance E R) := norm_sub_le _ _
      _ = _ := by rw [hHalfNorm, hSelf]
  change norm C ^ 2 <= norm E ^ 2 / 4 + (3 / 2 : Real) * norm F
  nlinarith only [hFirst, hSecond]

end PrimeFactorOscillations

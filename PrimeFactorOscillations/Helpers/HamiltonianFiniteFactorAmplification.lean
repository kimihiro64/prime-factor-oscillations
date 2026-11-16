/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.HamiltonianFiniteFactorGramBound
import PrimeFactorOscillations.Helpers.HamiltonianL2Resolvent
import PrimeFactorOscillations.Helpers.HamiltonianSpectralAmplification

/-! # Finite exceptional modes cost a constant, not an ambient energy factor -/

set_option autoImplicit false
set_option Elab.async false

open scoped Matrix.Norms.L2Operator

noncomputable section

namespace PrimeFactorOscillations

variable {Iota Jota : Type*} [Fintype Iota] [DecidableEq Iota]
variable [Fintype Jota] [DecidableEq Jota]

def hamiltonianMatrixGramAmplification (B : Matrix Iota Iota Real) : Real :=
  Matrix.det (1 + B.transpose * B) / Matrix.det (1 - B.transpose * B)

def hamiltonianFiniteFactorDeterminantCost (k : Nat) (alpha L : Real) : Real :=
  ((2 * k).factorial : Real) * (1 + alpha * (L ^ 2 + L ^ 4)) ^ (2 * k)

theorem hamiltonian_det_nonzero_of_right_inverse
    (M A : Matrix Iota Iota Real) (hInv : M * A = 1) :
    Not (Matrix.det M = 0) := by
  have h : Matrix.det M * Matrix.det A = 1 := by
    rw [<- Matrix.det_mul, hInv, Matrix.det_one]
  intro hZero
  rw [hZero, zero_mul] at h
  norm_num at h

variable [Nonempty Iota]

theorem hamiltonian_neumann_right_inverse
    (Q : Matrix Iota Iota Real) (c : Real) (hQ : norm Q <= c) (hc : c < 1) :
    (1 - Q) * Ring.inverse (1 - Q) = 1 /\
      norm (Ring.inverse (1 - Q)) <= 1 / (1 - c) := by
  have hUnit : IsUnit ((1 : Matrix Iota Iota Real) - Q) :=
    isUnit_one_sub_of_norm_lt_one (lt_of_le_of_lt hQ hc)
  have hInv := Ring.mul_inverse_cancel ((1 : Matrix Iota Iota Real) - Q) hUnit
  have hCert := l2_neumann_certificate Q c hQ hc
  have hGap : 0 < 1 - c := sub_pos.mpr hc
  have hEq : (1 - c) * (1 / (1 - c)) = 1 := by
    field_simp
  refine And.intro hInv ?_
  by_contra h
  have hLess := mul_lt_mul_of_pos_left (lt_of_not_ge h) hGap
  rw [hEq] at hLess
  linarith only [hLess, hCert]

theorem hamiltonian_gram_norm_bound
    (B : Matrix Iota Iota Real) (rho : Real)
    (hRho : 0 <= rho) (hB : norm B <= rho) :
    norm (B.transpose * B) <= rho ^ 2 := by
  have hBt : norm B.transpose <= rho := by
    rw [hamiltonian_real_transpose_norm]
    exact hB
  simpa only [pow_two] using
    hamiltonian_rectangular_product_norm_bound B.transpose B rho rho hRho hBt hB

theorem hamiltonian_finite_factor_amplification_stability
    (B R : Matrix Iota Iota Real) (U : Matrix Iota Jota Real)
    (V : Matrix Jota Iota Real) (rho b L : Real)
    (hRho0 : 0 <= rho) (hRho1 : rho < 1)
    (hb0 : 0 <= b) (hb1 : b < 1) (hL : 0 <= L)
    (hB : B = R + U * V) (hNormB : norm B <= rho)
    (hNormR : norm R <= b) (hU : norm U <= L) (hV : norm V <= L) :
    hamiltonianMatrixGramAmplification B <=
      hamiltonianFiniteFactorDeterminantCost (Fintype.card Jota) (1 / (1 - b ^ 2)) L *
        hamiltonianFiniteFactorDeterminantCost (Fintype.card Jota)
          (1 / (1 - rho ^ 2)) L * hamiltonianMatrixGramAmplification R := by
  have hb2 : b ^ 2 < 1 := by nlinarith only [hb0, hb1]
  have hr2 : rho ^ 2 < 1 := by nlinarith only [hRho0, hRho1]
  have hRGram := hamiltonian_gram_norm_bound R b hb0 hNormR
  have hBGram := hamiltonian_gram_norm_bound B rho hRho0 hNormB
  have hNeg : norm (-(R.transpose * R)) <= b ^ 2 := by simpa only [norm_neg] using hRGram
  have hp := hamiltonian_neumann_right_inverse (-(R.transpose * R)) (b ^ 2) hNeg hb2
  simp only [sub_neg_eq_add] at hp
  have hm := hamiltonian_neumann_right_inverse (B.transpose * B) (rho ^ 2) hBGram hr2
  have hAlphaP : 0 <= 1 / (1 - b ^ 2) := le_of_lt (one_div_pos.mpr (sub_pos.mpr hb2))
  have hAlphaM : 0 <= 1 / (1 - rho ^ 2) := le_of_lt (one_div_pos.mpr (sub_pos.mpr hr2))
  have hP := hamiltonian_gram_determinant_update_bound B R (1 + R.transpose * R)
    (Ring.inverse (1 + R.transpose * R)) U V (1 / (1 - b ^ 2)) L hB hp.1
      hAlphaP hL (hNormR.trans (le_of_lt hb1)) hp.2 hU hV
  have hM := hamiltonian_gram_determinant_update_bound B R (1 - B.transpose * B)
    (Ring.inverse (1 - B.transpose * B)) U V (1 / (1 - rho ^ 2)) L hB hm.1
      hAlphaM hL (hNormR.trans (le_of_lt hb1)) hm.2 hU hV
  have heP : (1 + R.transpose * R) + (B.transpose * B - R.transpose * R) =
      1 + B.transpose * B := by abel
  have heM : (1 - B.transpose * B) + (B.transpose * B - R.transpose * R) =
      1 - R.transpose * R := by abel
  rw [heP] at hP
  rw [heM] at hM
  have hPB : abs (Matrix.det (1 + B.transpose * B) / Matrix.det (1 + R.transpose * R)) <=
      hamiltonianFiniteFactorDeterminantCost (Fintype.card Jota) (1 / (1 - b ^ 2)) L := by
    simpa only [hamiltonianFiniteFactorDeterminantCost, Fintype.card_sum, two_mul] using hP
  have hMB : abs (Matrix.det (1 - R.transpose * R) / Matrix.det (1 - B.transpose * B)) <=
      hamiltonianFiniteFactorDeterminantCost (Fintype.card Jota) (1 / (1 - rho ^ 2)) L := by
    simpa only [hamiltonianFiniteFactorDeterminantCost, Fintype.card_sum, two_mul] using hM
  have hRp := hamiltonian_det_nonzero_of_right_inverse _ _ hp.1
  have hRm : Not (Matrix.det (1 - R.transpose * R) = 0) := by
    have hu := hamiltonian_neumann_right_inverse (R.transpose * R) (b ^ 2) hRGram hb2
    exact hamiltonian_det_nonzero_of_right_inverse _ _ hu.1
  have hPosB : 0 < hamiltonianMatrixGramAmplification B :=
    (hamiltonian_matrix_gram_amplification B rho hRho0 hRho1 hNormB).1
  have hPosR : 0 < hamiltonianMatrixGramAmplification R :=
    (hamiltonian_matrix_gram_amplification R b hb0 hb1 hNormR).1
  have hIdentity : hamiltonianMatrixGramAmplification B =
      (Matrix.det (1 + B.transpose * B) / Matrix.det (1 + R.transpose * R)) *
        (Matrix.det (1 - R.transpose * R) / Matrix.det (1 - B.transpose * B)) *
          hamiltonianMatrixGramAmplification R := by
    unfold hamiltonianMatrixGramAmplification
    field_simp
  calc
    _ = abs (hamiltonianMatrixGramAmplification B) := (abs_of_pos hPosB).symm
    _ = abs (Matrix.det (1 + B.transpose * B) / Matrix.det (1 + R.transpose * R)) *
        abs (Matrix.det (1 - R.transpose * R) / Matrix.det (1 - B.transpose * B)) *
          hamiltonianMatrixGramAmplification R := by
      rw [hIdentity, abs_mul, abs_mul, abs_of_pos hPosR]
    _ <= _ := mul_le_mul_of_nonneg_right
      (mul_le_mul hPB hMB (abs_nonneg _) ((abs_nonneg _).trans hPB)) (le_of_lt hPosR)

theorem hamiltonian_finite_factor_amplification_energy_bound
    (B R : Matrix Iota Iota Real) (U : Matrix Iota Jota Real)
    (V : Matrix Jota Iota Real) (rho b L : Real)
    (hRho0 : 0 <= rho) (hRho1 : rho < 1)
    (hb0 : 0 <= b) (hb1 : b < 1) (hL : 0 <= L)
    (hB : B = R + U * V) (hNormB : norm B <= rho)
    (hNormR : norm R <= b) (hU : norm U <= L) (hV : norm V <= L) :
    hamiltonianMatrixGramAmplification B <=
      (hamiltonianFiniteFactorDeterminantCost (Fintype.card Jota) (1 / (1 - b ^ 2)) L *
        hamiltonianFiniteFactorDeterminantCost (Fintype.card Jota)
          (1 / (1 - rho ^ 2)) L *
        Real.exp (hamiltonianSpectralKappa b *
          (2 * (Fintype.card Jota : Real) * rho * L ^ 2 +
            (Fintype.card Jota : Real) * L ^ 4))) *
      Real.exp (hamiltonianSpectralKappa b *
        Finset.univ.sum (fun i => Finset.univ.sum (fun j => B i j ^ 2))) := by
  let D := hamiltonianFiniteFactorDeterminantCost (Fintype.card Jota) (1 / (1 - b ^ 2)) L *
    hamiltonianFiniteFactorDeterminantCost (Fintype.card Jota) (1 / (1 - rho ^ 2)) L
  have hStable := hamiltonian_finite_factor_amplification_stability B R U V rho b L
    hRho0 hRho1 hb0 hb1 hL hB hNormB hNormR hU hV
  have hb2 : b ^ 2 < 1 := by nlinarith only [hb0, hb1]
  have hr2 : rho ^ 2 < 1 := by nlinarith only [hRho0, hRho1]
  have hAlphaP : 0 <= 1 / (1 - b ^ 2) := le_of_lt (one_div_pos.mpr (sub_pos.mpr hb2))
  have hAlphaM : 0 <= 1 / (1 - rho ^ 2) := le_of_lt (one_div_pos.mpr (sub_pos.mpr hr2))
  have hD : 0 <= D := by
    dsimp [D, hamiltonianFiniteFactorDeterminantCost]
    positivity
  have hAmp := (hamiltonian_matrix_gram_amplification R b hb0 hb1 hNormR).2
  rw [realGramEigenvalues_sum_eq_energy] at hAmp
  have hE := hamiltonian_finite_factor_energy_bound B R U V rho L
    hRho0 hL hB hNormB hU hV
  have hK := hamiltonian_spectral_kappa_nonnegative b hb0 hb1
  have hScaled := mul_le_mul_of_nonneg_left hE hK
  have hExp : Real.exp (hamiltonianSpectralKappa b *
      Finset.univ.sum (fun i => Finset.univ.sum (fun j => R i j ^ 2))) <=
      Real.exp (hamiltonianSpectralKappa b *
        (2 * (Fintype.card Jota : Real) * rho * L ^ 2 +
          (Fintype.card Jota : Real) * L ^ 4)) *
      Real.exp (hamiltonianSpectralKappa b *
        Finset.univ.sum (fun i => Finset.univ.sum (fun j => B i j ^ 2))) := by
    rw [<- Real.exp_add]
    apply Real.exp_le_exp.mpr
    nlinarith only [hScaled]
  change hamiltonianMatrixGramAmplification B <=
    (D * Real.exp _) * Real.exp _
  calc
    _ <= D * hamiltonianMatrixGramAmplification R := hStable
    _ <= D * Real.exp (hamiltonianSpectralKappa b *
        Finset.univ.sum (fun i => Finset.univ.sum (fun j => R i j ^ 2))) :=
      mul_le_mul_of_nonneg_left hAmp hD
    _ <= D * (Real.exp _ * Real.exp _) := mul_le_mul_of_nonneg_left hExp hD
    _ = _ := by ring

end PrimeFactorOscillations

/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.HamiltonianRepairedCovarianceTransport

/-! # Exact determinant and logarithmic Gaussian-normalizer transport

The actual repaired determinant is identified before its signed cost
is combined with the physical scaling and permanent corrections.
-/

set_option autoImplicit false
set_option Elab.async false

open scoped Matrix.Norms.L2Operator

noncomputable section

namespace PrimeFactorOscillations

variable {Iota : Type*} [Fintype Iota] [DecidableEq Iota]

theorem hamiltonian_block_determinant_positive (B : Matrix Iota Iota Real)
    (rho : Real) (hNorm : norm B <= rho) (hRho : rho < 1) :
    0 < Matrix.det ((1 : Matrix (Sum Iota Iota) (Sum Iota Iota) Real) + bipartiteLift B) := by
  let M := bipartiteLift B
  let hM := bipartiteLift_hermitian B
  have hMNorm : norm M <= rho := le_trans (bipartiteLift_l2_norm_le B) hNorm
  have hPos (i : Sum Iota Iota) : 0 < 1 + hM.eigenvalues i := by
    have hAbs : abs (hM.eigenvalues i) <= rho :=
      le_trans (realGaussianEigenvalue_abs_le_norm M hM i) hMNorm
    have hLower := (abs_le.mp hAbs).1
    linarith only [hLower, hRho]
  have hDet : Matrix.det ((1 : Matrix (Sum Iota Iota) (Sum Iota Iota) Real) + M) =
      Finset.univ.prod (fun i => 1 + hM.eigenvalues i) := by
    simpa only [neg_smul, sub_neg_eq_add, neg_mul, one_smul, one_mul] using
      hermitian_det_one_sub_smul M hM (-1)
  rw [hDet]
  exact Finset.prod_pos (fun i hi => hPos i)

theorem hamiltonian_log_real_gram_factor (B : Matrix Iota Iota Real)
    (rho : Real) (hNorm : norm B <= rho) (hRho : rho < 1) :
    Real.log (realGramDeterminantFactor B 1) =
      -(1 / 2 : Real) *
        Real.log (Matrix.det ((1 : Matrix (Sum Iota Iota) (Sum Iota Iota) Real) + bipartiteLift B)) := by
  have hDet := hamiltonian_block_determinant_positive B rho hNorm hRho
  have hFactor : realGramDeterminantFactor B 1 = hermitianDeterminantFactor (bipartiteLift B) 1 := by
    unfold realGramDeterminantFactor hermitianDeterminantFactor
    rw [det_one_add_bipartiteLift]
  rw [hFactor]
  unfold hermitianDeterminantFactor
  simp only [one_smul]
  change Real.log ((Matrix.det ((1 : Matrix (Sum Iota Iota) (Sum Iota Iota) Real) +
    bipartiteLift B)) ^ (-(1 / 2 : Real))) = _
  rw [Real.rpow_def_of_pos hDet, Real.log_exp]
  ring

theorem hamiltonian_repaired_centered_determinant
    (T : Matrix Iota Iota Real) (S U : Finset Iota) (hCard : S.card = U.card)
    (z : forall _i : (Compl.compl (S.disjSum U) : Finset (Sum Iota Iota)), Real)
    (q qNew : Real) :
    let R : Finset (Sum Iota Iota) := Compl.compl (S.disjSum U)
    let H := (1 : Matrix (Sum Iota Iota) (Sum Iota Iota) Real) +
      bipartiteLift (centeredKernel T q)
    let HR := H.submatrix (fun i : R => i.val) (fun i : R => i.val)
    let E := hamiltonianScalingPerturbation (hamiltonianRetainedKernel T S U)
      (hamiltonianRetainedCrossMask S U) z q qNew
    Matrix.det (HR + E) =
      Matrix.det ((1 : Matrix
        (Sum (Compl.compl U : Finset Iota) (Compl.compl U : Finset Iota))
        (Sum (Compl.compl U : Finset Iota) (Compl.compl U : Finset Iota)) Real) +
          bipartiteLift (centeredKernel (hamiltonianRepairedSquareKernel T S U hCard z) qNew)) := by
  let R : Finset (Sum Iota Iota) := Compl.compl (S.disjSum U)
  let e := hamiltonianRepairedSquareEquiv S U hCard
  let H := (1 : Matrix (Sum Iota Iota) (Sum Iota Iota) Real) +
    bipartiteLift (centeredKernel T q)
  let HR := H.submatrix (fun i : R => i.val) (fun i : R => i.val)
  let E := hamiltonianScalingPerturbation (hamiltonianRetainedKernel T S U)
    (hamiltonianRetainedCrossMask S U) z q qNew
  have hOne : (1 : Matrix R R Real).submatrix e e = 1 := by
    apply Matrix.ext
    intro i j
    simp only [Matrix.submatrix_apply, Matrix.one_apply, e.injective.eq_iff]
  have hCentered := hamiltonian_repaired_centered_reindex T S U hCard z q qNew
  have hSplit : HR + E = (1 : Matrix R R Real) + (HR + E - 1) := by abel
  have hMatrix : (HR + E).submatrix e e =
      1 + bipartiteLift (centeredKernel (hamiltonianRepairedSquareKernel T S U hCard z) qNew) := by
    rw [hSplit]
    change (1 : Matrix R R Real).submatrix e e + (HR + E - 1).submatrix e e = _
    rw [hOne, hCentered]
  have h := Matrix.det_submatrix_equiv_self e (HR + E)
  rw [hMatrix] at h
  exact h.symm

theorem stochastic_repaired_log_gram_ratio [Nonempty Iota]
    (T : Matrix Iota Iota Real) (S U : Finset Iota) (hCard : S.card = U.card)
    (q a rho : Real) (hq : (Fintype.card Iota : Real) * q = 1) (ha : 1 <= a)
    (hNonneg : forall i j, 0 <= T i j) (hUpper : forall i j, T i j <= a * q)
    (hNorm : norm (centeredKernel T q) <= rho) (hRho : rho < 1)
    (hSmall : (U.card : Real) * (a / (1 - rho)) ^ 3 * q <= 1 / 10000)
    (z : forall _i : (Compl.compl (S.disjSum U) : Finset (Sum Iota Iota)), Real)
    (hZ : norm z <= 20 * (U.card : Real) * a * q / (1 - rho)) :
    let R : Finset (Sum Iota Iota) := Compl.compl (S.disjSum U)
    let H := (1 : Matrix (Sum Iota Iota) (Sum Iota Iota) Real) +
      bipartiteLift (centeredKernel T q)
    let HR := H.submatrix (fun i : R => i.val) (fun i : R => i.val)
    let qNew := q / (1 - (U.card : Real) * q)
    let E := hamiltonianScalingPerturbation (hamiltonianRetainedKernel T S U)
      (hamiltonianRetainedCrossMask S U) z q qNew
    2 * (Real.log (realGramDeterminantFactor
        (centeredKernel (hamiltonianRepairedSquareKernel T S U hCard z) qNew) 1) -
      Real.log (realGramDeterminantFactor (centeredKernel T q) 1)) =
        -Real.log (Matrix.det (HR + E) / Matrix.det H) := by
  let R : Finset (Sum Iota Iota) := Compl.compl (S.disjSum U)
  let H := (1 : Matrix (Sum Iota Iota) (Sum Iota Iota) Real) +
    bipartiteLift (centeredKernel T q)
  let HR := H.submatrix (fun i : R => i.val) (fun i : R => i.val)
  let qNew := q / (1 - (U.card : Real) * q)
  let E := hamiltonianScalingPerturbation (hamiltonianRetainedKernel T S U)
    (hamiltonianRetainedCrossMask S U) z q qNew
  let BNew := centeredKernel (hamiltonianRepairedSquareKernel T S U hCard z) qNew
  let HNew := (1 : Matrix
      (Sum (Compl.compl U : Finset Iota) (Compl.compl U : Finset Iota))
      (Sum (Compl.compl U : Finset Iota) (Compl.compl U : Finset Iota)) Real) +
    bipartiteLift BNew
  have hNewNorm : norm BNew <= 1 - (1 - rho) / 2 :=
    stochastic_repaired_square_gap T S U hCard q a rho hq ha hNonneg hUpper
      hNorm hRho hSmall z hZ
  have hNewRho : 1 - (1 - rho) / 2 < 1 := by linarith only [hRho]
  have hOldPositive : 0 < Matrix.det H :=
    hamiltonian_block_determinant_positive _ rho hNorm hRho
  have hNewPositive : 0 < Matrix.det HNew :=
    hamiltonian_block_determinant_positive BNew _ hNewNorm hNewRho
  have hDet : Matrix.det (HR + E) = Matrix.det HNew :=
    hamiltonian_repaired_centered_determinant T S U hCard z q qNew
  have hOldLog := hamiltonian_log_real_gram_factor _ rho hNorm hRho
  have hNewLog := hamiltonian_log_real_gram_factor BNew _ hNewNorm hNewRho
  change 2 * (Real.log (realGramDeterminantFactor BNew 1) -
    Real.log (realGramDeterminantFactor (centeredKernel T q) 1)) =
      -Real.log (Matrix.det (HR + E) / Matrix.det H)
  rw [hDet, Real.log_div (ne_of_gt hNewPositive) (ne_of_gt hOldPositive), hNewLog, hOldLog]
  ring

end PrimeFactorOscillations

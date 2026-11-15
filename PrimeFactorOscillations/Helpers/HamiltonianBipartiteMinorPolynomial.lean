/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import Mathlib.Algebra.Polynomial.Eval.Defs
import PrimeFactorOscillations.Helpers.HamiltonianBipartiteDeterminant
import PrimeFactorOscillations.Helpers.HamiltonianRectangularMinors

/-! # Exact bipartite principal-minor signs and balance

The full determinant polynomial retains every selected support. Its
coefficient expansion proves that unbalanced parts have zero determinant
and that a balanced square lift has the actual signed determinant square.
These identities feed the bipartite specialization of the full Liu sum.
-/

set_option autoImplicit false
set_option Elab.async false

noncomputable section

namespace PrimeFactorOscillations

variable {Iota Jota R : Type*}
variable [Fintype Iota] [DecidableEq Iota]
variable [Fintype Jota] [DecidableEq Jota] [CommRing R]

theorem hamiltonianPrincipalPolynomial_comp (M : Matrix Iota Iota R)
    (g : Polynomial R) :
    (principalMinorGeneratingPolynomial M).comp g =
      Matrix.det (1 + HSMul.hSMul g (M.map Polynomial.C)) := by
  classical
  change (Polynomial.compRingHom g)
    (Matrix.det (1 + HSMul.hSMul (Polynomial.X : Polynomial R) (M.map Polynomial.C))) = _
  rw [RingHom.map_det]
  congr 1
  apply Matrix.ext
  intro i j
  change (((1 : Matrix Iota Iota (Polynomial R)) i j) +
      Polynomial.X * Polynomial.C (M i j)).comp g =
    ((1 : Matrix Iota Iota (Polynomial R)) i j) + g * Polynomial.C (M i j)
  rw [Polynomial.add_comp, Polynomial.mul_comp, Polynomial.X_comp, Polynomial.C_comp]
  congr 1
  by_cases h : i = j <;> simp [Matrix.one_apply, h]

theorem hamiltonian_monomial_comp_neg_X_sq (k : Nat) (a : R) :
    (Polynomial.monomial k a).comp (-((Polynomial.X : Polynomial R) ^ 2)) =
      Polynomial.monomial (2 * k) ((-1 : R) ^ k * a) := by
  rw [<- Polynomial.C_mul_X_pow_eq_monomial, <- Polynomial.C_mul_X_pow_eq_monomial]
  rw [Polynomial.C_mul_comp, Polynomial.X_pow_comp,
    neg_pow ((Polynomial.X : Polynomial R) ^ 2) k,
    pow_mul (Polynomial.X : Polynomial R) 2 k]
  simp only [map_mul, map_pow, map_neg, map_one]
  ring

theorem hamiltonianBipartitePolynomial_as_gram_comp (T : Matrix Iota Jota R) :
    principalMinorGeneratingPolynomial (bipartiteLift T) =
      (principalMinorGeneratingPolynomial (T.transpose * T)).comp
        (-((Polynomial.X : Polynomial R) ^ 2)) := by
  classical
  rw [principalMinorGeneratingPolynomial_bipartite, hamiltonianPrincipalPolynomial_comp]
  congr 1
  apply Matrix.ext
  intro i j
  simp only [Matrix.sub_apply, Matrix.add_apply, Matrix.smul_apply, Matrix.map_apply,
    Matrix.mul_apply, Matrix.transpose_apply, map_sum, map_mul, smul_eq_mul,
    neg_mul, sub_eq_add_neg]

theorem hamiltonianBipartitePolynomial_expansion (T : Matrix Iota Jota R) :
    principalMinorGeneratingPolynomial (bipartiteLift T) =
      Finset.sum Finset.univ (fun S : Finset Jota =>
        Polynomial.monomial (2 * S.card)
          ((-1 : R) ^ S.card * principalMinorDet (T.transpose * T) S)) := by
  classical
  rw [hamiltonianBipartitePolynomial_as_gram_comp, principalMinorGeneratingPolynomial_eq]
  change (Polynomial.compRingHom (-((Polynomial.X : Polynomial R) ^ 2)))
    (Finset.sum Finset.univ
      (fun S : Finset Jota => Polynomial.monomial S.card (principalMinorDet (T.transpose * T) S))) = _
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro S hS
  exact hamiltonian_monomial_comp_neg_X_sq S.card (principalMinorDet (T.transpose * T) S)

theorem hamiltonianBipartiteDet_zero_of_right_smaller (T : Matrix Iota Jota R)
    (hSize : Fintype.card Jota < Fintype.card Iota) :
    Matrix.det (bipartiteLift T) = 0 := by
  classical
  rw [<- principalMinor_topCoefficient (bipartiteLift T),
    hamiltonianBipartitePolynomial_expansion, Polynomial.finsetSum_coeff]
  apply Finset.sum_eq_zero
  intro S hS
  have hc : S.card <= Fintype.card Jota := by
    simpa only [Finset.card_univ] using Finset.card_le_card (Finset.subset_univ S)
  have hNe : Not (2 * S.card = Fintype.card (Sum Iota Jota)) := by
    rw [Fintype.card_sum]
    omega
  simp only [Polynomial.coeff_monomial, if_neg hNe, if_neg (Ne.symm hNe)]

theorem hamiltonianBipartiteDet_transpose (T : Matrix Iota Jota R) :
    Matrix.det (bipartiteLift T.transpose) = Matrix.det (bipartiteLift T) := by
  classical
  have h := Matrix.det_submatrix_equiv_self (Equiv.sumComm Jota Iota) (bipartiteLift T)
  have hMatrix : (bipartiteLift T).submatrix (Equiv.sumComm Jota Iota)
      (Equiv.sumComm Jota Iota) = bipartiteLift T.transpose := by
    apply Matrix.ext
    intro i j
    cases i <;> cases j <;> rfl
  rw [hMatrix] at h
  exact h

theorem hamiltonianBipartiteDet_zero_of_unbalanced (T : Matrix Iota Jota R)
    (hSize : Not (Fintype.card Iota = Fintype.card Jota)) :
    Matrix.det (bipartiteLift T) = 0 := by
  rcases Nat.lt_or_gt_of_ne hSize with hLt | hGt
  next =>
    rw [<- hamiltonianBipartiteDet_transpose]
    exact hamiltonianBipartiteDet_zero_of_right_smaller T.transpose hLt
  next =>
    exact hamiltonianBipartiteDet_zero_of_right_smaller T hGt

theorem hamiltonianBipartiteDet_square (T : Matrix Iota Iota R) :
    Matrix.det (bipartiteLift T) =
      (-1 : R) ^ Fintype.card Iota * Matrix.det T ^ 2 := by
  classical
  rw [<- principalMinor_topCoefficient (bipartiteLift T),
    hamiltonianBipartitePolynomial_expansion, Polynomial.finsetSum_coeff]
  rw [Finset.sum_eq_single Finset.univ]
  next =>
    simp only [Finset.card_univ, Fintype.card_sum, two_mul,
      Polynomial.coeff_monomial, ite_true]
    rw [principalMinorDet_univ, Matrix.det_mul, Matrix.det_transpose, pow_two]
  next =>
    intro S hS hNot
    have hc : Not (S.card = Fintype.card Iota) := by
      intro h
      apply hNot
      apply Finset.eq_of_subset_of_card_le (Finset.subset_univ S)
      simpa only [Finset.card_univ, h] using (Nat.le_refl (Fintype.card Iota))
    have hNe : Not (2 * S.card = Fintype.card (Sum Iota Iota)) := by
      rw [Fintype.card_sum]
      omega
    simp only [Polynomial.coeff_monomial, if_neg hNe, if_neg (Ne.symm hNe)]
  next =>
    intro h
    exact False.elim (h (Finset.mem_univ _))

end PrimeFactorOscillations

/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.HamiltonianSignedGramMoments

/-! # Rectangular squared minors and the signed stochastic cancellation

Cauchy--Binet is derived from the polynomial Sylvester identity and the
principal-minor coefficient formula. Both supports are actual finite subsets;
the choice of equal-cardinality enumeration disappears after squaring.
The final theorem applies the stochastic parity cancellation to the full
signed two-support sum, before any absolute estimate.
-/

set_option autoImplicit false
set_option Elab.async false

noncomputable section

namespace PrimeFactorOscillations

variable {Iota Jota R : Type*}
variable [DecidableEq Iota] [Fintype Iota]
variable [DecidableEq Jota] [Fintype Jota] [CommRing R]

theorem principalMinorDet_univ (M : Matrix Iota Iota R) :
    principalMinorDet M Finset.univ = Matrix.det M := by
  classical
  let e : Equiv (Finset.univ : Finset Iota) Iota := by
    exact
      { toFun := Subtype.val
        invFun := fun i => Subtype.mk i (Finset.mem_univ i)
        left_inv := fun i => Subtype.ext rfl
        right_inv := fun i => rfl }
  exact Matrix.det_submatrix_equiv_self e M

theorem principalMinor_topCoefficient (M : Matrix Iota Iota R) :
    (principalMinorGeneratingPolynomial M).coeff (Fintype.card Iota) =
      Matrix.det M := by
  classical
  unfold principalMinorGeneratingPolynomial
  rw [Matrix.coeff_det_one_add_X_smul_eq_sum_minors]
  have hFull : (Finset.univ : Finset Iota).powersetCard (Fintype.card Iota) =
      {Finset.univ} := by
    ext S
    simp only [Finset.mem_powersetCard, Finset.mem_singleton]
    constructor
    case mp =>
      intro h
      exact Finset.eq_of_subset_of_card_le h.1 (by
        simpa only [Finset.card_univ] using Nat.le_of_eq h.2.symm)
    case mpr =>
      intro h
      subst S
      simp
  rw [hFull, Finset.sum_singleton]
  exact principalMinorDet_univ M

theorem principalMinorPolynomial_mul_comm
    (A : Matrix Iota Jota R) (B : Matrix Jota Iota R) :
    principalMinorGeneratingPolynomial (A * B) =
      principalMinorGeneratingPolynomial (B * A) := by
  unfold principalMinorGeneratingPolynomial
  have hLeft :
      HSMul.hSMul (Polynomial.X : Polynomial R) ((A * B).map Polynomial.C) =
        HSMul.hSMul (Polynomial.X : Polynomial R) (A.map Polynomial.C) *
          B.map Polynomial.C := by
    apply Matrix.ext
    intro i j
    simp only [Matrix.map_apply, Matrix.mul_apply, Matrix.smul_apply,
      smul_eq_mul, map_sum, map_mul, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k hk
    ring
  have hRight :
      HSMul.hSMul (Polynomial.X : Polynomial R) ((B * A).map Polynomial.C) =
        B.map Polynomial.C *
          HSMul.hSMul (Polynomial.X : Polynomial R) (A.map Polynomial.C) := by
    apply Matrix.ext
    intro i j
    simp only [Matrix.map_apply, Matrix.mul_apply, Matrix.smul_apply,
      smul_eq_mul, map_sum, map_mul, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k hk
    ring
  rw [hLeft, hRight]
  exact Matrix.det_one_add_mul_comm _ _

theorem rectangularProduct_det_as_principalMinors
    (A : Matrix Iota Jota R) (B : Matrix Jota Iota R) :
    Matrix.det (A * B) =
      Finset.sum (Finset.univ.powersetCard (Fintype.card Iota))
        (fun S => principalMinorDet (B * A) S) := by
  rw [<- principalMinor_topCoefficient (A * B),
    principalMinorPolynomial_mul_comm]
  exact Matrix.coeff_det_one_add_X_smul_eq_sum_minors (B * A) (Fintype.card Iota)

def equalCardMinorEquiv (S J : Finset Iota) (h : S.card = J.card) : Equiv J S :=
  Fintype.equivOfCardEq (by simpa only [Fintype.card_coe] using h.symm)

def rectangularMinorDet (T : Matrix Iota Iota R) (S J : Finset Iota) : R :=
  if h : S.card = J.card then
    Matrix.det (T.submatrix
      (fun i : J => (equalCardMinorEquiv S J h i).val)
      (Subtype.val : J -> Iota))
  else 0

theorem gramPrincipalMinor_eq_rectangularSquares
    (T : Matrix Iota Iota R) (J : Finset Iota) :
    principalMinorDet (T.transpose * T) J =
      Finset.sum (Finset.univ.powersetCard J.card)
        (fun S => rectangularMinorDet T S J ^ 2) := by
  classical
  let A : Matrix J Iota R :=
    T.transpose.submatrix (Subtype.val : J -> Iota) id
  let B : Matrix Iota J R :=
    T.submatrix id (Subtype.val : J -> Iota)
  have hProduct : (T.transpose * T).submatrix
      (Subtype.val : J -> Iota) (Subtype.val : J -> Iota) = A * B := by
    ext i j
    rfl
  unfold principalMinorDet
  rw [hProduct, rectangularProduct_det_as_principalMinors A B]
  simp only [Fintype.card_coe]
  apply Finset.sum_congr rfl
  intro S hS
  have hCard : S.card = J.card := (Finset.mem_powersetCard.mp hS).2
  let e : Equiv J S := equalCardMinorEquiv S J hCard
  let U : Matrix J J R :=
    T.submatrix (fun i => (e i).val) (Subtype.val : J -> Iota)
  have hReindex :
      (((B * A).submatrix (Subtype.val : S -> Iota)
        (Subtype.val : S -> Iota)).submatrix e e) = U * U.transpose := by
    ext i j
    rfl
  unfold rectangularMinorDet
  rw [dite_eq_left hCard]
  change principalMinorDet (B * A) S = Matrix.det U ^ 2
  unfold principalMinorDet
  rw [<- Matrix.det_submatrix_equiv_self e, hReindex,
    Matrix.det_mul, Matrix.det_transpose, pow_two]

def signedRectangularMinorMoment (T : Matrix Iota Iota R) : R :=
  -Finset.sum Finset.univ (fun J : Finset Iota =>
    (-1 : R) ^ J.card * (J.card : R) *
      Finset.sum (Finset.univ.powersetCard J.card)
        (fun S => rectangularMinorDet T S J ^ 2))

theorem signedRectangularMinorMoment_eq_centeredDet
    (T : Matrix Iota Iota R) (q : R)
    (hq : (Fintype.card Iota : R) * q = 1)
    (hrow : forall i, Finset.sum Finset.univ (fun j => T i j) = 1)
    (hcol : forall j, Finset.sum Finset.univ (fun i => T i j) = 1) :
    signedRectangularMinorMoment T =
      Matrix.det (1 - (centeredKernel T q).transpose * centeredKernel T q) := by
  have hMoment : signedRectangularMinorMoment T = signedGramMinorMoment T := by
    unfold signedRectangularMinorMoment signedGramMinorMoment
    congr 1
    apply Finset.sum_congr rfl
    intro J hJ
    rw [gramPrincipalMinor_eq_rectangularSquares]
  rw [hMoment]
  exact signedGramMinorMoment_eq_centeredDet T q hq hrow hcol

end PrimeFactorOscillations

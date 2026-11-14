/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.HamiltonianStochasticParity

/-! # Signed Gram-minor moments from balance

The parity factor is proved from row and column balance and then consumed in
the actual Gram-minor generating polynomial. All principal minors and their
cardinality weights remain in the finite sum. No spectral estimate or desired
moment identity is installed as a premise.
-/

set_option autoImplicit false
set_option Elab.async false

noncomputable section

namespace PrimeFactorOscillations

variable {Iota R : Type*} [DecidableEq Iota] [Fintype Iota] [CommRing R]

def gramDeterminantPolynomial (T : Matrix Iota Iota R) : Polynomial R :=
  Matrix.det ((1 : Matrix Iota Iota (Polynomial R)) -
    HSMul.hSMul (Polynomial.X : Polynomial R)
      ((T.map Polynomial.C).transpose * T.map Polynomial.C))

theorem gramDeterminantPolynomial_as_minors (T : Matrix Iota Iota R) :
    gramDeterminantPolynomial T =
      principalMinorGeneratingPolynomial (-(T.transpose * T)) := by
  unfold gramDeterminantPolynomial principalMinorGeneratingPolynomial
  congr 1
  ext i j
  simp [Matrix.map_apply, Matrix.mul_apply, Matrix.transpose_apply,
    Matrix.one_apply, Matrix.smul_apply, smul_eq_mul, sub_eq_add_neg]

theorem gramDeterminantPolynomial_eval_one (T : Matrix Iota Iota R) :
    Polynomial.eval 1 (gramDeterminantPolynomial T) =
      Matrix.det (1 - T.transpose * T) := by
  unfold gramDeterminantPolynomial
  change (Polynomial.evalRingHom (1 : R)) (Matrix.det _) = _
  rw [RingHom.map_det]
  congr 1
  ext i j
  change Polynomial.eval (1 : R)
    (((1 : Matrix Iota Iota (Polynomial R)) -
      HSMul.hSMul (Polynomial.X : Polynomial R)
        ((T.map Polynomial.C).transpose * T.map Polynomial.C)) i j) = _
  by_cases h : i = j <;>
    simp [Matrix.map_apply, Matrix.mul_apply, Matrix.transpose_apply,
      Matrix.smul_apply, smul_eq_mul, Polynomial.eval_finsetSum, h]

theorem gramDeterminantPolynomial_parityFactor (T : Matrix Iota Iota R) (q : R)
    (hq : (Fintype.card Iota : R) * q = 1)
    (hrow : forall i, Finset.sum Finset.univ (fun j => T i j) = 1)
    (hcol : forall j, Finset.sum Finset.univ (fun i => T i j) = 1) :
    gramDeterminantPolynomial T =
      (1 - Polynomial.X) * gramDeterminantPolynomial (centeredKernel T q) := by
  have hqPoly : (Fintype.card Iota : Polynomial R) * Polynomial.C q = 1 := by
    simpa only [map_mul, map_natCast, map_one] using
      congrArg (Polynomial.C : R -> Polynomial R) hq
  have hrowPoly : forall i,
      Finset.sum Finset.univ (fun j => (T.map Polynomial.C) i j) = 1 := by
    intro i
    simpa only [map_sum, map_one, Matrix.map_apply] using
      congrArg (Polynomial.C : R -> Polynomial R) (hrow i)
  have hcolPoly : forall j,
      Finset.sum Finset.univ (fun i => (T.map Polynomial.C) i j) = 1 := by
    intro j
    simpa only [map_sum, map_one, Matrix.map_apply] using
      congrArg (Polynomial.C : R -> Polynomial R) (hcol j)
  have hCenter : centeredKernel (T.map Polynomial.C) (Polynomial.C q) =
      (centeredKernel T q).map Polynomial.C := by
    ext i j
    simp [centeredKernel, averagingKernel, Matrix.map_apply]
  unfold gramDeterminantPolynomial
  have h := stochasticGram_parityFactor (T.map Polynomial.C) (Polynomial.C q)
    hqPoly hrowPoly hcolPoly (Polynomial.X : Polynomial R)
  rw [hCenter] at h
  exact h

theorem gramEuler_eval (T : Matrix Iota Iota R) (t : R) :
    Polynomial.eval t (polynomialEuler (gramDeterminantPolynomial T)) =
      Finset.sum Finset.univ (fun S : Finset Iota =>
        (S.card : R) * (-1 : R) ^ S.card *
          principalMinorDet (T.transpose * T) S * t ^ S.card) := by
  rw [gramDeterminantPolynomial_as_minors,
    principalMinor_euler_eval (-(T.transpose * T)) t]
  apply Finset.sum_congr rfl
  intro S hS
  simp only [principalMinorDet, Matrix.submatrix_neg, Pi.neg_apply,
    Matrix.det_neg, Fintype.card_coe]
  ring

def signedGramMinorMoment (T : Matrix Iota Iota R) : R :=
  -Finset.sum Finset.univ (fun S : Finset Iota =>
    (-1 : R) ^ S.card * (S.card : R) * principalMinorDet (T.transpose * T) S)

theorem signedGramMinorMoment_eq_centeredDet (T : Matrix Iota Iota R) (q : R)
    (hq : (Fintype.card Iota : R) * q = 1)
    (hrow : forall i, Finset.sum Finset.univ (fun j => T i j) = 1)
    (hcol : forall j, Finset.sum Finset.univ (fun i => T i j) = 1) :
    signedGramMinorMoment T =
      Matrix.det (1 - (centeredKernel T q).transpose * centeredKernel T q) := by
  have hMoment : signedGramMinorMoment T =
      -Polynomial.eval 1 (polynomialEuler (gramDeterminantPolynomial T)) := by
    rw [gramEuler_eval]
    unfold signedGramMinorMoment
    congr 1
    apply Finset.sum_congr rfl
    intro S hS
    simp only [one_pow, mul_one]
    ring
  calc
    _ = -Polynomial.eval 1 (polynomialEuler (gramDeterminantPolynomial T)) := hMoment
    _ = Polynomial.eval 1 (parityRootMoment
        (gramDeterminantPolynomial (centeredKernel T q))) := by
      rw [gramDeterminantPolynomial_parityFactor T q hq hrow hcol]
      simp only [parityRootMoment, Polynomial.eval_neg]
    _ = Polynomial.eval 1 (gramDeterminantPolynomial (centeredKernel T q)) :=
      parityRootMoment_eval_one _
    _ = _ := gramDeterminantPolynomial_eval_one _

theorem signedGram_secondSizeMoment (T : Matrix Iota Iota R) (q : R)
    (hq : (Fintype.card Iota : R) * q = 1)
    (hrow : forall i, Finset.sum Finset.univ (fun j => T i j) = 1)
    (hcol : forall j, Finset.sum Finset.univ (fun i => T i j) = 1) :
    Polynomial.eval 1
      (-polynomialEuler (gramDeterminantPolynomial T)).derivative.derivative =
        4 * Polynomial.eval 1 (gramDeterminantPolynomial (centeredKernel T q)).derivative +
          3 * Polynomial.eval 1
            (gramDeterminantPolynomial (centeredKernel T q)).derivative.derivative := by
  rw [gramDeterminantPolynomial_parityFactor T q hq hrow hcol]
  exact parityRootMoment_secondDerivative_eval_one _

end PrimeFactorOscillations

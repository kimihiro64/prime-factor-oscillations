/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Polynomial
import PrimeFactorOscillations.Helpers.HamiltonianCoordinateMinorPolynomial
import PrimeFactorOscillations.Helpers.HamiltonianStochasticParity

/-! # The full signed aperiodic leading determinant

The constant projection is factored before differentiation. Every
principal support and its sign remain in the exact signal identity.
No symmetry, lower entry bound or permanent estimate is assumed.
-/

set_option autoImplicit false
set_option Elab.async false

noncomputable section

namespace PrimeFactorOscillations

variable {Iota : Type*} [Fintype Iota] [DecidableEq Iota]

theorem stochastic_determinant_constant_factor
    {R : Type*} [CommRing R] (T : Matrix Iota Iota R) (q : R)
    (hq : (Fintype.card Iota : R) * q = 1)
    (hRow : forall i, Finset.univ.sum (fun j => T i j) = 1)
    (hCol : forall j, Finset.univ.sum (fun i => T i j) = 1) (t : R) :
    Matrix.det ((1 : Matrix Iota Iota R) - HSMul.hSMul t T) =
      (1 - t) * Matrix.det
        ((1 : Matrix Iota Iota R) - HSMul.hSMul t (centeredKernel T q)) := by
  let B := centeredKernel T q
  have hOrth : averagingKernel q * B = 0 := by
    dsimp only [B, centeredKernel]
    rw [Matrix.mul_sub, averagingKernel_mul_of_columnSum T q hCol,
      averagingKernel_mul_self q hq, sub_self]
  have hSplit : T = averagingKernel q + B := by
    dsimp only [B, centeredKernel]
    abel
  have hFactor :
      ((1 : Matrix Iota Iota R) - HSMul.hSMul t (averagingKernel q)) *
        ((1 : Matrix Iota Iota R) - HSMul.hSMul t B) =
      (1 : Matrix Iota Iota R) - HSMul.hSMul t (averagingKernel q + B) := by
    rw [Matrix.sub_mul, Matrix.one_mul, Matrix.mul_sub, Matrix.mul_one]
    simp only [Matrix.smul_mul, Matrix.mul_smul, hOrth, smul_zero, sub_zero]
    rw [smul_add]
    abel
  calc
    _ = Matrix.det ((1 : Matrix Iota Iota R) -
        HSMul.hSMul t (averagingKernel q + B)) := by rw [hSplit]
    _ = (1 - t) * Matrix.det ((1 : Matrix Iota Iota R) - HSMul.hSMul t B) := by
      rw [<- hFactor, Matrix.det_mul, det_one_sub_averagingKernel q hq t]

theorem stochastic_aperiodic_euler_signal
    (T : Matrix Iota Iota Real) (q : Real)
    (hq : (Fintype.card Iota : Real) * q = 1)
    (hRow : forall i, Finset.univ.sum (fun j => T i j) = 1)
    (hCol : forall j, Finset.univ.sum (fun i => T i j) = 1) :
    -Polynomial.eval (-1) (polynomialEuler (principalMinorGeneratingPolynomial T)) =
      Matrix.det ((1 : Matrix Iota Iota Real) - centeredKernel T q) := by
  let p := principalMinorGeneratingPolynomial T
  let d := principalMinorGeneratingPolynomial (centeredKernel T q)
  have hValue (x : Real) : Polynomial.eval x p = (1 + x) * Polynomial.eval x d := by
    dsimp only [p, d]
    rw [principalMinorGeneratingPolynomial_eval, principalMinorGeneratingPolynomial_eval]
    simpa only [neg_smul, sub_neg_eq_add, neg_neg] using
      stochastic_determinant_constant_factor T q hq hRow hCol (-x)
  have hFunction : (fun x : Real => Polynomial.eval x p) =
      (fun x : Real => (1 + x) * Polynomial.eval x d) := funext hValue
  have hDeriv : HasDerivAt (fun x : Real => (1 + x) * Polynomial.eval x d)
      (Polynomial.eval (-1) d) (-1) := by
    simpa using! (((hasDerivAt_id (-1 : Real)).const_add 1).mul (d.hasDerivAt (-1)))
  have hDerivative : Polynomial.eval (-1) p.derivative = Polynomial.eval (-1) d := by
    calc
      _ = deriv (fun x : Real => Polynomial.eval x p) (-1) := (p.hasDerivAt (-1)).deriv.symm
      _ = _ := by rw [hFunction, hDeriv.deriv]
  change -Polynomial.eval (-1) (polynomialEuler p) = _
  rw [polynomialEuler, Polynomial.eval_mul, Polynomial.eval_X]
  simp only [neg_one_mul, neg_neg]
  rw [hDerivative]
  dsimp only [d]
  rw [principalMinorGeneratingPolynomial_eval]
  simp only [neg_one_smul, <- sub_eq_add_neg]

theorem stochastic_signed_principal_minor_signal
    (T : Matrix Iota Iota Real) (q : Real)
    (hq : (Fintype.card Iota : Real) * q = 1)
    (hRow : forall i, Finset.univ.sum (fun j => T i j) = 1)
    (hCol : forall j, Finset.univ.sum (fun i => T i j) = 1) :
    -Finset.univ.sum (fun S : Finset Iota =>
        (S.card : Real) * principalMinorDet T S * (-1 : Real) ^ S.card) =
      Matrix.det ((1 : Matrix Iota Iota Real) - centeredKernel T q) := by
  rw [<- principalMinor_euler_eval]
  exact stochastic_aperiodic_euler_signal T q hq hRow hCol

end PrimeFactorOscillations

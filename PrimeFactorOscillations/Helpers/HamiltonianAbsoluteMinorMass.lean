/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Polynomial
import PrimeFactorOscillations.Helpers.HamiltonianCoordinateMinorPolynomial
import PrimeFactorOscillations.Helpers.HamiltonianMatrixSpectralAverage
import PrimeFactorOscillations.Helpers.HamiltonianRectangularMinors
import PrimeFactorOscillations.Helpers.HamiltonianStochasticParity

/-! # Exact weighted absolute minor mass for the retained residual

The unsigned mass is used only after the signed first-order term
has been evaluated. Cauchy--Binet keeps both independent supports.
The actual positive Gram spectrum controls the Euler derivative,
and the constant-direction determinant factor remains exact.
-/

set_option autoImplicit false
set_option Elab.async false

noncomputable section

namespace PrimeFactorOscillations

variable {Iota : Type*} [Fintype Iota] [DecidableEq Iota]

def hamiltonianAbsoluteMinorMass (T : Matrix Iota Iota Real) : Real :=
  Finset.univ.sum (fun U : Finset Iota =>
    (U.card : Real) * (Finset.univ.powersetCard U.card).sum
      (fun S => rectangularMinorDet T S U ^ 2))

theorem hamiltonian_absolute_minor_mass_euler (T : Matrix Iota Iota Real) :
    hamiltonianAbsoluteMinorMass T =
      Polynomial.eval 1 (polynomialEuler
        (principalMinorGeneratingPolynomial (T.transpose * T))) := by
  rw [principalMinor_euler_eval]
  simp only [one_pow, mul_one]
  unfold hamiltonianAbsoluteMinorMass
  apply Finset.sum_congr rfl
  intro U hU
  rw [gramPrincipalMinor_eq_rectangularSquares]

theorem hamiltonian_principal_euler_spectral
    (G : Matrix Iota Iota Real) (hG : G.IsHermitian) :
    Polynomial.eval 1 (polynomialEuler (principalMinorGeneratingPolynomial G)) =
      Finset.univ.sum (fun i : Iota => hG.eigenvalues i *
        (Finset.univ.erase i).prod (fun j => 1 + hG.eigenvalues j)) := by
  let p := principalMinorGeneratingPolynomial G
  let lam := hG.eigenvalues
  have hValue (t : Real) :
      Polynomial.eval t p = Finset.univ.prod (fun i => 1 + t * lam i) := by
    rw [principalMinorGeneratingPolynomial_eval]
    simpa only [neg_smul, sub_neg_eq_add, neg_mul, neg_neg] using
      hermitian_det_one_sub_smul G hG (-t)
  have hFunction : (fun t : Real => Polynomial.eval t p) =
      (fun t : Real => Finset.univ.prod (fun i => 1 + t * lam i)) := funext hValue
  have hEach (i : Iota) :
      HasDerivAt (fun t : Real => 1 + t * lam i) (lam i) 1 := by
    simpa using! ((hasDerivAt_id (1 : Real)).mul_const (lam i)).const_add 1
  have hProd : HasDerivAt
      (fun t : Real => Finset.univ.prod (fun i => 1 + t * lam i))
      (Finset.univ.sum (fun i : Iota =>
        (Finset.univ.erase i).prod (fun j => 1 + lam j) * lam i)) 1 := by
    simpa only [one_mul, smul_eq_mul] using!
      (HasDerivAt.fun_finsetProd (u := Finset.univ) (fun i _ => hEach i))
  calc
    _ = Polynomial.eval 1 p.derivative := by
      simp only [polynomialEuler, Polynomial.eval_mul, Polynomial.eval_X, one_mul, p]
    _ = deriv (fun t : Real => Polynomial.eval t p) 1 := (p.hasDerivAt 1).deriv.symm
    _ = Finset.univ.sum (fun i : Iota =>
        (Finset.univ.erase i).prod (fun j => 1 + lam j) * lam i) := by
      rw [hFunction, hProd.deriv]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro i hi
      ring

theorem hamiltonian_hermitian_euler_positive_bound
    (G : Matrix Iota Iota Real) (hG : G.IsHermitian)
    (hEigen : forall i, 0 <= hG.eigenvalues i) :
    0 < Matrix.det ((1 : Matrix Iota Iota Real) + G) /\
      Polynomial.eval 1 (polynomialEuler (principalMinorGeneratingPolynomial G)) <=
        Matrix.trace G * Matrix.det ((1 : Matrix Iota Iota Real) + G) := by
  let lam := hG.eigenvalues
  let D := Finset.univ.prod (fun i : Iota => 1 + lam i)
  have hDet : Matrix.det ((1 : Matrix Iota Iota Real) + G) = D := by
    simpa only [neg_smul, one_smul, sub_neg_eq_add, neg_one_mul] using
      hermitian_det_one_sub_smul G hG (-1)
  have hD : 0 < D := Finset.prod_pos (fun i _ => by linarith only [hEigen i])
  have hTerm (i : Iota) :
      lam i * (Finset.univ.erase i).prod (fun j => 1 + lam j) <= lam i * D := by
    have hNonneg : 0 <= (Finset.univ.erase i).prod (fun j => 1 + lam j) :=
      Finset.prod_nonneg (fun j _ => by linarith only [hEigen j])
    have hWhole : (1 + lam i) *
        (Finset.univ.erase i).prod (fun j => 1 + lam j) = D := by
      exact Finset.mul_prod_erase Finset.univ (fun j => 1 + lam j) (Finset.mem_univ i)
    rw [<- hWhole]
    nlinarith only [mul_nonneg (sq_nonneg (lam i)) hNonneg]
  refine And.intro (by rw [hDet]; exact hD) ?_
  rw [hamiltonian_principal_euler_spectral G hG, hDet, hG.trace_eq_sum_eigenvalues]
  calc
    _ <= Finset.univ.sum (fun i : Iota => lam i * D) :=
      Finset.sum_le_sum (fun i _ => hTerm i)
    _ = _ := (Finset.sum_mul Finset.univ lam D).symm

theorem stochastic_absolute_minor_mass_bound
    (T : Matrix Iota Iota Real) (q a : Real)
    (hq : (Fintype.card Iota : Real) * q = 1)
    (hRow : forall i, Finset.univ.sum (fun j => T i j) = 1)
    (hCol : forall j, Finset.univ.sum (fun i => T i j) = 1)
    (hNonneg : forall i j, 0 <= T i j) (hUpper : forall i j, T i j <= a * q) :
    hamiltonianAbsoluteMinorMass T <=
      2 * a * Matrix.det ((1 : Matrix Iota Iota Real) +
        (centeredKernel T q).transpose * centeredKernel T q) := by
  have hEnergy : Finset.univ.sum (fun i => Finset.univ.sum (fun j => T i j ^ 2)) <= a := by
    calc
      _ <= Finset.univ.sum (fun i => Finset.univ.sum (fun j => (a * q) * T i j)) := by
        apply Finset.sum_le_sum
        intro i hi
        apply Finset.sum_le_sum
        intro j hj
        have h := mul_le_mul_of_nonneg_right (hUpper i j) (hNonneg i j)
        nlinarith only [h]
      _ = Finset.univ.sum (fun _ : Iota => a * q) := by
        simp only [<- Finset.mul_sum, hRow, mul_one]
      _ = a * ((Fintype.card Iota : Real) * q) := by
        simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
        ring
      _ = a := by rw [hq, mul_one]
  have hTrace : Matrix.trace (T.transpose * T) <= a := by
    rw [(realGramHermitian T).trace_eq_sum_eigenvalues]
    change Finset.univ.sum (realGramEigenvalues T) <= a
    rw [realGramEigenvalues_sum_eq_energy]
    exact hEnergy
  have hData := hamiltonian_hermitian_euler_positive_bound (T.transpose * T)
    (realGramHermitian T) (realGramEigenvalues_nonnegative T)
  have hParity := stochasticGram_parityFactor T q hq hRow hCol (-1)
  norm_num only [neg_smul, one_smul, sub_neg_eq_add] at hParity
  calc
    _ = Polynomial.eval 1 (polynomialEuler
        (principalMinorGeneratingPolynomial (T.transpose * T))) :=
      hamiltonian_absolute_minor_mass_euler T
    _ <= Matrix.trace (T.transpose * T) *
        Matrix.det ((1 : Matrix Iota Iota Real) + T.transpose * T) := hData.2
    _ <= a * Matrix.det ((1 : Matrix Iota Iota Real) + T.transpose * T) :=
      mul_le_mul_of_nonneg_right hTrace (le_of_lt hData.1)
    _ = _ := by rw [hParity]; ring

end PrimeFactorOscillations

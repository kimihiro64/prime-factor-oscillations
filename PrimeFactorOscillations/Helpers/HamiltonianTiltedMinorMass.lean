/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import Mathlib.Tactic.GCongr
import PrimeFactorOscillations.Helpers.HamiltonianAbsoluteMinorMass

/-! # Tilted weighted squared-minor mass for the complete retained tails

The evaluation point is an arbitrary real tilt throughout the Euler
and actual spectral derivative identities. The stochastic constant
direction contributes its exact factor 1+t. The centered energy
provider is consumed before the exponential determinant estimate.
-/

set_option autoImplicit false
set_option Elab.async false

noncomputable section

namespace PrimeFactorOscillations

variable {Iota : Type*} [Fintype Iota] [DecidableEq Iota]

def hamiltonianTiltedMinorMass (T : Matrix Iota Iota Real) (t : Real) : Real :=
  Finset.univ.sum (fun U : Finset Iota => (U.card : Real) * t ^ U.card *
    (Finset.univ.powersetCard U.card).sum (fun S => rectangularMinorDet T S U ^ 2))

theorem hamiltonian_tilted_minor_mass_euler (T : Matrix Iota Iota Real) (t : Real) :
    hamiltonianTiltedMinorMass T t =
      Polynomial.eval t (polynomialEuler
        (principalMinorGeneratingPolynomial (T.transpose * T))) := by
  rw [principalMinor_euler_eval]
  unfold hamiltonianTiltedMinorMass
  apply Finset.sum_congr rfl
  intro U hU
  rw [gramPrincipalMinor_eq_rectangularSquares]
  ring

theorem hamiltonian_principal_euler_spectral_at
    (G : Matrix Iota Iota Real) (hG : G.IsHermitian) (t : Real) :
    Polynomial.eval t (polynomialEuler (principalMinorGeneratingPolynomial G)) =
      Finset.univ.sum (fun i : Iota => t * hG.eigenvalues i *
        (Finset.univ.erase i).prod (fun j => 1 + t * hG.eigenvalues j)) := by
  let p := principalMinorGeneratingPolynomial G
  let lam := hG.eigenvalues
  have hValue (x : Real) :
      Polynomial.eval x p = Finset.univ.prod (fun i => 1 + x * lam i) := by
    rw [principalMinorGeneratingPolynomial_eval]
    simpa only [neg_smul, sub_neg_eq_add, neg_mul, neg_neg] using
      hermitian_det_one_sub_smul G hG (-x)
  have hFunction : (fun x : Real => Polynomial.eval x p) =
      (fun x : Real => Finset.univ.prod (fun i => 1 + x * lam i)) := funext hValue
  have hEach (i : Iota) :
      HasDerivAt (fun x : Real => 1 + x * lam i) (lam i) t := by
    simpa using! ((hasDerivAt_id t).mul_const (lam i)).const_add 1
  have hProd : HasDerivAt
      (fun x : Real => Finset.univ.prod (fun i => 1 + x * lam i))
      (Finset.univ.sum (fun i : Iota =>
        (Finset.univ.erase i).prod (fun j => 1 + t * lam j) * lam i)) t := by
    simpa only [smul_eq_mul] using!
      (HasDerivAt.fun_finsetProd (u := Finset.univ) (fun i _ => hEach i))
  calc
    _ = t * Polynomial.eval t p.derivative := by
      simp only [polynomialEuler, Polynomial.eval_mul, Polynomial.eval_X, p]
    _ = t * deriv (fun x : Real => Polynomial.eval x p) t := by rw [(p.hasDerivAt t).deriv]
    _ = t * Finset.univ.sum (fun i : Iota =>
        (Finset.univ.erase i).prod (fun j => 1 + t * lam j) * lam i) := by
      rw [hFunction, hProd.deriv]
    _ = _ := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i hi
      ring

theorem hamiltonian_hermitian_euler_positive_bound_at
    (G : Matrix Iota Iota Real) (hG : G.IsHermitian)
    (hEigen : forall i, 0 <= hG.eigenvalues i) (t : Real) (ht : 0 <= t) :
    0 < Matrix.det ((1 : Matrix Iota Iota Real) + HSMul.hSMul t G) /\
      Polynomial.eval t (polynomialEuler (principalMinorGeneratingPolynomial G)) <=
        t * Matrix.trace G * Matrix.det ((1 : Matrix Iota Iota Real) + HSMul.hSMul t G) := by
  let lam := hG.eigenvalues
  let D := Finset.univ.prod (fun i : Iota => 1 + t * lam i)
  have hDet : Matrix.det ((1 : Matrix Iota Iota Real) + HSMul.hSMul t G) = D := by
    simpa only [neg_smul, sub_neg_eq_add, neg_mul, neg_neg] using
      hermitian_det_one_sub_smul G hG (-t)
  have hCoeff (i : Iota) : 0 <= t * lam i := mul_nonneg ht (hEigen i)
  have hD : 0 < D := Finset.prod_pos (fun i _ => by linarith only [hCoeff i])
  have hTerm (i : Iota) :
      t * lam i * (Finset.univ.erase i).prod (fun j => 1 + t * lam j) <= t * lam i * D := by
    have hNonneg : 0 <= (Finset.univ.erase i).prod (fun j => 1 + t * lam j) :=
      Finset.prod_nonneg (fun j _ => by linarith only [hCoeff j])
    have hWhole : (1 + t * lam i) *
        (Finset.univ.erase i).prod (fun j => 1 + t * lam j) = D :=
      Finset.mul_prod_erase Finset.univ (fun j => 1 + t * lam j) (Finset.mem_univ i)
    rw [<- hWhole]
    nlinarith only [mul_nonneg (sq_nonneg (t * lam i)) hNonneg]
  refine And.intro (by rw [hDet]; exact hD) ?_
  have hTraceCanonical : Matrix.trace G = Finset.univ.sum lam := by
    simpa using! hG.trace_eq_sum_eigenvalues
  rw [hamiltonian_principal_euler_spectral_at G hG t, hDet]
  calc
    _ <= Finset.univ.sum (fun i : Iota => t * lam i * D) :=
      Finset.sum_le_sum (fun i _ => hTerm i)
    _ = t * Matrix.trace G * D := by
      rw [hTraceCanonical, Finset.mul_sum, Finset.sum_mul]

theorem hamiltonian_hermitian_positive_det_exp_bound
    (G : Matrix Iota Iota Real) (hG : G.IsHermitian)
    (hEigen : forall i, 0 <= hG.eigenvalues i) (t : Real) (ht : 0 <= t) :
    Matrix.det ((1 : Matrix Iota Iota Real) + HSMul.hSMul t G) <=
      Real.exp (t * Matrix.trace G) := by
  have hDet : Matrix.det ((1 : Matrix Iota Iota Real) + HSMul.hSMul t G) =
      Finset.univ.prod (fun i => 1 + t * hG.eigenvalues i) := by
    simpa only [neg_smul, sub_neg_eq_add, neg_mul, neg_neg] using
      hermitian_det_one_sub_smul G hG (-t)
  rw [hDet]
  calc
    _ <= Finset.univ.prod (fun i => Real.exp (t * hG.eigenvalues i)) := by
      have hNonneg (i : Iota) : 0 <= 1 + t * hG.eigenvalues i :=
        add_nonneg (by norm_num) (mul_nonneg ht (hEigen i))
      have hPoint (i : Iota) : 1 + t * hG.eigenvalues i <= Real.exp (t * hG.eigenvalues i) := by
        simpa only [add_comm] using Real.add_one_le_exp (t * hG.eigenvalues i)
      gcongr with i hi
      all_goals first
        | exact fun i _ => hNonneg i
        | exact fun i _ => hPoint i
        | exact hNonneg _
        | exact hPoint _
    _ = _ := by
      have hTraceCanonical : Matrix.trace G = Finset.univ.sum (fun i => hG.eigenvalues i) := by
        simpa using! hG.trace_eq_sum_eigenvalues
      rw [<- Real.exp_sum, <- Finset.mul_sum, hTraceCanonical]

theorem stochastic_tilted_minor_mass_bound
    (T : Matrix Iota Iota Real) (q a t : Real)
    (hq : (Fintype.card Iota : Real) * q = 1) (ha : 1 <= a) (ht : 0 <= t)
    (hRow : forall i, Finset.univ.sum (fun j => T i j) = 1)
    (hCol : forall j, Finset.univ.sum (fun i => T i j) = 1)
    (hNonneg : forall i j, 0 <= T i j) (hUpper : forall i j, T i j <= a * q) :
    hamiltonianTiltedMinorMass T t <=
      t * a * (1 + t) * Real.exp (t * (a - 1)) := by
  let B := centeredKernel T q
  have hCentered : Matrix.trace (B.transpose * B) <= a - 1 := by
    rw [(realGramHermitian B).trace_eq_sum_eigenvalues]
    change Finset.univ.sum (realGramEigenvalues B) <= a - 1
    rw [realGramEigenvalues_sum_eq_energy]
    exact stochastic_total_energy T q a hq hRow hNonneg hUpper
  have hProjection : Matrix.trace (averagingKernel (Iota := Iota) q) = 1 := by
    change Finset.univ.sum (fun _ : Iota => q) = 1
    simpa only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul] using hq
  have hTraceIdentity : Matrix.trace (B.transpose * B) = Matrix.trace (T.transpose * T) - 1 := by
    rw [centeredKernel_gram_eq_sub T q hq hCol, Matrix.trace_sub, hProjection]
  have hTrace : Matrix.trace (T.transpose * T) <= a := by
    linarith only [hCentered, hTraceIdentity]
  have hPositive := hamiltonian_hermitian_euler_positive_bound_at (T.transpose * T)
    (realGramHermitian T) (realGramEigenvalues_nonnegative T) t ht
  have hParity := stochasticGram_parityFactor T q hq hRow hCol (-t)
  simp only [neg_smul, sub_neg_eq_add, sub_neg_eq_add, neg_neg] at hParity
  have hDetB : Matrix.det ((1 : Matrix Iota Iota Real) + HSMul.hSMul t (B.transpose * B)) <=
      Real.exp (t * (a - 1)) := by
    exact le_trans (hamiltonian_hermitian_positive_det_exp_bound (B.transpose * B)
      (realGramHermitian B) (realGramEigenvalues_nonnegative B) t ht)
      (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hCentered ht))
  have hA : 0 <= a := le_trans (by norm_num) ha
  have hTA : 0 <= t * a := mul_nonneg ht hA
  have hOne : 0 <= 1 + t := add_nonneg (by norm_num) ht
  calc
    _ = Polynomial.eval t (polynomialEuler
        (principalMinorGeneratingPolynomial (T.transpose * T))) :=
      hamiltonian_tilted_minor_mass_euler T t
    _ <= t * Matrix.trace (T.transpose * T) *
        Matrix.det ((1 : Matrix Iota Iota Real) + HSMul.hSMul t (T.transpose * T)) := hPositive.2
    _ <= t * a *
        Matrix.det ((1 : Matrix Iota Iota Real) + HSMul.hSMul t (T.transpose * T)) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hTrace ht) (le_of_lt hPositive.1)
    _ = t * a * ((1 + t) *
        Matrix.det ((1 : Matrix Iota Iota Real) + HSMul.hSMul t (B.transpose * B))) := by rw [hParity]
    _ <= t * a * ((1 + t) * Real.exp (t * (a - 1))) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hDetB hOne) hTA
    _ = _ := by ring

end PrimeFactorOscillations

/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.HamiltonianGaussianPartialMatchings

/-! # Exact Gaussian rook identification and its stochastic complex bound

The maintained rook polynomial, including every factorial completion
weight, equals the actual affine Gaussian polynomial state. The positive
Gaussian product envelope is consumed only after this signed identity.
-/

set_option autoImplicit false
set_option Elab.async false

open scoped Matrix.Norms.L2Operator

noncomputable section

namespace PrimeFactorOscillations

variable {Iota : Type*} [Fintype Iota] [DecidableEq Iota]

def hamiltonianComplexRookPolynomial (B : Matrix Iota Iota Real) (t : Complex) :
    Complex :=
  Finset.sum Finset.univ (fun sigma : Equiv.Perm Iota =>
    Finset.sum (Finset.univ : Finset Iota).powerset (fun S =>
      (Finset.prod S (fun i => (B (sigma i) i : Complex)) /
        (((Fintype.card Iota - S.card).factorial : Nat) : Complex)) * t ^ S.card))

theorem hamiltonianComplexRookPolynomial_ofReal
    (B : Matrix Iota Iota Real) (s : Real) :
    hamiltonianComplexRookPolynomial B (s : Complex) =
      (hamiltonianRookPolynomial B s : Complex) := by
  unfold hamiltonianComplexRookPolynomial hamiltonianRookPolynomial
  push_cast
  rfl

theorem gaussianLinearForm_scale (c : Complex) (a : Iota -> Complex) :
    gaussianLinearForm (fun i => c * a i) =
      MvPolynomial.C c * gaussianLinearForm a := by
  unfold gaussianLinearForm
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  rw [map_mul]
  ring

theorem gaussianLinearCovariance_scale (z a b : Iota -> Complex) (c : Complex) :
    gaussianLinearCovariance z (fun i => c * a i) (fun i => c * b i) =
      c ^ 2 * gaussianLinearCovariance z a b := by
  unfold gaussianLinearCovariance
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  ring

theorem realGaussianAffinePolynomial_rook {n : Nat}
    (B : Matrix (Fin n) (Fin n) Real) (c : Complex) :
    gaussianPolynomialState
        (realGaussianEigenVariances (bipartiteLift B) (bipartiteLift_hermitian B))
        (realGaussianAffinePolynomial (bipartiteLift B)
          (bipartiteLift_hermitian B) c) =
      hamiltonianComplexRookPolynomial B (c ^ 2) := by
  let M := bipartiteLift B
  let hM := bipartiteLift_hermitian B
  let z := realGaussianEigenVariances M hM
  let left := fun i : Fin n => fun k =>
    c * realGaussianEigenRows M hM (Sum.inr i) k
  let right := fun j : Fin n => fun k =>
    c * realGaussianEigenRows M hM (Sum.inl j) k
  have hCov : forall i j : Sum (Fin n) (Fin n),
      gaussianLinearCovariance z
          (fun k => c * realGaussianEigenRows M hM i k)
          (fun k => c * realGaussianEigenRows M hM j k) =
        c ^ 2 * (M i j : Complex) := by
    intro i j
    rw [gaussianLinearCovariance_scale, realGaussianEigenCovariance]
  have hLeft : forall i j, gaussianLinearCovariance z (left i) (left j) = 0 := by
    intro i j
    rw [hCov]
    change c ^ 2 * (0 : Complex) = 0
    ring
  have hRight : forall i j, gaussianLinearCovariance z (right i) (right j) = 0 := by
    intro i j
    rw [hCov]
    change c ^ 2 * (0 : Complex) = 0
    ring
  have hCross : forall i j,
      gaussianLinearCovariance z (left i) (right j) = c ^ 2 * (B j i : Complex) := by
    intro i j
    rw [hCov]
    rfl
  have hPoly : realGaussianAffinePolynomial M hM c =
      Finset.prod Finset.univ (fun i => 1 + gaussianLinearForm (left i)) *
        Finset.prod Finset.univ (fun j => 1 + gaussianLinearForm (right j)) := by
    unfold realGaussianAffinePolynomial
    rw [Fintype.prod_sum_type]
    dsimp only [left, right]
    simp_rw [gaussianLinearForm_scale]
    exact mul_comm _ _
  change gaussianPolynomialState z (realGaussianAffinePolynomial M hM c) = _
  rw [hPoly, gaussianAffineProduct_rook z n left right hLeft hRight]
  unfold hamiltonianComplexRookPolynomial
  simp only [Fintype.card_fin]
  apply Finset.sum_congr rfl
  intro sigma hs
  apply Finset.sum_congr rfl
  intro S hS
  simp_rw [hCross, Finset.prod_mul_distrib, Finset.prod_const]
  ring

theorem hamiltonianComplexRookPolynomial_stochastic_bound {n : Nat}
    (T : Matrix (Fin n) (Fin n) Real) (q a rho : Real) (t : Complex)
    (hq : (n : Real) * q = 1) (ha : 1 <= a)
    (hRow : forall i, Finset.sum Finset.univ (fun j => T i j) = 1)
    (hCol : forall j, Finset.sum Finset.univ (fun i => T i j) = 1)
    (hNonneg : forall i j, 0 <= T i j) (hUpper : forall i j, T i j <= a * q)
    (hNorm : norm (centeredKernel T q) <= rho) (hGap : 0 < 1 - norm t * rho) :
    norm (hamiltonianComplexRookPolynomial (centeredKernel T q) t) <=
      Real.exp (2 * norm t / (1 - norm t * rho) *
        Real.sqrt ((n : Real) * (a - 1))) := by
  have hId := realGaussianAffinePolynomial_rook (centeredKernel T q)
    (complexGaussianSquareRoot t)
  rw [complexGaussianSquareRoot_sq] at hId
  rw [<- hId]
  simpa only [Fintype.card_fin] using
    stochasticGaussianAffinePolynomial_bound T q a rho t
      (by simpa only [Fintype.card_fin] using hq) ha
      hRow hCol hNonneg hUpper hNorm hGap

end PrimeFactorOscillations

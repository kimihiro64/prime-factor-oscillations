/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.HamiltonianGaussianQuotientCovariance

/-! # Exact signed readout of every quotient Gaussian Wick moment

Actual normalized integrals, repeated vertices, and the complete degree-six
diagonal compensation are matched to the maintained finite Wick recursion.
-/

set_option autoImplicit false
set_option Elab.async false

noncomputable section

namespace PrimeFactorOscillations

variable {Iota J A B : Type*} [Fintype Iota] [DecidableEq Iota]

theorem listMap_eraseIdx_eq (f : A -> B) (xs : List A) (k : Nat) :
    (xs.eraseIdx k).map f = (xs.map f).eraseIdx k := by
  induction xs generalizing k with
  | nil => cases k <;> rfl
  | cons a xs ih =>
    cases k with
    | zero => rfl
    | succ k =>
      change f a :: (xs.eraseIdx k).map f = f a :: (xs.map f).eraseIdx k
      rw [ih]

theorem listMap_getD_lt (f : A -> B) (xs : List A) (k : Nat)
    (a : A) (b : B) (hk : k < xs.length) :
    (xs.map f).getD k b = f (xs.getD k a) := by
  induction xs generalizing k with
  | nil => simp only [List.length_nil, Nat.not_lt_zero] at hk
  | cons x xs ih =>
    cases k with
    | zero => rfl
    | succ k =>
      change (xs.map f).getD k b = f (xs.getD k a)
      exact ih k (by simp only [List.length_cons] at hk; omega)

theorem gaussianLinearWickValue_real_covariance
    (z : Iota -> Complex) (row : J -> Iota -> Complex) (M : Matrix J J Real)
    (hCov : forall i j, gaussianLinearCovariance z (row i) (row j) = (M i j : Complex))
    (e : Nat) (xs : List J) (hLen : xs.length = 2 * e) :
    gaussianLinearWickValue z (xs.map row) = (wickPairMoment M e xs : Complex) := by
  induction e generalizing xs with
  | zero =>
    cases xs with
    | nil => simp only [List.map_nil, gaussianLinearWickValue_nil, wickPairMoment,
        Complex.ofReal_one]
    | cons i xs => simp only [List.length_cons] at hLen; omega
  | succ e ih =>
    cases xs with
    | nil => simp only [List.length_nil] at hLen; omega
    | cons i xs =>
      rw [List.map_cons, gaussianLinearWickValue_cons, wickPairMoment, List.length_map]
      push_cast
      apply Finset.sum_congr rfl
      intro k hk
      have hkLt := Finset.mem_range.mp hk
      have hErase := List.length_eraseIdx_add_one hkLt
      have hEraseLen : (xs.eraseIdx k).length = 2 * e := by
        simp only [List.length_cons] at hLen
        omega
      rw [listMap_getD_lt row xs k i (fun _ => 0) hkLt,
        <- listMap_eraseIdx_eq row xs k, hCov,
        ih (xs.eraseIdx k) hEraseLen]

theorem realGaussianQuotientWick_integral (M : Matrix Iota Iota Real)
    (hM : M.IsHermitian) (s : Real)
    (hAdd : forall j, Not (1 + s * hM.eigenvalues j = 0))
    (e : Nat) (xs : List Iota) (hLen : xs.length = 2 * e) :
    MeasureTheory.integral gaussianTensorMeasure
        (standardGaussianPolynomialKernel
          (fun j => (s : Complex) * realGaussianEigenVariances M hM j /
            (1 + (s : Complex) * realGaussianEigenVariances M hM j))
          (gaussianLinearProduct (xs.map (realGaussianEigenRows M hM)))) /
        gaussianTensorTiltNormalizer (fun _ : Iota => 0) =
      (wickPairMoment (resolventCovariance (HSMul.hSMul s M)) e xs : Complex) := by
  rw [standardGaussianPolynomial_normalized]
  exact gaussianLinearWickValue_real_covariance _ _ _
    (realGaussianQuotientCovariance_entry_resolvent M hM s hAdd) e xs hLen

theorem realGaussianQuotientWick_integral_bound (M : Matrix Iota Iota Real)
    (hM : M.IsHermitian) (s : Real)
    (hAdd : forall j, Not (1 + s * hM.eigenvalues j = 0))
    (c : Real) (hc : 0 <= c)
    (hEntry : forall i j, abs (resolventCovariance (HSMul.hSMul s M) i j) <= c)
    (e : Nat) (xs : List Iota) (hLen : xs.length = 2 * e) :
    norm (MeasureTheory.integral gaussianTensorMeasure
        (standardGaussianPolynomialKernel
          (fun j => (s : Complex) * realGaussianEigenVariances M hM j /
            (1 + (s : Complex) * realGaussianEigenVariances M hM j))
          (gaussianLinearProduct (xs.map (realGaussianEigenRows M hM)))) /
        gaussianTensorTiltNormalizer (fun _ : Iota => 0)) <=
      (wickPairCount e : Real) * c ^ e := by
  rw [realGaussianQuotientWick_integral M hM s hAdd e xs hLen,
    Complex.norm_real, Real.norm_eq_abs]
  exact wickPairMoment_bound _ c hc hEntry e xs hLen

def gaussianLinearDegreeSixValue [Fintype J] [DecidableEq J]
    (z : Iota -> Complex) (row : J -> Iota -> Complex) : Complex :=
  -(1 / 4 : Complex) * Finset.sum Finset.univ (fun i =>
      gaussianLinearWickValue z ([i, i, i, i].map row)) +
    (1 / 18 : Complex) * Finset.sum Finset.univ (fun i =>
      Finset.sum Finset.univ (fun j => if i = j then 0 else
        gaussianLinearWickValue z ([i, i, i, j, j, j].map row))) -
    (1 / 9 : Complex) * Finset.sum Finset.univ (fun i =>
      gaussianLinearWickValue z ([i, i, i, i, i, i].map row))

theorem gaussianLinearDegreeSixValue_eq [Fintype J] [DecidableEq J]
    (z : Iota -> Complex) (row : J -> Iota -> Complex) (M : Matrix J J Real)
    (hCov : forall i j, gaussianLinearCovariance z (row i) (row j) = (M i j : Complex)) :
    gaussianLinearDegreeSixValue z row = (wickDegreeSixCorrection M : Complex) := by
  have hFour : forall i, gaussianLinearWickValue z ([i, i, i, i].map row) =
      (wickPairMoment M 2 [i, i, i, i] : Complex) := by
    intro i
    exact gaussianLinearWickValue_real_covariance z row M hCov 2 _ (by rfl)
  have hTriple : forall i j, gaussianLinearWickValue z ([i, i, i, j, j, j].map row) =
      (wickPairMoment M 3 [i, i, i, j, j, j] : Complex) := by
    intro i j
    exact gaussianLinearWickValue_real_covariance z row M hCov 3 _ (by rfl)
  have hSix : forall i, gaussianLinearWickValue z ([i, i, i, i, i, i].map row) =
      (wickPairMoment M 3 [i, i, i, i, i, i] : Complex) := by
    intro i
    exact gaussianLinearWickValue_real_covariance z row M hCov 3 _ (by rfl)
  unfold gaussianLinearDegreeSixValue wickDegreeSixCorrection
  simp only [hFour, hTriple, hSix]
  push_cast
  simp only [apply_ite, Complex.ofReal_zero]

theorem realGaussianQuotientDegreeSixValue (M : Matrix Iota Iota Real)
    (hM : M.IsHermitian) (s : Real)
    (hAdd : forall j, Not (1 + s * hM.eigenvalues j = 0)) :
    gaussianLinearDegreeSixValue
        (fun j => (s : Complex) * realGaussianEigenVariances M hM j /
          (1 + (s : Complex) * realGaussianEigenVariances M hM j))
        (realGaussianEigenRows M hM) =
      ((covarianceCorrection (resolventCovariance (HSMul.hSMul s M)) -
        (5 / 2 : Real) * Finset.sum Finset.univ (fun i =>
          resolventCovariance (HSMul.hSMul s M) i i ^ 3) : Real) : Complex) := by
  rw [gaussianLinearDegreeSixValue_eq _ _ _
    (realGaussianQuotientCovariance_entry_resolvent M hM s hAdd),
    wickDegreeSixCorrection_eq]

end PrimeFactorOscillations

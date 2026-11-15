/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.HamiltonianCompensatedGaussianIntegral

/-! # Actual Gaussian tilt normalizers without a square-root branch choice

The scalar integral square and finite tensor normalizer square are exact.
On the real interval their signs follow from the actual positive integral.
-/

set_option autoImplicit false
set_option Elab.async false

noncomputable section

namespace PrimeFactorOscillations

variable {Iota : Type*} [Fintype Iota] [DecidableEq Iota]

theorem gaussian_disk_one_add_ne_zero (z : Complex) (hz : norm z < 1) :
    Not (1 + z = 0) := by
  intro h
  have hZ : z = -1 := by
    calc
      z = (1 + z) - 1 := by ring
      _ = -1 := by rw [h]; ring
  rw [hZ, norm_neg, norm_one] at hz
  exact (lt_irrefl 1) hz

theorem complexGaussianMoment_zero_sq (b : Complex) (hb : 0 < b.re) :
    complexGaussianMoment b 0 ^ 2 = (Real.pi : Complex) / b := by
  have hKernel : complexGaussianKernel b 0 =
      (fun x : Real => Complex.exp (-b * (x : Complex) ^ 2)) := by
    funext x
    simp only [complexGaussianKernel, pow_zero, one_mul]
  rw [complexGaussianMoment, hKernel]
  exact integral_gaussian_sq_complex hb

theorem gaussianTiltMoment_sq (z : Complex) (hz : norm z < 1) :
    complexGaussianMoment (gaussianTiltPrecision z) 0 ^ 2 =
      (realStandardGaussianNormalizer : Complex) ^ 2 * (1 + z) := by
  have hAdd := gaussian_disk_one_add_ne_zero z hz
  have hPrec : Not (gaussianTiltPrecision z = 0) := by
    intro h
    have hPos := gaussianTiltPrecision_real_part z hz
    rw [h, Complex.zero_re] at hPos
    norm_num at hPos
  rw [complexGaussianMoment_zero_sq _
    (lt_trans (by norm_num) (gaussianTiltPrecision_real_part z hz))]
  have hStd : (realStandardGaussianNormalizer : Complex) ^ 2 =
      2 * (Real.pi : Complex) := by
    exact_mod_cast realStandardGaussianNormalizer_sq
  rw [hStd]
  apply (div_eq_iff hPrec).mpr
  unfold gaussianTiltPrecision
  field_simp
  ring

theorem finiteGaussianNormalizer_square {K : Type*} [Field K]
    (a b : Iota -> K) (c : K) (hc : Not (c = 0))
    (hSq : forall i, a i ^ 2 = c ^ 2 * b i) :
    (Finset.prod Finset.univ a / c ^ Fintype.card Iota) ^ 2 =
      Finset.prod Finset.univ b := by
  rw [div_pow, <- Finset.prod_pow]
  simp_rw [hSq]
  rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ]
  have hPow : (c ^ 2) ^ Fintype.card Iota = (c ^ Fintype.card Iota) ^ 2 := by
    rw [<- pow_mul, <- pow_mul, Nat.mul_comm 2 (Fintype.card Iota)]
  rw [hPow]
  field_simp

theorem gaussianTensorTiltNormalizer_ratio_sq (z : Iota -> Complex)
    (hz : forall i, norm (z i) < 1) :
    (gaussianTensorTiltNormalizer z /
        ((realStandardGaussianNormalizer ^ Fintype.card Iota : Real) : Complex)) ^ 2 =
      Finset.prod Finset.univ (fun i => 1 + z i) := by
  have hStd : Not ((realStandardGaussianNormalizer : Complex) = 0) := by
    exact_mod_cast (ne_of_gt realStandardGaussianNormalizer_positive)
  unfold gaussianTensorTiltNormalizer
  push_cast
  exact finiteGaussianNormalizer_square _ _ _ hStd
    (fun i => gaussianTiltMoment_sq (z i) (hz i))

theorem gaussianTiltMoment_ofReal (u : Real) :
    complexGaussianMoment (gaussianTiltPrecision (u : Complex)) 0 =
      (realQuadraticGaussianIntegral (u / (1 + u)) : Complex) := by
  have hKernel : complexGaussianKernel (gaussianTiltPrecision (u : Complex)) 0 =
      fun x : Real =>
        (Real.exp (-((1 - u / (1 + u)) / 2) * x ^ 2) : Complex) := by
    funext x
    simp only [complexGaussianKernel, pow_zero, one_mul]
    rw [Complex.ofReal_exp]
    congr 1
    unfold gaussianTiltPrecision
    push_cast
    ring
  rw [complexGaussianMoment, hKernel, _root_.integral_complex_ofReal]
  rfl

theorem realGaussianTilt_gap (u : Real) (hu : abs u < 1) :
    0 < 1 - u / (1 + u) := by
  have hPlus : 0 < 1 + u := by
    have hLower := (abs_lt.mp hu).1
    linarith
  have hId : 1 - u / (1 + u) = 1 / (1 + u) := by
    field_simp
    ring
  rw [hId]
  exact div_pos (by norm_num) hPlus

theorem realGaussianTiltMoment_positive (u : Real) (hu : abs u < 1) :
    0 < realQuadraticGaussianIntegral (u / (1 + u)) := by
  rw [realQuadraticGaussianIntegral, integral_gaussian]
  exact Real.sqrt_pos.mpr
    (div_pos Real.pi_pos (div_pos (realGaussianTilt_gap u hu) (by norm_num)))

theorem realGaussianTiltMoment_sq (u : Real) (hu : abs u < 1) :
    realQuadraticGaussianIntegral (u / (1 + u)) ^ 2 =
      realStandardGaussianNormalizer ^ 2 * (1 + u) := by
  rw [realQuadraticGaussianIntegral_sq _ (realGaussianTilt_gap u hu),
    realStandardGaussianNormalizer_sq]
  have hPlus : Not (1 + u = 0) := by
    have hLower := (abs_lt.mp hu).1
    linarith
  apply (div_eq_iff (ne_of_gt (realGaussianTilt_gap u hu))).mpr
  field_simp
  ring

def realGaussianTiltTensorNormalizer (u : Iota -> Real) : Real :=
  Finset.prod Finset.univ (fun i => realQuadraticGaussianIntegral (u i / (1 + u i)))

theorem realGaussianTiltTensorNormalizer_positive (u : Iota -> Real)
    (hu : forall i, abs (u i) < 1) :
    0 < realGaussianTiltTensorNormalizer u :=
  Finset.prod_pos (fun i _ => realGaussianTiltMoment_positive (u i) (hu i))

theorem realGaussianTiltTensorNormalizer_cast (u : Iota -> Real) :
    gaussianTensorTiltNormalizer (fun i => (u i : Complex)) =
      (realGaussianTiltTensorNormalizer u : Complex) := by
  unfold gaussianTensorTiltNormalizer realGaussianTiltTensorNormalizer
  simp_rw [gaussianTiltMoment_ofReal]
  push_cast
  rfl

theorem realGaussianTiltTensorNormalizer_ratio_sq (u : Iota -> Real)
    (hu : forall i, abs (u i) < 1) :
    (realGaussianTiltTensorNormalizer u /
        realStandardGaussianNormalizer ^ Fintype.card Iota) ^ 2 =
      Finset.prod Finset.univ (fun i => 1 + u i) :=
  finiteGaussianNormalizer_square _ _ _
    (ne_of_gt realStandardGaussianNormalizer_positive)
    (fun i => realGaussianTiltMoment_sq (u i) (hu i))

end PrimeFactorOscillations

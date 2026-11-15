/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import PrimeFactorOscillations.Helpers.HamiltonianGaussianLinearWick

/-! # Unrestricted complex covariance realized by standard Gaussians

The covariance coordinates may be arbitrarily large or indefinite.
Complex square roots realize them against the actual standard Gaussian
density. The exact mixed Wick recursion therefore applies without an
artificial covariance-norm restriction.
-/

set_option autoImplicit false
set_option Elab.async false

noncomputable section

namespace PrimeFactorOscillations

def complexGaussianSquareRoot (z : Complex) : Complex :=
  z ^ (Inv.inv (2 : Complex))

theorem complexGaussianSquareRoot_sq (z : Complex) :
    complexGaussianSquareRoot z ^ 2 = z :=
  Complex.cpow_nat_inv_pow z (n := 2) (by decide)

theorem standardGaussianMoment_recurrence (n : Nat) :
    complexGaussianMoment (gaussianTiltPrecision 0) (n + 2) =
      ((n + 1 : Nat) : Complex) * complexGaussianMoment (gaussianTiltPrecision 0) n := by
  have hb : 0 < (gaussianTiltPrecision 0).re := by
    norm_num [gaussianTiltPrecision, Complex.div_re]
  have hTwo : (2 : Complex) * gaussianTiltPrecision 0 = 1 := by
    norm_num [gaussianTiltPrecision]
  simpa only [hTwo, div_one] using
    complexGaussianMoment_recurrence (gaussianTiltPrecision 0) hb n

theorem standardGaussianMonomial_moment (z w : Complex) (hw : w ^ 2 = z) (n : Nat) :
    w ^ n * complexGaussianMoment (gaussianTiltPrecision 0) n /
        complexGaussianMoment (gaussianTiltPrecision 0) 0 =
      gaussianWickMonomial z n := by
  let b := gaussianTiltPrecision 0
  have hb : 0 < b.re := by
    dsimp only [b]
    norm_num [gaussianTiltPrecision, Complex.div_re]
  have hM0 := complexGaussianMoment_zero_nonzero b hb
  change w ^ n * complexGaussianMoment b n / complexGaussianMoment b 0 = _
  induction n using Nat.strong_induction_on with
  | h n ih =>
    cases n with
    | zero =>
      simp only [pow_zero, one_mul, gaussianWickMonomial, div_self hM0]
    | succ n =>
      cases n with
      | zero =>
        rw [complexGaussianMoment_first b hb, mul_zero, zero_div]
        rfl
      | succ n =>
        have hPrev := ih n (by omega)
        change w ^ (n + 2) * complexGaussianMoment b (n + 2) /
            complexGaussianMoment b 0 = gaussianWickMonomial z (n + 2)
        rw [standardGaussianMoment_recurrence, gaussianWickMonomial]
        calc
          w ^ (n + 2) *
              (((n + 1 : Nat) : Complex) * complexGaussianMoment b n) /
              complexGaussianMoment b 0 =
            ((n + 1 : Nat) : Complex) * w ^ 2 *
              (w ^ n * complexGaussianMoment b n / complexGaussianMoment b 0) := by
                rw [pow_add]
                ring
          _ = ((n + 1 : Nat) : Complex) * z * gaussianWickMonomial z n := by
            rw [hw, hPrev]

variable {Iota : Type*} [Fintype Iota] [DecidableEq Iota]

def standardGaussianPolynomialKernel (z : Iota -> Complex)
    (p : MvPolynomial Iota Complex) : (Iota -> Real) -> Complex :=
  gaussianMvTiltKernel (fun _ => 0) (fun i => complexGaussianSquareRoot (z i)) p

theorem standardGaussianTensor_normalized (z : Iota -> Complex) (d : Iota -> Nat) :
    MeasureTheory.integral gaussianTensorMeasure
        (gaussianTensorTiltKernel (fun _ => 0)
          (fun i => complexGaussianSquareRoot (z i)) d) /
        gaussianTensorTiltNormalizer (fun _ : Iota => 0) =
      gaussianMonomialState z d := by
  rw [gaussianTensorTiltKernel_integral, gaussianTensorTiltNormalizer,
    <- Finset.prod_div_distrib]
  unfold gaussianMonomialState
  apply Finset.prod_congr rfl
  intro i hi
  exact standardGaussianMonomial_moment (z i) _ (complexGaussianSquareRoot_sq (z i)) (d i)

theorem standardGaussianPolynomialKernel_integrable (z : Iota -> Complex)
    (p : MvPolynomial Iota Complex) :
    MeasureTheory.Integrable (standardGaussianPolynomialKernel z p) gaussianTensorMeasure :=
  gaussianMvTiltKernel_integrable (fun _ => 0)
    (fun i => complexGaussianSquareRoot (z i)) (fun _ => by norm_num) p

theorem standardGaussianPolynomial_normalized (z : Iota -> Complex)
    (p : MvPolynomial Iota Complex) :
    MeasureTheory.integral gaussianTensorMeasure (standardGaussianPolynomialKernel z p) /
        gaussianTensorTiltNormalizer (fun _ : Iota => 0) =
      gaussianPolynomialState z p := by
  unfold standardGaussianPolynomialKernel
  rw [gaussianMvTiltKernel_expansion]
  unfold gaussianTensorPolynomialTiltKernel gaussianPolynomialState
  rw [MeasureTheory.integral_finsetSum p.support
    (fun d _ => (gaussianTensorTiltKernel_integrable (fun _ => 0)
      (fun i => complexGaussianSquareRoot (z i)) (fun _ => by norm_num)
        (fun i => d i)).const_mul (p.coeff d)),
    Finset.sum_div]
  apply Finset.sum_congr rfl
  intro d hd
  rw [MeasureTheory.integral_const_mul, mul_div_assoc,
    standardGaussianTensor_normalized z (fun i => d i)]

theorem standardGaussianLinearWickIntegral_norm_bound (z : Iota -> Complex)
    (c : Real) (hc : 0 <= c) (e : Nat) (xs : List (Iota -> Complex))
    (hLen : xs.length = 2 * e)
    (hCov : forall a, Membership.mem xs a ->
      forall b, Membership.mem xs b -> norm (gaussianLinearCovariance z a b) <= c) :
    norm (MeasureTheory.integral gaussianTensorMeasure
        (standardGaussianPolynomialKernel z (gaussianLinearProduct xs)) /
        gaussianTensorTiltNormalizer (fun _ : Iota => 0)) <=
      (wickPairCount e : Real) * c ^ e := by
  rw [standardGaussianPolynomial_normalized]
  exact gaussianLinearWickValue_norm_bound z c hc e xs hLen hCov

end PrimeFactorOscillations

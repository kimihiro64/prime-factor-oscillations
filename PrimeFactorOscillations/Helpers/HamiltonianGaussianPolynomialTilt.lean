/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import Mathlib.Algebra.Polynomial.Eval.Degree
import PrimeFactorOscillations.Helpers.HamiltonianGaussianQuadraticTilt
import PrimeFactorOscillations.Helpers.HamiltonianWickExpansion

/-! # Actual polynomial Gaussian reweighting

All polynomial moments of the complete complex quadratic tilt are
integrable. Their normalized integrals are evaluated by the same pairing
recurrence as Wick moments, without dropping the covariance quotient.
-/

set_option autoImplicit false
set_option Elab.async false

noncomputable section

namespace PrimeFactorOscillations

open MeasureTheory

theorem complexGaussianMoment_zero_nonzero (b : Complex) (hb : 0 < b.re) :
    Not (complexGaussianMoment b 0 = 0) := by
  have hKernel : complexGaussianKernel b 0 =
      (fun x : Real => Complex.exp (-b * (x : Complex) ^ 2)) := by
    funext x
    simp only [complexGaussianKernel, pow_zero, one_mul]
  have hSq : complexGaussianMoment b 0 ^ 2 = (Real.pi : Complex) / b := by
    rw [complexGaussianMoment, hKernel]
    exact integral_gaussian_sq_complex hb
  have hb0 : Not (b = 0) := by
    intro h
    have hRe := congrArg Complex.re h
    simp only [Complex.zero_re] at hRe
    rw [hRe] at hb
    exact (lt_irrefl 0) hb
  have hPi : Not ((Real.pi : Complex) = 0) := by
    intro h
    have hRe := congrArg Complex.re h
    simp only [Complex.ofReal_re, Complex.zero_re] at hRe
    exact Real.pi_ne_zero hRe
  intro hZero
  rw [hZero, zero_pow (by decide)] at hSq
  exact (div_ne_zero hPi hb0) hSq.symm

def gaussianWickMonomial (z : Complex) : Nat -> Complex
  | 0 => 1
  | 1 => 0
  | n + 2 => ((n + 1 : Nat) : Complex) * z * gaussianWickMonomial z n

theorem gaussianWickMonomial_even (z : Complex) (e : Nat) :
    gaussianWickMonomial z (2 * e) = (wickPairCount e : Complex) * z ^ e := by
  induction e with
  | zero => simp [gaussianWickMonomial, wickPairCount]
  | succ e ih =>
    have hIndex : 2 * (e + 1) = 2 * e + 2 := by omega
    rw [hIndex, gaussianWickMonomial, ih, wickPairCount, pow_succ]
    push_cast
    ring

theorem gaussianWickMonomial_odd (z : Complex) (e : Nat) :
    gaussianWickMonomial z (2 * e + 1) = 0 := by
  induction e with
  | zero => rfl
  | succ e ih =>
    have hIndex : 2 * (e + 1) + 1 = (2 * e + 1) + 2 := by omega
    rw [hIndex, gaussianWickMonomial, ih, mul_zero]

private theorem tilt_one_add_nonzero (z : Complex) (hz : norm z < 1) :
    Not (1 + z = 0) := by
  intro h
  have hEq : z = -(1 : Complex) := by
    calc
      z = (1 + z) - 1 := by ring
      _ = -1 := by rw [h]; ring
  rw [hEq, norm_neg, norm_one] at hz
  exact (lt_irrefl 1) hz

theorem gaussianTilt_variance (z : Complex) (hz : norm z < 1)
    (w : Complex) (hw : w ^ 2 = z / (1 + z)) :
    w ^ 2 / (2 * gaussianTiltPrecision z) = z := by
  have hAdd := tilt_one_add_nonzero z hz
  rw [hw]
  unfold gaussianTiltPrecision
  field_simp [hAdd]
  ring

theorem gaussianTilt_monomial_moment (z : Complex) (hz : norm z < 1)
    (w : Complex) (hw : w ^ 2 = z / (1 + z)) (n : Nat) :
    w ^ n * complexGaussianMoment (gaussianTiltPrecision z) n /
        complexGaussianMoment (gaussianTiltPrecision z) 0 =
      gaussianWickMonomial z n := by
  let b := gaussianTiltPrecision z
  have hb : 0 < b.re :=
    lt_trans (by norm_num) (gaussianTiltPrecision_real_part z hz)
  have hM0 := complexGaussianMoment_zero_nonzero b hb
  have hVariance : w ^ 2 / (2 * b) = z := gaussianTilt_variance z hz w hw
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
        rw [complexGaussianMoment_recurrence b hb n, gaussianWickMonomial]
        calc
          w ^ (n + 2) *
              (((n + 1 : Nat) : Complex) * complexGaussianMoment b n / (2 * b)) /
              complexGaussianMoment b 0 =
            ((n + 1 : Nat) : Complex) * (w ^ 2 / (2 * b)) *
              (w ^ n * complexGaussianMoment b n / complexGaussianMoment b 0) := by
                rw [pow_add]
                ring
          _ = ((n + 1 : Nat) : Complex) * z * gaussianWickMonomial z n := by
            rw [hVariance, hPrev]

def gaussianPolynomialTiltKernel (z w : Complex) (p : Polynomial Complex)
    (x : Real) : Complex :=
  p.eval (w * (x : Complex)) *
    Complex.exp ((z / (1 + z)) * (x : Complex) ^ 2 / 2) *
    Complex.exp (-(x : Complex) ^ 2 / 2)

theorem gaussianPolynomialTiltKernel_expansion (z w : Complex)
    (p : Polynomial Complex) :
    gaussianPolynomialTiltKernel z w p =
      (fun x : Real => Finset.sum (Finset.range (p.natDegree + 1))
        (fun n => (p.coeff n * w ^ n) *
          complexGaussianKernel (gaussianTiltPrecision z) n x)) := by
  funext x
  have hExponent :
      (z / (1 + z)) * (x : Complex) ^ 2 / 2 -
          (x : Complex) ^ 2 / 2 =
        -gaussianTiltPrecision z * (x : Complex) ^ 2 := by
    unfold gaussianTiltPrecision
    ring
  unfold gaussianPolynomialTiltKernel
  rw [mul_assoc, <- Complex.exp_add]
  rw [show (z / (1 + z)) * (x : Complex) ^ 2 / 2 +
      -(x : Complex) ^ 2 / 2 =
      (z / (1 + z)) * (x : Complex) ^ 2 / 2 -
        (x : Complex) ^ 2 / 2 by ring, hExponent]
  rw [Polynomial.eval_eq_sum_range, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro n hn
  rw [mul_pow]
  unfold complexGaussianKernel
  ring

theorem gaussianPolynomialTiltKernel_integrable (z : Complex) (hz : norm z < 1)
    (w : Complex) (p : Polynomial Complex) :
    MeasureTheory.Integrable (gaussianPolynomialTiltKernel z w p) := by
  rw [gaussianPolynomialTiltKernel_expansion]
  exact MeasureTheory.integrable_finset_sum _
    (fun n _ => (tiltedGaussianKernel_integrable z hz n).const_mul (p.coeff n * w ^ n))

theorem gaussianPolynomialTilt_integral (z : Complex) (hz : norm z < 1)
    (w : Complex) (p : Polynomial Complex) :
    MeasureTheory.integral MeasureTheory.volume (gaussianPolynomialTiltKernel z w p) =
      Finset.sum (Finset.range (p.natDegree + 1))
        (fun n => (p.coeff n * w ^ n) *
          complexGaussianMoment (gaussianTiltPrecision z) n) := by
  rw [gaussianPolynomialTiltKernel_expansion]
  rw [MeasureTheory.integral_finsetSum _
    (fun n _ => (tiltedGaussianKernel_integrable z hz n).const_mul (p.coeff n * w ^ n))]
  apply Finset.sum_congr rfl
  intro n hn
  rw [MeasureTheory.integral_const_mul]
  rfl

theorem gaussianPolynomialTilt_normalized (z : Complex) (hz : norm z < 1)
    (w : Complex) (hw : w ^ 2 = z / (1 + z)) (p : Polynomial Complex) :
    MeasureTheory.integral MeasureTheory.volume (gaussianPolynomialTiltKernel z w p) /
        complexGaussianMoment (gaussianTiltPrecision z) 0 =
      Finset.sum (Finset.range (p.natDegree + 1))
        (fun n => p.coeff n * gaussianWickMonomial z n) := by
  rw [gaussianPolynomialTilt_integral z hz w p, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro n hn
  calc
    (p.coeff n * w ^ n) * complexGaussianMoment (gaussianTiltPrecision z) n /
        complexGaussianMoment (gaussianTiltPrecision z) 0 =
      p.coeff n * (w ^ n * complexGaussianMoment (gaussianTiltPrecision z) n /
        complexGaussianMoment (gaussianTiltPrecision z) 0) := by ring
    _ = p.coeff n * gaussianWickMonomial z n := by
      rw [gaussianTilt_monomial_moment z hz w hw n]

end PrimeFactorOscillations

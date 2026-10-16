/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.UniformCarrierBounds

/-!
# Uniform Carrier Perturbation

Quantitative finite-profile quotient stability under uniform coefficient perturbations.
-/

set_option autoImplicit false
set_option Elab.async false

noncomputable section
namespace PrimeFactorOscillations.UniformCarrier

open BombieriVinogradov.ComplexAnalysis

theorem normalized_prefix_errors (A B : PrimeClockLaw) (N r : Nat) (hr : 0 < r)
    (D b R t : Real) (hD : 0 <= D) (ht : 0 <= t) (htb : t <= b) (hbR : b < R)
    (hcoeff : forall j, norm (taylorCoefficient (A.complexPrefix N) 0 j -
      taylorCoefficient (B.complexPrefix N) 0 j) <= D / R ^ j) :
    abs (Nat.normalizedDescFactorialPolynomial (prefixCoefficient A N) r t -
      Nat.normalizedDescFactorialPolynomial (prefixCoefficient B N) r t) <= D / (1 - b / R) /\
    abs (deriv (Nat.normalizedDescFactorialPolynomial (prefixCoefficient A N) r) t -
      deriv (Nat.normalizedDescFactorialPolynomial (prefixCoefficient B N) r) t) <=
        D / (R * (1 - b / R) ^ 2) := by
  let c : Nat -> Complex := fun j =>
    taylorCoefficient (A.complexPrefix N) 0 j - taylorCoefficient (B.complexPrefix N) 0 j
  have hv := Nat.norm_descFactorial_coefficient_le_geometric r hr c D b R t hD ht htb hbR hcoeff
  have hd := Nat.norm_descFactorial_coefficient_deriv_le_geometric r hr c D b R t hD ht htb hbR hcoeff
  have hreal (w : Complex) (m j : Nat) :
      (w * (t : Complex) ^ m *
        ((r.descFactorial j : Complex) / (r : Complex) ^ j)).re =
          w.re * t ^ m * ((r.descFactorial j : Real) / (r : Real) ^ j) := by
    have hw : ((r.descFactorial j : Complex) / (r : Complex) ^ j) =
        Complex.ofReal ((r.descFactorial j : Real) / (r : Real) ^ j) := by
      simp only [Complex.ofReal_div, Complex.ofReal_pow, Complex.ofReal_natCast]
    rw [hw, <- Complex.ofReal_pow]
    simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]
  have hveq : ((Finset.range (r + 1)).sum (fun j => c j * (t : Complex) ^ j *
      ((r.descFactorial j : Complex) / (r : Complex) ^ j))).re =
        Nat.normalizedDescFactorialPolynomial (prefixCoefficient A N) r t -
          Nat.normalizedDescFactorialPolynomial (prefixCoefficient B N) r t := by
    unfold Nat.normalizedDescFactorialPolynomial
    rw [Complex.re_sum, <- Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro j _
    rw [hreal]
    simp only [c, Complex.sub_re, prefixCoefficient]
    ring
  have hdeq : ((Finset.range (r + 1)).sum (fun j => (j : Complex) * c j *
      (t : Complex) ^ (j - 1) *
        ((r.descFactorial j : Complex) / (r : Complex) ^ j))).re =
        deriv (Nat.normalizedDescFactorialPolynomial (prefixCoefficient A N) r) t -
          deriv (Nat.normalizedDescFactorialPolynomial (prefixCoefficient B N) r) t := by
    rw [Nat.deriv_normalizedDescFactorialPolynomial,
      Nat.deriv_normalizedDescFactorialPolynomial, Complex.re_sum, <- Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro j _
    rw [hreal]
    simp only [c, Complex.mul_re, Complex.natCast_re, Complex.natCast_im,
      Complex.sub_re, prefixCoefficient, zero_mul, sub_zero]
    ring
  constructor
  . rw [<- hveq]
    exact (Complex.abs_re_le_norm _).trans hv
  . rw [<- hdeq]
    exact (Complex.abs_re_le_norm _).trans hd

theorem normalized_quotient_error (A AN V VN d C D M : Real)
    (hd : 0 < d) (hC : 0 <= C) (hD : 0 <= D) (hM : 0 <= M)
    (hA : d <= A) (hAN : d <= AN)
    (hV : abs V <= M) (hValue : abs (AN - A) <= C)
    (hDeriv : abs (VN - V) <= D) :
    abs (VN / AN - V / A) <= D / d + M * C / (d * d) := by
  have hApos := hd.trans_le hA
  have hANpos := hd.trans_le hAN
  have hid : VN / AN - V / A =
      (VN - V) / AN + V * (A - AN) / (AN * A) := by
    field_simp [hANpos.ne', hApos.ne']
    ring
  have hprod : d * d <= AN * A := mul_le_mul hAN hA hd.le hANpos.le
  have hfirst : abs ((VN - V) / AN) <= D / d := by
    rw [abs_div, abs_of_pos hANpos]
    exact (div_le_div_of_nonneg_right hDeriv hANpos.le).trans
      (div_le_div_of_nonneg_left hD hd hAN)
  have hsecond : abs (V * (A - AN) / (AN * A)) <= M * C / (d * d) := by
    rw [abs_div, abs_mul, abs_sub_comm A AN, abs_of_pos (mul_pos hANpos hApos)]
    have hn := mul_le_mul hV hValue (abs_nonneg _) hM
    exact (div_le_div_of_nonneg_right hn (mul_nonneg hANpos.le hApos.le)).trans
      (div_le_div_of_nonneg_left (mul_nonneg hM hC) (mul_pos hd hd) hprod)
  rw [hid]
  exact (abs_add_le _ _).trans (add_le_add hfirst hsecond)

theorem ratio_error_of_coefficient_bound (A B : PrimeClockLaw) (N r : Nat) (hr : 0 < r)
    (u b R D m M : Real) (hu : 0 < u) (htb : (r : Real) / u <= b)
    (hbR : b < R) (hD : 0 <= D) (hm : 0 < m) (hM : 0 <= M)
    (hcoeff : forall j, norm (taylorCoefficient (A.complexPrefix N) 0 j -
      taylorCoefficient (B.complexPrefix N) 0 j) <= D / R ^ j)
    (hBase : m <= Nat.normalizedDescFactorialPolynomial (prefixCoefficient B N) r ((r : Real) / u))
    (hSmall : D / (1 - b / R) <= m / 2)
    (hV : abs (deriv (Nat.normalizedDescFactorialPolynomial (prefixCoefficient B N) r)
      ((r : Real) / u)) <= M) :
    0 < Nat.factorialConvolution (prefixCoefficient A N) r u /\
    abs (prefixRatio A N r u - prefixRatio B N r u) <=
      b ^ 2 / (r : Real) *
        ((D / (R * (1 - b / R) ^ 2)) / (m / 2) +
          M * (D / (1 - b / R)) / ((m / 2) * (m / 2))) := by
  have hrR : (0 : Real) < r := by exact_mod_cast hr
  let t := (r : Real) / u
  have ht : 0 <= t := div_nonneg hrR.le hu.le
  have hb : 0 <= b := ht.trans htb
  have hR : 0 < R := hb.trans_lt hbR
  have hq : 0 < 1 - b / R := sub_pos.mpr ((div_lt_one hR).mpr hbR)
  let X := Nat.normalizedDescFactorialPolynomial (prefixCoefficient B N) r t
  let Y := Nat.normalizedDescFactorialPolynomial (prefixCoefficient A N) r t
  let V := deriv (Nat.normalizedDescFactorialPolynomial (prefixCoefficient B N) r) t
  let W := deriv (Nat.normalizedDescFactorialPolynomial (prefixCoefficient A N) r) t
  have he := normalized_prefix_errors A B N r hr D b R t hD ht htb hbR hcoeff
  have hX : m / 2 <= X := by change m / 2 <= _; linarith only [hBase, hm]
  have hY : m / 2 <= Y := by
    have helo := (abs_le.mp he.1).1
    change -(D / (1 - b / R)) <= Y - X at helo
    change m <= X at hBase
    linarith only [helo, hBase, hSmall]
  have hXp : 0 < X := (half_pos hm).trans_le hX
  have hYp : 0 < Y := (half_pos hm).trans_le hY
  have hquot := normalized_quotient_error X Y V W (m / 2)
    (D / (1 - b / R)) (D / (R * (1 - b / R) ^ 2)) M
    (half_pos hm) (div_nonneg hD hq.le) (by positivity) hM
    hX hY hV he.1 he.2
  constructor
  . rw [Nat.factorialConvolution_eq_normalizedDescFactorialPolynomial
      (prefixCoefficient A N) r hr u hu.ne']
    exact mul_pos (by positivity) hYp
  . unfold prefixRatio
    rw [Nat.factorialConvolution_ratio_eq_normalized_logDeriv
      (prefixCoefficient A N) r hr u hu.ne' hYp.ne',
      Nat.factorialConvolution_ratio_eq_normalized_logDeriv
      (prefixCoefficient B N) r hr u hu.ne' hXp.ne']
    change abs ((t - (t ^ 2 / r) * W / Y) - (t - (t ^ 2 / r) * V / X)) <= _
    have hid : (t - (t ^ 2 / r) * W / Y) - (t - (t ^ 2 / r) * V / X) =
        -(t ^ 2 / r) * (W / Y - V / X) := by ring
    rw [hid, abs_mul, abs_neg, abs_of_nonneg (div_nonneg (sq_nonneg t) hrR.le)]
    apply mul_le_mul _ hquot (abs_nonneg _) (by positivity)
    apply div_le_div_of_nonneg_right _ hrR.le
    nlinarith

end PrimeFactorOscillations.UniformCarrier

/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.CubicReciprocalMellin
/-!
# Nonvanishing of the reciprocal Gaussian Mellin window

Factors the exact signed four-scale multiplier and proves that the actual
Mellin transform is nonzero on 0 < Re(s) < 1. No hypothesis on zeta zeros is
used, and no prime-carrier or Abel-endpoint estimate is asserted.
-/

set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace PrimeFactorOscillations.CubicReciprocalMellin
open CubicReciprocalGaussian OAI.SevenEighths
theorem base_two_cpow_ne_zero (s : Complex) :
    Not ((2 : Complex) ^ s = 0) := by
  intro h
  have h0 := ((Complex.cpow_eq_zero_iff (2 : Complex) s).1 h).1
  norm_num at h0

theorem scaleMultiplier_factor (s : Complex) :
    scaleMultiplier s =
      (((2 : Complex) ^ s - 1) * ((2 : Complex) ^ s - 2) *
        ((2 : Complex) ^ s - 4) * ((2 : Complex) ^ s + 2)) /
        (16 * ((2 : Complex) ^ s) ^ 2) := by
  let z : Complex := (2 : Complex) ^ s
  have hz : Not (z = 0) := base_two_cpow_ne_zero s
  have hhalf : (2 : Complex) ^ (-s) * ((1 / 2 : Real) : Complex) ^ (-s) = 1 := by
    have h := Complex.mul_cpow_ofReal_nonneg
      (a := (2 : Real)) (b := (1 / 2 : Real)) (by norm_num) (by norm_num) (-s)
    norm_num at h
    simpa only [Complex.ofReal_div, Complex.ofReal_one, Complex.ofReal_ofNat] using h.symm
  have htwo : (2 : Complex) ^ (-s) = z ^ (-1 : Int) := by
    simp only [Complex.cpow_neg, zpow_neg_one, z]
  have hh : ((1 / 2 : Real) : Complex) ^ (-s) = z := by
    rw [htwo, zpow_neg_one] at hhalf
    calc
      _ = (z * (Inv.inv z)) * ((1 / 2 : Real) : Complex) ^ (-s) := by
        field_simp
      _ = z := by rw [mul_assoc, hhalf, mul_one]
  have hf : ((4 : Real) : Complex) ^ (-s) =
      ((2 : Complex) ^ (-s)) ^ 2 := by
    have h := Complex.mul_cpow_ofReal_nonneg
      (a := (2 : Real)) (b := (2 : Real)) (by norm_num) (by norm_num) (-s)
    norm_num [pow_two] at h
    simpa only [Complex.ofReal_div, Complex.ofReal_one, Complex.ofReal_ofNat, pow_two] using h
  have hq : ((1 / 4 : Real) : Complex) ^ (-s) =
      (((1 / 2 : Real) : Complex) ^ (-s)) ^ 2 := by
    have h := Complex.mul_cpow_ofReal_nonneg
      (a := (1 / 2 : Real)) (b := (1 / 2 : Real)) (by norm_num) (by norm_num) (-s)
    norm_num [pow_two] at h
    simpa only [Complex.ofReal_div, Complex.ofReal_one, Complex.ofReal_ofNat, pow_two] using h
  have he : scaleMultiplier s =
      (5 / 4 : Complex) * (Inv.inv z) - (5 / 16 : Complex) * z -
        ((Inv.inv z)) ^ 2 + (1 / 16 : Complex) * z ^ 2 := by
    norm_num [scaleMultiplier, Fin.sum_univ_succ, coefficients, radii] at *
    rw [hf, hq, hh, htwo]
    ring
  rw [he]
  change _ = ((z - 1) * (z - 2) * (z - 4) * (z + 2)) / (16 * z ^ 2)
  field_simp
  ring

theorem baseMultiplier_ne_zero (s : Complex) (hs : 0 < s.re) :
    Not (baseMultiplier s = 0) := by
  have ha : Not ((ProbeRadialMellin.paperConstant : Complex) ^ (-(s / 2)) = 0) := by
    intro h
    have h0 := ((Complex.cpow_eq_zero_iff _ _).1 h).1
    have hp : Not ((ProbeRadialMellin.paperConstant : Real) = 0) :=
      ne_of_gt ProbeRadialMellin.paperConstant_pos
    exact hp (Complex.ofReal_eq_zero.mp h0)
  have hg : Not (Complex.Gamma (s / 2) = 0) :=
    Complex.Gamma_ne_zero_of_re_pos (by
      simp only [Complex.div_ofNat_re]
      linarith)
  dsimp [baseMultiplier]
  exact mul_ne_zero (by norm_num) (mul_ne_zero ha hg)

theorem scaleMultiplier_ne_zero (s : Complex) (hs : 0 < s.re) (hs1 : s.re < 1) :
    Not (scaleMultiplier s = 0) := by
  have hn : norm ((2 : Complex) ^ s) = (2 : Real) ^ s.re := by
    simpa only [Complex.ofReal_ofNat] using
      (Complex.norm_cpow_eq_rpow_re_of_pos (by norm_num : (0 : Real) < 2) s)
  have hlo : 1 < norm ((2 : Complex) ^ s) := by
    rw [hn]
    exact Real.one_lt_rpow (by norm_num) hs
  have hhi : norm ((2 : Complex) ^ s) < 2 := by
    rw [hn]
    have h := Real.rpow_lt_rpow_of_exponent_lt (by norm_num : (1 : Real) < 2) hs1
    simpa only [Real.rpow_one] using h
  have h1 : Not ((2 : Complex) ^ s - 1 = 0) := by
    intro h
    have he : (2 : Complex) ^ s = 1 := sub_eq_zero.mp h
    rw [he, norm_one] at hlo
    linarith
  have h2 : Not ((2 : Complex) ^ s - 2 = 0) := by
    intro h
    have he : (2 : Complex) ^ s = 2 := sub_eq_zero.mp h
    rw [he] at hhi
    norm_num at hhi
  have h4 : Not ((2 : Complex) ^ s - 4 = 0) := by
    intro h
    have he : (2 : Complex) ^ s = 4 := sub_eq_zero.mp h
    rw [he] at hhi
    norm_num at hhi
  have hm2 : Not ((2 : Complex) ^ s + 2 = 0) := by
    intro h
    have he : (2 : Complex) ^ s = -2 := by linear_combination h
    rw [he, norm_neg] at hhi
    norm_num at hhi
  rw [scaleMultiplier_factor]
  exact div_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero h1 h2) h4) hm2)
    (mul_ne_zero (by norm_num) (pow_ne_zero _ (base_two_cpow_ne_zero s)))

theorem primeProfile_mellin_ne_zero (s : Complex)
    (hs : 0 < s.re) (hs1 : s.re < 1) :
    Not (mellin primeProfile s = 0) := by
  rw [(primeProfile_hasMellin s hs).2]
  exact mul_ne_zero (baseMultiplier_ne_zero s hs) (scaleMultiplier_ne_zero s hs hs1)

end PrimeFactorOscillations.CubicReciprocalMellin

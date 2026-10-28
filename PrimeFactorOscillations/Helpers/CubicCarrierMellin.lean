/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.CubicReciprocalNonzero
/-!
# Mellin transfer in the actual squared-radius carrier coordinate

The carrier profile is evaluated at the integer norm, not its square.
The Mellin argument is therefore twice that of the prime-radius profile.
Proves convergence and nonvanishing on 1/2 < Re(s) < 1 without RH.
-/

set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace PrimeFactorOscillations.CubicCarrierMellin
open MeasureTheory
open CubicReciprocalGaussian CubicReciprocalMellin

theorem scaleMultiplier_ne_zero_above_one (s : Complex)
    (hs : 1 < s.re) (hs2 : s.re < 2) :
    Not (scaleMultiplier s = 0) := by
  have hn : norm ((2 : Complex) ^ s) = (2 : Real) ^ s.re := by
    simpa only [Complex.ofReal_ofNat] using
      (Complex.norm_cpow_eq_rpow_re_of_pos (by norm_num : (0 : Real) < 2) s)
  have hlo : 2 < norm ((2 : Complex) ^ s) := by
    rw [hn]
    have h := Real.rpow_lt_rpow_of_exponent_lt (by norm_num : (1 : Real) < 2) hs
    simpa only [Real.rpow_one] using h
  have hhi : norm ((2 : Complex) ^ s) < 4 := by
    rw [hn]
    have h := Real.rpow_lt_rpow_of_exponent_lt (by norm_num : (1 : Real) < 2) hs2
    norm_num at h
    exact h
  have h1 : Not ((2 : Complex) ^ s - 1 = 0) := by
    intro h
    have he : (2 : Complex) ^ s = 1 := sub_eq_zero.mp h
    rw [he, norm_one] at hlo
    linarith
  have h2 : Not ((2 : Complex) ^ s - 2 = 0) := by
    intro h
    have he : (2 : Complex) ^ s = 2 := sub_eq_zero.mp h
    rw [he] at hlo
    norm_num at hlo
  have h4 : Not ((2 : Complex) ^ s - 4 = 0) := by
    intro h
    have he : (2 : Complex) ^ s = 4 := sub_eq_zero.mp h
    rw [he] at hhi
    norm_num at hhi
  have hm2 : Not ((2 : Complex) ^ s + 2 = 0) := by
    intro h
    have he : (2 : Complex) ^ s = -2 := by linear_combination h
    rw [he, norm_neg] at hlo
    norm_num at hlo
  rw [scaleMultiplier_factor]
  exact div_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero h1 h2) h4) hm2)
    (mul_ne_zero (by norm_num) (pow_ne_zero _ (base_two_cpow_ne_zero s)))

def carrierMultiplier (s : Complex) : Complex :=
  2 * (baseMultiplier (2 * s) * scaleMultiplier (2 * s))

theorem carrierProfile_hasMellin (s : Complex) (hs : 0 < s.re) :
    HasMellin carrierProfile s (carrierMultiplier s) := by
  have h2 : 0 < (2 * s).re := by
    simp only [Complex.mul_re]
    norm_num
    linarith
  have hw := primeProfile_hasMellin (2 * s) h2
  have hf : (fun u : Real => carrierProfile (u ^ (2 : Real))) =
      CubicReciprocalMellin.primeProfile := by
    funext u
    exact congrArg carrierProfile (Real.rpow_natCast u 2)
  have ha : (2 * s) / (2 : Complex) = s := by ring
  have hc : MellinConvergent carrierProfile s := by
    have h := (MellinConvergent.comp_rpow (f := carrierProfile)
      (s := 2 * s) (a := (2 : Real)) (by norm_num : Not ((2 : Real) = 0))).1
      (by rw [hf]; exact hw.1)
    simpa only [Complex.ofReal_ofNat, ha] using h
  have hm := mellin_comp_rpow carrierProfile (2 * s) (2 : Real)
  rw [hf, hw.2] at hm
  have he : mellin carrierProfile s = carrierMultiplier s := by
    simp only [Complex.ofReal_ofNat, ha] at hm
    norm_num [Complex.real_smul] at hm
    dsimp [carrierMultiplier]
    linear_combination -2 * hm
  exact And.intro hc he

theorem carrierMultiplier_ne_zero (s : Complex)
    (hs : (1 / 2 : Real) < s.re) (hs1 : s.re < 1) :
    Not (carrierMultiplier s = 0) := by
  have hre : (2 * s).re = 2 * s.re := by
    simp only [Complex.mul_re]
    norm_num
  dsimp [carrierMultiplier]
  exact mul_ne_zero (by norm_num)
    (mul_ne_zero (baseMultiplier_ne_zero (2 * s) (by rw [hre]; linarith))
      (scaleMultiplier_ne_zero_above_one (2 * s)
        (by rw [hre]; linarith) (by rw [hre]; linarith)))

theorem carrierProfile_mellin_ne_zero (s : Complex)
    (hs : (1 / 2 : Real) < s.re) (hs1 : s.re < 1) :
    Not (mellin carrierProfile s = 0) := by
  rw [(carrierProfile_hasMellin s (by linarith)).2]
  exact carrierMultiplier_ne_zero s hs hs1

end PrimeFactorOscillations.CubicCarrierMellin

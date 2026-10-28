/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.CubicCompensatedWindow
import PrimeFactorOscillations.Helpers.CubicReciprocalGaussian

/-!
# Mellin transfer of the reciprocal Gaussian window

Computes the convergent transform of the actual four-scale prime profile.
Every signed coefficient is retained. This is a window identity, not an
estimate on the arithmetic prime-carrier or Abel endpoint.
-/

set_option autoImplicit false
set_option Elab.async false

noncomputable section
namespace PrimeFactorOscillations.CubicReciprocalMellin
open OAI OAI.SevenEighths
open MeasureTheory ProbeRadialMellin
open CubicReciprocalGaussian CubicCompensatedWindow

def radii : Fin 4 -> Real := ![2, 1 / 2, 4, 1 / 4]

def baseProfile (u : Real) : Complex := expWindow (paperConstant * u ^ 2)
def primeProfile (u : Real) : Complex := carrierProfile (u ^ 2)

def baseMultiplier (s : Complex) : Complex :=
  HSMul.hSMul (Inv.inv (2 : Real))
    ((paperConstant : Complex) ^ (-(s / 2)) * Complex.Gamma (s / 2))

def scaleMultiplier (s : Complex) : Complex :=
  Finset.univ.sum (fun i : Fin 4 => coefficients i * (radii i : Complex) ^ (-s))

theorem radii_pos (i : Fin 4) : 0 < radii i := by
  fin_cases i <;> norm_num [radii]

theorem radii_sq (i : Fin 4) : radii i ^ 2 = scales i := by
  fin_cases i <;> norm_num [radii, scales]

theorem baseProfile_hasMellin (s : Complex) (hs : 0 < s.re) :
    HasMellin baseProfile s (baseMultiplier s) := by
  have hs2 : 0 < (s / 2).re := by
    simp only [Complex.div_ofNat_re]
    linarith
  let f : Real -> Complex := fun v => expWindow (paperConstant * v)
  have hfc : MellinConvergent f (s / 2) :=
    (MellinConvergent.comp_mul_left paperConstant_pos).2 (expWindow_convergent _ hs2)
  have hfm : mellin f (s / 2) =
      (paperConstant : Complex) ^ (-(s / 2)) * Complex.Gamma (s / 2) := by
    have h := mellin_comp_mul_left expWindow (s / 2) paperConstant_pos
    rw [expWindow_mellin _ hs2] at h
    simpa only [smul_eq_mul] using h
  have hc : MellinConvergent (fun u : Real => f (u ^ (2 : Real))) s :=
    (MellinConvergent.comp_rpow (by norm_num : Not ((2 : Real) = 0))).2
      (by simpa only [Complex.ofReal_ofNat] using hfc)
  have hpow : (fun u : Real => f (u ^ (2 : Real))) =
      (fun u : Real => f (u ^ 2)) := by
    funext u
    exact congrArg f (Real.rpow_natCast u 2)
  rw [hpow] at hc
  have hm := mellin_comp_rpow f s (2 : Real)
  rw [hpow] at hm
  have he : mellin baseProfile s = baseMultiplier s := by
    change mellin (fun u : Real => f (u ^ 2)) s = _
    simpa only [Complex.ofReal_ofNat,
      abs_of_pos (by norm_num : (0 : Real) < 2), hfm, baseMultiplier] using hm
  exact And.intro hc he

theorem primeProfile_eq_scaled (u : Real) :
    primeProfile u = Finset.univ.sum (fun i : Fin 4 =>
      coefficients i * baseProfile (radii i * u)) := by
  unfold primeProfile carrierProfile
  apply Finset.sum_congr rfl
  intro i hi
  have hr : paperConstant * (radii i * u) ^ 2 =
      (paperConstant * scales i) * u ^ 2 := by
    rw [<- radii_sq i]
    ring
  have he := congrArg (fun x : Real => (x : Complex)) hr
  push_cast at he
  unfold baseProfile expWindow
  congr 2
  push_cast
  linear_combination he

theorem primeProfile_hasMellin (s : Complex) (hs : 0 < s.re) :
    HasMellin primeProfile s (baseMultiplier s * scaleMultiplier s) := by
  classical
  have hbase := baseProfile_hasMellin s hs
  have hk (i : Fin 4) :
      HasMellin (fun u : Real => coefficients i * baseProfile (radii i * u)) s
        (coefficients i * ((radii i : Complex) ^ (-s) * baseMultiplier s)) := by
    have hc : MellinConvergent (fun u : Real => baseProfile (radii i * u)) s :=
      (MellinConvergent.comp_mul_left (radii_pos i)).2 hbase.1
    have hm := mellin_comp_mul_left baseProfile s (radii_pos i)
    rw [hbase.2] at hm
    have h := hasMellin_const_smul hc (coefficients i)
    simpa only [smul_eq_mul, hm] using h
  have h0 := hk 0
  have h1 := hk 1
  have h2 := hk 2
  have h3 := hk 3
  have h01 := hasMellin_add h0.1 h1.1
  rw [h0.2, h1.2] at h01
  have h012 := hasMellin_add h01.1 h2.1
  rw [h01.2, h2.2] at h012
  have h0123 := hasMellin_add h012.1 h3.1
  rw [h012.2, h3.2] at h0123
  have hf : (fun u : Real =>
      ((coefficients 0 * baseProfile (radii 0 * u) +
        coefficients 1 * baseProfile (radii 1 * u)) +
        coefficients 2 * baseProfile (radii 2 * u)) +
        coefficients 3 * baseProfile (radii 3 * u)) = primeProfile := by
    funext u
    rw [primeProfile_eq_scaled]
    norm_num [Fin.sum_univ_succ] <;> ring
  have hv :
      ((coefficients 0 * ((radii 0 : Complex) ^ (-s) * baseMultiplier s) +
        coefficients 1 * ((radii 1 : Complex) ^ (-s) * baseMultiplier s)) +
        coefficients 2 * ((radii 2 : Complex) ^ (-s) * baseMultiplier s)) +
        coefficients 3 * ((radii 3 : Complex) ^ (-s) * baseMultiplier s) =
      baseMultiplier s * scaleMultiplier s := by
    norm_num [scaleMultiplier, Fin.sum_univ_succ] <;> ring
  rw [hf, hv] at h0123
  exact h0123

end PrimeFactorOscillations.CubicReciprocalMellin

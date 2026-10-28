/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.CubicCarrierMellin
/-!
# Holomorphy of the reciprocal Gaussian carrier multiplier

Proves that the exact convergent Mellin multiplier is analytic on the
positive half-plane. Its use in a conductor average still requires the
same-variable signal transfer; no signed arithmetic estimate is asserted.
-/

set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace PrimeFactorOscillations.CubicCarrierAnalytic
open OAI OAI.SevenEighths
open CubicReciprocalGaussian CubicReciprocalMellin CubicCarrierMellin

theorem const_cpow_analyticAt (a : Complex) (ha : Not (a = 0))
    (g : Complex -> Complex) (s : Complex) (hg : AnalyticAt Complex g s) :
    AnalyticAt Complex (fun z => a ^ g z) s := by
  have he : (fun z => a ^ g z) = (fun z => Complex.exp (Complex.log a * g z)) := by
    funext z
    exact Complex.cpow_def_of_ne_zero ha (g z)
  rw [he]
  exact (analyticAt_const.mul hg).cexp

theorem gamma_analyticAt_of_re_pos (s : Complex) (hs : 0 < s.re) :
    AnalyticAt Complex Complex.Gamma s := by
  have hd : DifferentiableOn Complex Complex.Gamma {z : Complex | 0 < z.re} := by
    intro z hz
    exact (OAI.CubicReflectionKernel.Gamma_differentiableAt_of_re_pos z hz).differentiableWithinAt
  have ho : IsOpen {z : Complex | 0 < z.re} := isOpen_lt continuous_const Complex.continuous_re
  exact hd.analyticOnNhd ho s hs

theorem baseMultiplier_analyticAt (s : Complex) (hs : 0 < s.re) :
    AnalyticAt Complex baseMultiplier s := by
  have hhalf : AnalyticAt Complex (fun z : Complex => z / 2) s :=
    analyticAt_id.div_const
  have hs2 : 0 < (s / 2).re := by
    simp only [Complex.div_ofNat_re]
    linarith
  have ha : Not ((ProbeRadialMellin.paperConstant : Complex) = 0) := by
    exact_mod_cast ne_of_gt ProbeRadialMellin.paperConstant_pos
  have hp := const_cpow_analyticAt (ProbeRadialMellin.paperConstant : Complex) ha
    (fun z => -(z / 2)) s hhalf.neg
  have hg := (gamma_analyticAt_of_re_pos (s / 2) hs2).comp
    (f := fun z : Complex => z / 2) hhalf
  have hc : AnalyticAt Complex
      (fun _ : Complex => ((Inv.inv (2 : Real)) : Complex)) s := analyticAt_const
  have hprod : AnalyticAt Complex
      (fun z : Complex => (ProbeRadialMellin.paperConstant : Complex) ^ (-(z / 2)) *
        Complex.Gamma (z / 2)) s := hp.mul hg
  have hout : AnalyticAt Complex
      (fun z : Complex => ((Inv.inv (2 : Real)) : Complex) *
        ((ProbeRadialMellin.paperConstant : Complex) ^ (-(z / 2)) *
          Complex.Gamma (z / 2))) s := hc.mul hprod
  convert hout using 1
  funext z
  simp only [baseMultiplier, Complex.real_smul, Complex.ofReal_inv]

theorem scaleMultiplier_analyticAt (s : Complex) :
    AnalyticAt Complex scaleMultiplier s := by
  have hi (i : Fin 4) : AnalyticAt Complex
      (fun z => coefficients i * (radii i : Complex) ^ (-z)) s := by
    have hn : Not ((radii i : Complex) = 0) := by
      exact_mod_cast ne_of_gt (radii_pos i)
    exact analyticAt_const.mul
      (const_cpow_analyticAt _ hn (fun z : Complex => -z) s analyticAt_id.neg)
  have ht := ((hi 0).add (hi 1)).add (hi 2)
  have hsum := ht.add (hi 3)
  convert hsum using 1
  funext z
  norm_num [scaleMultiplier, Fin.sum_univ_succ]
  ring

theorem carrierMultiplier_analyticAt (s : Complex) (hs : 0 < s.re) :
    AnalyticAt Complex carrierMultiplier s := by
  have hs2 : 0 < (2 * s).re := by
    simp only [Complex.mul_re]
    norm_num
    linarith
  have hi : AnalyticAt Complex (fun z : Complex => 2 * z) s :=
    analyticAt_const.mul analyticAt_id
  have hb := (baseMultiplier_analyticAt (2 * s) hs2).comp hi
  have hc := (scaleMultiplier_analyticAt (2 * s)).comp hi
  exact analyticAt_const.mul (hb.mul hc)

end PrimeFactorOscillations.CubicCarrierAnalytic

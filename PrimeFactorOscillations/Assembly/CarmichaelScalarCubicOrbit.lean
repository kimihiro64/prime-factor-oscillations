/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/

import PrimeFactorOscillations.Assembly.CarmichaelTwoPowerMultiplicity
import PrimeFactorOscillations.Helpers.QRHSevenEighths
import PrimeFactorOscillations.Mathlib.Analysis.Complex.AnchoredScalarMultiplicity

/-!
# Scalar-only cubic-orbit recovery of actual zeta multiplicities

Only the real parts of two cubic residue limits are observed. The installed
unconditional seven-eighths theorem anchors the ninth-power reference.
No RH or multiplicity cap is assumed. Observation error remains explicit.
-/

set_option autoImplicit false
set_option Elab.async false

noncomputable section

namespace PrimeFactorOscillations.CarmichaelWeightedSignal

open DirichletCompensatedProbe

def cubicScalarCoefficient (rho : Complex) : Real :=
  ((3 : Complex) * rho / (rho + 2)).re

private theorem cubic_point_strip (rho : Complex) (hRe : And (0 < rho.re) (rho.re < 1)) :
    And (0 < (powerMap 3 rho).re) ((powerMap 3 rho).re < 1) := by
  have h := powerMap_real_identity 3 (by norm_num) rho
  exact And.intro (by linarith [hRe.1]) (by linarith [hRe.2])

private theorem cubic_point_im (rho : Complex) (hIm : Not (rho.im = 0)) :
    Not ((powerMap 3 rho).im = 0) := by
  have h := powerMap_im_identity 3 (by norm_num) rho
  intro he
  rw [he, zero_mul] at h
  exact hIm h.symm

private theorem cubic_twice_re (rho : Complex) (hRe : 0 < rho.re) :
    (7 / 8 : Real) < (powerMap 3 (powerMap 3 rho)).re := by
  have he : powerMap 3 (powerMap 3 rho) = powerMap 9 rho := by
    norm_num [powerMap] <;> ring
  rw [he]
  have h := powerMap_real_identity 9 (by norm_num) rho
  linarith

theorem zeta_cubic_orbit_terminal_order (rho : Complex) (hRe : 0 < rho.re) :
    analyticOrderNatAt riemannZeta (powerMap 3 (powerMap 3 rho)) = 0 := by
  have hNZ := QRH.zeta_ne_zero (powerMap 3 (powerMap 3 rho)) (cubic_twice_re rho hRe)
  have hOrd : analyticOrderAt riemannZeta (powerMap 3 (powerMap 3 rho)) = 0 :=
    analyticOrderAt_eq_zero.mpr (Or.inr hNZ)
  change (analyticOrderAt riemannZeta (powerMap 3 (powerMap 3 rho))).toNat = 0
  rw [hOrd]
  rfl

theorem zeta_cubic_orbit_scalar_values (rho : Complex) (hRe : 0 < rho.re) :
    And ((zetaCanonicalPowerResidue 3 rho).re =
      Complex.anchoredScalarFirst (cubicScalarCoefficient rho)
        (analyticOrderNatAt riemannZeta rho : Int)
        (analyticOrderNatAt riemannZeta (powerMap 3 rho) : Int))
      ((zetaCanonicalPowerResidue 3 (powerMap 3 rho)).re =
        -(analyticOrderNatAt riemannZeta (powerMap 3 rho) : Real)) := by
  refine And.intro ?_ ?_
  . have hCode := zetaCanonicalPowerResidue_eq_integerCode (3 : Nat) rho
    norm_num only [Nat.cast_ofNat] at hCode
    rw [hCode]
    have he : rho + (3 : Complex) - 1 = rho + 2 := by ring
    simpa only [cubicScalarCoefficient, Nat.cast_ofNat, he] using
      Complex.integerResidueCode_re_scalar 3 rho
        (analyticOrderNatAt riemannZeta rho : Int)
        (analyticOrderNatAt riemannZeta (powerMap 3 rho) : Int)
  . have ht := zeta_cubic_orbit_terminal_order rho hRe
    simp [zetaCanonicalPowerResidue, ht]

theorem zeta_cubic_orbit_real_limits
    (G : Complex -> Complex)
    (hG : AnalyticOnNhd Complex G {s : Complex | And (0 < s.re) (s.re < 1)})
    (rho : Complex) (hRe : And (0 < rho.re) (rho.re < 1)) (hIm : Not (rho.im = 0)) :
    And (Filter.Tendsto
      (fun s => ((s - rho) * affinePowerReadout (zetaMultiplicityReadout G) 3 s).re)
      (nhdsWithin rho (Set.compl {rho}))
      (nhds (Complex.anchoredScalarFirst (cubicScalarCoefficient rho)
        (analyticOrderNatAt riemannZeta rho : Int)
        (analyticOrderNatAt riemannZeta (powerMap 3 rho) : Int))))
      (Filter.Tendsto
        (fun s => ((s - powerMap 3 rho) * affinePowerReadout (zetaMultiplicityReadout G) 3 s).re)
        (nhdsWithin (powerMap 3 rho) (Set.compl {powerMap 3 rho}))
        (nhds (-(analyticOrderNatAt riemannZeta (powerMap 3 rho) : Real)))) := by
  have hValues := zeta_cubic_orbit_scalar_values rho hRe.1
  have h0 := zeta_power_readout_scaled_limit G hG 3 (by norm_num) rho hRe hIm
  have h1 := zeta_power_readout_scaled_limit G hG 3 (by norm_num) (powerMap 3 rho)
    (cubic_point_strip rho hRe) (cubic_point_im rho hIm)
  refine And.intro ?_ ?_
  . have hh := (Complex.continuous_re.tendsto _).comp h0
    have he : Function.comp Complex.re
        (fun s : Complex => (s - rho) * affinePowerReadout (zetaMultiplicityReadout G) 3 s) =
        (fun s : Complex => ((s - rho) * affinePowerReadout (zetaMultiplicityReadout G) 3 s).re) := by
      funext s
      exact Function.comp_apply
    rw [he] at hh
    simpa only [hValues.1] using hh
  . have hh := (Complex.continuous_re.tendsto _).comp h1
    have he : Function.comp Complex.re
        (fun s : Complex => (s - powerMap 3 rho) * affinePowerReadout (zetaMultiplicityReadout G) 3 s) =
        (fun s : Complex => ((s - powerMap 3 rho) * affinePowerReadout (zetaMultiplicityReadout G) 3 s).re) := by
      funext s
      exact Function.comp_apply
    rw [he] at hh
    simpa only [hValues.2] using hh

theorem zeta_cubic_orbit_scalar_decode (rho : Complex) (hRe : 0 < rho.re) (y0 y1 : Real)
    (h0 : abs ((zetaCanonicalPowerResidue 3 rho).re - y0) < 1 / 2)
    (h1 : abs ((zetaCanonicalPowerResidue 3 (powerMap 3 rho)).re - y1) < 1 / 2) :
    Complex.anchoredScalarDecode (cubicScalarCoefficient rho) y0 y1 =
      Prod.mk (analyticOrderNatAt riemannZeta rho : Int)
        (analyticOrderNatAt riemannZeta (powerMap 3 rho) : Int) := by
  have hValues := zeta_cubic_orbit_scalar_values rho hRe
  rw [hValues.1] at h0
  rw [hValues.2] at h1
  apply Complex.anchoredScalar_decode (cubicScalarCoefficient rho) y0 y1
    (analyticOrderNatAt riemannZeta rho : Int)
    (analyticOrderNatAt riemannZeta (powerMap 3 rho) : Int) h0
  simpa using h1

theorem zeta_cubic_orbit_negative_signal (rho : Complex) (hRe : 0 < rho.re)
    (hMass : 1 <= analyticOrderNatAt riemannZeta rho +
      analyticOrderNatAt riemannZeta (powerMap 3 rho)) :
    min (zetaCanonicalPowerResidue 3 rho).re
      (zetaCanonicalPowerResidue 3 (powerMap 3 rho)).re <= -1 := by
  have hValues := zeta_cubic_orbit_scalar_values rho hRe
  rw [hValues.1, hValues.2]
  exact Complex.anchoredScalar_negative_signal (cubicScalarCoefficient rho)
    (analyticOrderNatAt riemannZeta rho)
    (analyticOrderNatAt riemannZeta (powerMap 3 rho)) hMass

end PrimeFactorOscillations.CarmichaelWeightedSignal

end

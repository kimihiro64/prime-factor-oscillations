/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/

import PrimeFactorOscillations.Assembly.CarmichaelDirichletResidues
import PrimeFactorOscillations.Assembly.CarmichaelScalarCubicOrbit

/-!
# All-character scalar cubic-orbit recovery, including the real axis

The actual residue limits give (-A+t*B,-B), uniformly in conductor and height.
Only the terminal ninth-power point uses the installed unconditional QRH
provider. A half-unit observation tolerance recovers both orders and gives
a coefficient-free Boolean test for a zero at either observed orbit point.
This is recovery, not a new zero-free boundary or a sampling-error estimate.
-/

set_option autoImplicit false
set_option Elab.async false

noncomputable section

namespace PrimeFactorOscillations.CarmichaelWeightedSignal

open DirichletCompensatedProbe

private theorem dirichlet_strip_ne_one (rho : Complex) (hRe : rho.re < 1) :
    Not (rho = 1) := by
  intro he
  have hh := congrArg Complex.re he
  change rho.re = 1 at hh
  linarith

private theorem dirichlet_cubic_point_strip (rho : Complex)
    (hRe : And (0 < rho.re) (rho.re < 1)) :
    And (0 < (powerMap 3 rho).re) ((powerMap 3 rho).re < 1) := by
  have h := powerMap_real_identity 3 (by norm_num) rho
  exact And.intro (by linarith [hRe.1]) (by linarith [hRe.2])

theorem dirichlet_cubic_orbit_terminal_order {q : Nat} [NeZero q]
    (chi : DirichletCharacter Complex q) (rho : Complex)
    (hRe : And (0 < rho.re) (rho.re < 1)) :
    analyticOrderNatAt (DirichletCharacter.LFunction chi)
      (powerMap 3 (powerMap 3 rho)) = 0 := by
  have h0 := powerMap_real_identity 3 (by norm_num) rho
  have h1 := powerMap_real_identity 3 (by norm_num) (powerMap 3 rho)
  have hBound : (7 / 8 : Real) < (powerMap 3 (powerMap 3 rho)).re := by
    linarith [hRe.1]
  have hUpper : (powerMap 3 (powerMap 3 rho)).re < 1 := by
    linarith [hRe.2]
  have hNZ := QRH.dirichletL_ne_zero q chi (powerMap 3 (powerMap 3 rho)) hBound
    (by intro hPole; exact dirichlet_strip_ne_one _ hUpper hPole.2)
  have hOrd : analyticOrderAt (DirichletCharacter.LFunction chi)
      (powerMap 3 (powerMap 3 rho)) = 0 :=
    analyticOrderAt_eq_zero.mpr (Or.inr hNZ)
  change (analyticOrderAt (DirichletCharacter.LFunction chi)
    (powerMap 3 (powerMap 3 rho))).toNat = 0
  rw [hOrd]
  rfl

theorem dirichlet_cubic_orbit_scalar_values {q : Nat} [NeZero q]
    (chi : DirichletCharacter Complex q) (rho : Complex)
    (hRe : And (0 < rho.re) (rho.re < 1)) :
    And ((dirichletCanonicalPowerResidue chi 3 rho).re =
      Complex.anchoredScalarFirst (cubicScalarCoefficient rho)
        (analyticOrderNatAt (DirichletCharacter.LFunction chi) rho : Int)
        (analyticOrderNatAt (DirichletCharacter.LFunction chi) (powerMap 3 rho) : Int))
      ((dirichletCanonicalPowerResidue chi 3 (powerMap 3 rho)).re =
        -(analyticOrderNatAt (DirichletCharacter.LFunction chi) (powerMap 3 rho) : Real)) := by
  constructor
  . have he : dirichletCanonicalPowerResidue chi 3 rho =
        Complex.integerResidueCode 3 rho
          (analyticOrderNatAt (DirichletCharacter.LFunction chi) rho : Int)
          (analyticOrderNatAt (DirichletCharacter.LFunction chi) (powerMap 3 rho) : Int) := by
      simp [dirichletCanonicalPowerResidue, Complex.integerResidueCode]
    rw [he]
    have hden : rho + (3 : Complex) - 1 = rho + 2 := by ring
    simpa only [cubicScalarCoefficient, Nat.cast_ofNat, hden] using
      Complex.integerResidueCode_re_scalar 3 rho
        (analyticOrderNatAt (DirichletCharacter.LFunction chi) rho : Int)
        (analyticOrderNatAt (DirichletCharacter.LFunction chi) (powerMap 3 rho) : Int)
  . have ht := dirichlet_cubic_orbit_terminal_order chi rho hRe
    simp [dirichletCanonicalPowerResidue, ht]

theorem dirichlet_cubic_orbit_real_limits {q : Nat} [NeZero q]
    (chi : DirichletCharacter Complex q) (G : Complex -> Complex)
    (hG : AnalyticOnNhd Complex G {s : Complex | And (0 < s.re) (s.re < 1)})
    (rho : Complex) (hRe : And (0 < rho.re) (rho.re < 1)) :
    And (Filter.Tendsto
      (fun s => ((s - rho) * affinePowerReadout (DirichletZeroReadout.readout chi G) 3 s).re)
      (nhdsWithin rho (Set.compl {rho}))
      (nhds (Complex.anchoredScalarFirst (cubicScalarCoefficient rho)
        (analyticOrderNatAt (DirichletCharacter.LFunction chi) rho : Int)
        (analyticOrderNatAt (DirichletCharacter.LFunction chi) (powerMap 3 rho) : Int))))
      (Filter.Tendsto
        (fun s => ((s - powerMap 3 rho) *
          affinePowerReadout (DirichletZeroReadout.readout chi G) 3 s).re)
        (nhdsWithin (powerMap 3 rho) (Set.compl {powerMap 3 rho}))
        (nhds (-(analyticOrderNatAt (DirichletCharacter.LFunction chi) (powerMap 3 rho) : Real)))) := by
  have hValues := dirichlet_cubic_orbit_scalar_values chi rho hRe
  have h0 := dirichlet_power_readout_scaled_limit chi G hG 3 (by norm_num) rho hRe
  have h1 := dirichlet_power_readout_scaled_limit chi G hG 3 (by norm_num) (powerMap 3 rho)
    (dirichlet_cubic_point_strip rho hRe)
  constructor
  . have hh := (Complex.continuous_re.tendsto _).comp h0
    have he : Function.comp Complex.re
        (fun s : Complex => (s - rho) * affinePowerReadout (DirichletZeroReadout.readout chi G) 3 s) =
        (fun s : Complex => ((s - rho) * affinePowerReadout (DirichletZeroReadout.readout chi G) 3 s).re) := by
      funext s
      exact Function.comp_apply
    rw [he] at hh
    simpa only [hValues.1] using hh
  . have hh := (Complex.continuous_re.tendsto _).comp h1
    have he : Function.comp Complex.re
        (fun s : Complex => (s - powerMap 3 rho) *
          affinePowerReadout (DirichletZeroReadout.readout chi G) 3 s) =
        (fun s : Complex => ((s - powerMap 3 rho) *
          affinePowerReadout (DirichletZeroReadout.readout chi G) 3 s).re) := by
      funext s
      exact Function.comp_apply
    rw [he] at hh
    simpa only [hValues.2] using hh

theorem dirichlet_cubic_orbit_scalar_decode {q : Nat} [NeZero q]
    (chi : DirichletCharacter Complex q) (rho : Complex)
    (hRe : And (0 < rho.re) (rho.re < 1)) (y0 y1 : Real)
    (h0 : abs ((dirichletCanonicalPowerResidue chi 3 rho).re - y0) < 1 / 2)
    (h1 : abs ((dirichletCanonicalPowerResidue chi 3 (powerMap 3 rho)).re - y1) < 1 / 2) :
    Complex.anchoredScalarDecode (cubicScalarCoefficient rho) y0 y1 =
      Prod.mk (analyticOrderNatAt (DirichletCharacter.LFunction chi) rho : Int)
        (analyticOrderNatAt (DirichletCharacter.LFunction chi) (powerMap 3 rho) : Int) := by
  have hValues := dirichlet_cubic_orbit_scalar_values chi rho hRe
  rw [hValues.1] at h0
  rw [hValues.2] at h1
  apply Complex.anchoredScalar_decode (cubicScalarCoefficient rho) y0 y1
    (analyticOrderNatAt (DirichletCharacter.LFunction chi) rho : Int)
    (analyticOrderNatAt (DirichletCharacter.LFunction chi) (powerMap 3 rho) : Int) h0
  simpa using h1

theorem dirichlet_cubic_orbit_zero_signal {q : Nat} [NeZero q]
    (chi : DirichletCharacter Complex q) (rho : Complex)
    (hRe : And (0 < rho.re) (rho.re < 1)) :
    (DirichletCharacter.LFunction chi rho = 0 \/
      DirichletCharacter.LFunction chi (powerMap 3 rho) = 0) <->
    min (dirichletCanonicalPowerResidue chi 3 rho).re
      (dirichletCanonicalPowerResidue chi 3 (powerMap 3 rho)).re <= -1 := by
  have hValues := dirichlet_cubic_orbit_scalar_values chi rho hRe
  have hA := LFunction_order_pos_iff_zero chi rho (dirichlet_strip_ne_one rho hRe.2)
  have hB := LFunction_order_pos_iff_zero chi (powerMap 3 rho)
    (dirichlet_strip_ne_one _ (dirichlet_cubic_point_strip rho hRe).2)
  constructor
  . intro hz
    have hMass : 1 <= analyticOrderNatAt (DirichletCharacter.LFunction chi) rho +
        analyticOrderNatAt (DirichletCharacter.LFunction chi) (powerMap 3 rho) := by
      cases hz with
      | inl ha => have hp := hA.mpr ha; omega
      | inr hb => have hp := hB.mpr hb; omega
    rw [hValues.1, hValues.2]
    exact Complex.anchoredScalar_negative_signal (cubicScalarCoefficient rho)
      (analyticOrderNatAt (DirichletCharacter.LFunction chi) rho)
      (analyticOrderNatAt (DirichletCharacter.LFunction chi) (powerMap 3 rho)) hMass
  . intro hSignal
    by_contra hz
    have ha : analyticOrderNatAt (DirichletCharacter.LFunction chi) rho = 0 := by
      by_contra hn
      exact hz (Or.inl (hA.mp (Nat.pos_of_ne_zero hn)))
    have hb : analyticOrderNatAt (DirichletCharacter.LFunction chi) (powerMap 3 rho) = 0 := by
      by_contra hn
      exact hz (Or.inr (hB.mp (Nat.pos_of_ne_zero hn)))
    rw [hValues.1, hValues.2] at hSignal
    norm_num [Complex.anchoredScalarFirst, ha, hb] at hSignal

theorem dirichlet_cubic_orbit_noisy_zero_iff {q : Nat} [NeZero q]
    (chi : DirichletCharacter Complex q) (rho : Complex)
    (hRe : And (0 < rho.re) (rho.re < 1)) (y0 y1 : Real)
    (h0 : abs ((dirichletCanonicalPowerResidue chi 3 rho).re - y0) < 1 / 2)
    (h1 : abs ((dirichletCanonicalPowerResidue chi 3 (powerMap 3 rho)).re - y1) < 1 / 2) :
    (DirichletCharacter.LFunction chi rho = 0 \/
      DirichletCharacter.LFunction chi (powerMap 3 rho) = 0) <-> min y0 y1 < -1 / 2 := by
  have hZero := dirichlet_cubic_orbit_zero_signal chi rho hRe
  constructor
  . intro hz
    have hs := hZero.mp hz
    have hh0 := (abs_lt.mp h0).1
    have hh1 := (abs_lt.mp h1).1
    by_contra hn
    have hm : -1 / 2 <= min y0 y1 := le_of_not_gt hn
    have hy0 := le_trans hm (min_le_left y0 y1)
    have hy1 := le_trans hm (min_le_right y0 y1)
    have hr0 : -1 < (dirichletCanonicalPowerResidue chi 3 rho).re := by linarith
    have hr1 : -1 < (dirichletCanonicalPowerResidue chi 3 (powerMap 3 rho)).re := by linarith
    have hm' := lt_min hr0 hr1
    linarith
  . intro hy
    by_contra hz
    have hValues := dirichlet_cubic_orbit_scalar_values chi rho hRe
    have ha : analyticOrderNatAt (DirichletCharacter.LFunction chi) rho = 0 := by
      by_contra hn
      exact hz (Or.inl ((LFunction_order_pos_iff_zero chi rho
        (dirichlet_strip_ne_one rho hRe.2)).mp (Nat.pos_of_ne_zero hn)))
    have hb : analyticOrderNatAt (DirichletCharacter.LFunction chi) (powerMap 3 rho) = 0 := by
      by_contra hn
      exact hz (Or.inr ((LFunction_order_pos_iff_zero chi (powerMap 3 rho)
        (dirichlet_strip_ne_one _ (dirichlet_cubic_point_strip rho hRe).2)).mp
          (Nat.pos_of_ne_zero hn)))
    rw [hValues.1] at h0
    rw [hValues.2] at h1
    simp only [ha, hb, Complex.anchoredScalarFirst, Nat.cast_zero, Int.cast_zero,
      neg_zero, mul_zero, zero_add, zero_sub, abs_neg] at h0 h1
    have hy0 : -1 / 2 < y0 := by linarith [(abs_lt.mp h0).1]
    have hy1 : -1 / 2 < y1 := by linarith [(abs_lt.mp h1).1]
    have hm := lt_min hy0 hy1
    linarith

end PrimeFactorOscillations.CarmichaelWeightedSignal

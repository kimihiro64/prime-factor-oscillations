/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Assembly.CarmichaelPowerTrace
import PrimeFactorOscillations.Helpers.NicolasFiniteZeroMass
import PrimeFactorOscillations.Mathlib.Analysis.Complex.ResidueReferencePhase

/-!
# Global multiplicity profiles from critical-line phase observations

A single imaginary residue coordinate discards the target order and recovers
the shifted reference order. Varying the real degree parametrizes the full
nonreal right half-strip. The independent canonical zero trace and the
installed seven-eighths strip also give a finite-height total-order bound.
No new simplicity theorem, sampling rate, or zero-free exponent is asserted.
-/

set_option autoImplicit false
set_option Elab.async false

noncomputable section

namespace PrimeFactorOscillations.CarmichaelWeightedSignal

open DirichletCompensatedProbe

theorem powerMap_criticalPhaseAnchor (d t : Real) (hd : 0 < d) :
    powerMap d (Complex.criticalPhaseAnchor d t) =
      Complex.criticalPhaseReference d t := by
  have hr := powerMap_real_identity d hd (Complex.criticalPhaseAnchor d t)
  have hi := powerMap_im_identity d hd (Complex.criticalPhaseAnchor d t)
  have hf : (1 - 1 / (2 * d)) * d = d - 1 / 2 := by
    field_simp [hd.ne']
  apply Complex.ext
  . change (powerMap d (Complex.criticalPhaseAnchor d t)).re =
        1 - 1 / (2 * d)
    change (powerMap d (Complex.criticalPhaseAnchor d t)).re * d =
      1 / 2 + d - 1 at hr
    have he : ((powerMap d (Complex.criticalPhaseAnchor d t)).re -
        (1 - 1 / (2 * d))) * d = 0 := by nlinarith only [hr, hf]
    exact sub_eq_zero.mp ((mul_eq_zero.mp he).resolve_right hd.ne')
  . change (powerMap d (Complex.criticalPhaseAnchor d t)).im = t
    change (powerMap d (Complex.criticalPhaseAnchor d t)).im * d = d * t at hi
    have he : ((powerMap d (Complex.criticalPhaseAnchor d t)).im - t) * d = 0 := by
      nlinarith only [hi]
    exact sub_eq_zero.mp ((mul_eq_zero.mp he).resolve_right hd.ne')

def criticalPhaseMultiplicity (d t : Real) : Real :=
  Complex.residueReferencePhase d (Complex.criticalPhaseAnchor d t)
    (zetaCanonicalPowerResidue d (Complex.criticalPhaseAnchor d t))

theorem critical_phase_multiplicity (d t : Real) (hd : 1 < d)
    (ht : Not (t = 0)) :
    criticalPhaseMultiplicity d t =
      (analyticOrderNatAt riemannZeta (Complex.criticalPhaseReference d t) : Real) := by
  let z := Complex.criticalPhaseAnchor d t
  have hi : Not (z.im = 0) := mul_ne_zero (ne_of_gt (by linarith : 0 < d)) ht
  have he : zetaCanonicalPowerResidue d z =
      Complex.realPowerResidueCode d z
        (analyticOrderNatAt riemannZeta z : Int)
        (analyticOrderNatAt riemannZeta (powerMap d z) : Int) := by
    simp [zetaCanonicalPowerResidue, Complex.realPowerResidueCode]
  unfold criticalPhaseMultiplicity
  change Complex.residueReferencePhase d z (zetaCanonicalPowerResidue d z) = _
  rw [he, Complex.residueReferencePhase_code d z _ _ hd hi]
  simp only [Int.cast_natCast]
  rw [show z = Complex.criticalPhaseAnchor d t from rfl,
    powerMap_criticalPhaseAnchor d t (by linarith)]

theorem critical_phase_nonneg (d t : Real) (hd : 1 < d) (ht : Not (t = 0)) :
    0 <= criticalPhaseMultiplicity d t := by
  rw [critical_phase_multiplicity d t hd ht]
  exact Nat.cast_nonneg _

theorem critical_phase_readout_limit (G : Complex -> Complex)
    (hG : AnalyticOnNhd Complex G {s : Complex | And (0 < s.re) (s.re < 1)})
    (d t : Real) (hd : 1 < d) (ht : Not (t = 0)) :
    Filter.Tendsto
      (fun s => Complex.residueReferencePhase d (Complex.criticalPhaseAnchor d t)
        ((s - Complex.criticalPhaseAnchor d t) *
          affinePowerReadout (zetaMultiplicityReadout G) d s))
      (nhdsWithin (Complex.criticalPhaseAnchor d t)
        (Set.compl {Complex.criticalPhaseAnchor d t}))
      (nhds (analyticOrderNatAt riemannZeta (Complex.criticalPhaseReference d t) : Real)) := by
  let z := Complex.criticalPhaseAnchor d t
  have hi : Not (z.im = 0) := mul_ne_zero (ne_of_gt (by linarith : 0 < d)) ht
  have hl := zeta_power_readout_scaled_limit G hG d hd z (by
    change And ((0 : Real) < 1 / 2) ((1 / 2 : Real) < 1)
    norm_num) hi
  have hp := (Complex.continuous_im.tendsto _).comp hl
  have hn : Filter.Tendsto
      (fun s => Complex.normSq (z + (d : Complex) - 1) *
        ((s - z) * affinePowerReadout (zetaMultiplicityReadout G) d s).im)
      (nhdsWithin z (Set.compl {z}))
      (nhds (Complex.normSq (z + (d : Complex) - 1) *
        (zetaCanonicalPowerResidue d z).im)) := tendsto_const_nhds.mul hp
  have hf := hn.div_const (d * (d - 1) * z.im)
  change Filter.Tendsto
    (fun s => Complex.residueReferencePhase d z
      ((s - z) * affinePowerReadout (zetaMultiplicityReadout G) d s))
    (nhdsWithin z (Set.compl {z})) (nhds (criticalPhaseMultiplicity d t)) at hf
  rw [critical_phase_multiplicity d t hd ht] at hf
  exact hf

def NonrealRightMultiplicityCap (b : Real) (M : Nat) : Prop :=
  forall z : Complex, b < z.re -> z.re < 1 -> Not (z.im = 0) ->
    analyticOrderNatAt riemannZeta z <= M

def CriticalPhaseCap (b : Real) (M : Nat) : Prop :=
  forall d t : Real, 1 < d -> Not (t = 0) ->
    b < (Complex.criticalPhaseReference d t).re ->
      criticalPhaseMultiplicity d t <= (M : Real)

theorem critical_phase_cap_iff (b : Real) (hb : (1 / 2 : Real) <= b) (M : Nat) :
    CriticalPhaseCap b M <-> NonrealRightMultiplicityCap b M := by
  constructor
  . intro h z hbz hz1 hzi
    let d := Complex.criticalPhaseDegree z.re
    have hd : 1 < d := Complex.criticalPhaseDegree_gt_one z.re (by linarith) hz1
    have he : Complex.criticalPhaseReference d z.im = z := by
      rw [show d = Complex.criticalPhaseDegree z.re from rfl,
        Complex.criticalPhaseReference_degree z.re z.im hz1]
    have hp := h d z.im hd hzi (by rw [he]; exact hbz)
    rw [critical_phase_multiplicity d z.im hd hzi, he] at hp
    exact_mod_cast hp
  . intro h d t hd ht hbz
    rw [critical_phase_multiplicity d t hd ht]
    have hd0 : 0 < d := by linarith
    have hz1 : (Complex.criticalPhaseReference d t).re < 1 := by
      change 1 - 1 / (2 * d) < 1
      have hp : 0 < 1 / (2 * d) := div_pos (by norm_num) (by linarith)
      linarith
    have hp := h (Complex.criticalPhaseReference d t) hbz hz1 ht
    exact_mod_cast hp

theorem critical_phase_three_quarters_iff (M : Nat) :
    (forall d t : Real, 2 < d -> Not (t = 0) ->
      criticalPhaseMultiplicity d t <= (M : Real)) <->
        NonrealRightMultiplicityCap (3 / 4) M := by
  rw [<- critical_phase_cap_iff (3 / 4) (by norm_num) M]
  constructor
  . intro h d t hd ht hb
    have hd0 : 0 < d := by linarith
    have hf : (1 - 1 / (2 * d)) * (2 * d) = 2 * d - 1 := by
      field_simp [hd0.ne']
    have hp := mul_pos (sub_pos.mpr hb) (show 0 < 2 * d by linarith)
    change 0 < (1 - 1 / (2 * d) - 3 / 4) * (2 * d) at hp
    have hh : 2 < d := by nlinarith only [hp, hf]
    exact h d t hh ht
  . intro h d t hd ht
    have hd0 : 0 < d := by linarith
    have hf : (1 - 1 / (2 * d)) * (2 * d) = 2 * d - 1 := by
      field_simp [hd0.ne']
    have hb : (3 / 4 : Real) < (Complex.criticalPhaseReference d t).re := by
      by_contra hn
      have hp := mul_nonneg (sub_nonneg.mpr (le_of_not_gt hn))
        (show 0 <= 2 * d by linarith)
      change 0 <= (3 / 4 - (1 - 1 / (2 * d))) * (2 * d) at hp
      nlinarith only [hp, hf, hd]
    exact h d t (by linarith) ht hb

theorem nonreal_right_zero_cap_iff (b : Real) (hb : 0 <= b) :
    NonrealRightMultiplicityCap b 0 <->
      (forall z : Complex, b < z.re -> z.re < 1 -> Not (z.im = 0) ->
        Not (riemannZeta z = 0)) := by
  constructor
  . intro h z hbz hz1 hzi hz
    have hlo : 0 < z.re := lt_of_le_of_lt hb hbz
    have hone : Not (z = 1) := by
      intro he
      have hr := congrArg Complex.re he
      change z.re = 1 at hr
      linarith
    have hxi : Complex.riemannXi z = 0 := by
      rw [riemannXi_eq_xiZetaUnit_mul hlo hone, hz, mul_zero]
    have hm := (xiZeroMultiplicity_pos_iff z).mpr hxi
    rw [xiZeroMultiplicity_eq_zetaOrder hlo hone] at hm
    have hc := h z hbz hz1 hzi
    omega
  . intro h z hbz hz1 hzi
    have hn := h z hbz hz1 hzi
    change (analyticOrderAt riemannZeta z).toNat <= 0
    rw [analyticOrderAt_eq_zero.mpr (Or.inr hn)]
    simp

theorem critical_phase_three_quarters_subunit_iff :
    (forall d t : Real, 2 < d -> Not (t = 0) ->
      criticalPhaseMultiplicity d t < 1) <->
      (forall z : Complex, (3 / 4 : Real) < z.re -> z.re < 1 ->
        Not (z.im = 0) -> Not (riemannZeta z = 0)) := by
  constructor
  . intro h
    apply (nonreal_right_zero_cap_iff (3 / 4) (by norm_num)).mp
    apply (critical_phase_three_quarters_iff 0).mp
    intro d t hd ht
    have hp := h d t hd ht
    rw [critical_phase_multiplicity d t (by linarith) ht] at hp
    have hn : analyticOrderNatAt riemannZeta
        (Complex.criticalPhaseReference d t) < 1 := by exact_mod_cast hp
    have hz : analyticOrderNatAt riemannZeta
        (Complex.criticalPhaseReference d t) = 0 := by omega
    rw [critical_phase_multiplicity d t (by linarith) ht, hz]
  . intro h d t hd ht
    have hc := (nonreal_right_zero_cap_iff (3 / 4) (by norm_num)).mpr h
    have hp := (critical_phase_three_quarters_iff 0).mpr hc d t hd ht
    norm_num at hp
    linarith

theorem critical_phase_beyond_four (d t : Real) (hd : 4 < d)
    (ht : Not (t = 0)) : criticalPhaseMultiplicity d t = 0 := by
  rw [critical_phase_multiplicity d t (by linarith) ht]
  have hd0 : 0 < d := by linarith
  have hf : (1 - 1 / (2 * d)) * (2 * d) = 2 * d - 1 := by
    field_simp [hd0.ne']
  have hb : (7 / 8 : Real) < (Complex.criticalPhaseReference d t).re := by
    change 7 / 8 < 1 - 1 / (2 * d)
    nlinarith only [hf, hd]
  have hn := QRH.zeta_ne_zero (Complex.criticalPhaseReference d t) hb
  change ((analyticOrderAt riemannZeta
    (Complex.criticalPhaseReference d t)).toNat : Real) = 0
  rw [analyticOrderAt_eq_zero.mpr (Or.inr hn)]
  simp

end PrimeFactorOscillations.CarmichaelWeightedSignal

namespace PrimeFactorOscillations

open Complex Robin1984 PrimeClassDeletion

theorem xi_distinct_finite_count_le (S : Finset XiDistinctZero)
    (T : Real) (_hT : 0 <= T)
    (hHeight : forall z : XiDistinctZero, Membership.mem S z -> abs z.val.im <= T) :
    S.sum (fun z => (xiZeroMultiplicity z.val : Real)) <=
      (Real.eulerMascheroniConstant + 2 - Real.log (4 * Real.pi)) *
        (T ^ 2 + 43 / 64) := by
  let K := fun z : XiDistinctZero => ((z.val * (1 - z.val)) ^ (-1 : Int)).re
  have hStrip (z : XiDistinctZero) :
      And ((1 / 8 : Real) <= z.val.re) (z.val.re <= (7 / 8 : Real)) := by
    have h := xi_zero_strip_of_zeta_nonvanishing (by norm_num : (0 : Real) <= 7 / 8)
      (fun s hs _ => QRH.zeta_ne_zero s hs) z.property
    exact And.intro (by linarith [h.1]) h.2
  have hKernel (z : XiDistinctZero) : 0 <= K z :=
    Complex.inverse_product_re_nonneg z.val (by linarith [(hStrip z).1])
      (by linarith [(hStrip z).2])
  have hPoint (z : XiDistinctZero) (hz : Membership.mem S z) :
      1 <= (T ^ 2 + 43 / 64) * K z := by
    have hl := Complex.inverse_product_seven_eighths_lower z.val
      (hStrip z).1 (hStrip z).2
    have hh := abs_le.mp (hHeight z hz)
    have hp := mul_nonneg (sub_nonneg.mpr hh.2)
      (show 0 <= T + z.val.im by linarith [hh.1])
    have hsq : z.val.im ^ 2 <= T ^ 2 := by nlinarith only [hp]
    have hm := mul_le_mul_of_nonneg_right hsq (hKernel z)
    dsimp only [K] at *
    nlinarith only [hl, hm]
  have hMass : S.sum (fun z => (xiZeroMultiplicity z.val : Real) * K z) <=
      Real.eulerMascheroniConstant + 2 - Real.log (4 * Real.pi) := by
    rw [<- nicolas_distinct_product_real_hasSum.tsum_eq]
    exact nicolas_distinct_product_real_hasSum.summable.sum_le_tsum S
      (fun z _ => mul_nonneg (Nat.cast_nonneg _) (hKernel z))
  calc
    _ <= S.sum (fun z => (T ^ 2 + 43 / 64) *
        ((xiZeroMultiplicity z.val : Real) * K z)) := by
      apply Finset.sum_le_sum
      intro z hz
      have hp := mul_le_mul_of_nonneg_left (hPoint z hz)
        (show 0 <= (xiZeroMultiplicity z.val : Real) from Nat.cast_nonneg _)
      nlinarith only [hp]
    _ = (T ^ 2 + 43 / 64) *
        S.sum (fun z => (xiZeroMultiplicity z.val : Real) * K z) := by
      rw [Finset.mul_sum]
    _ <= (T ^ 2 + 43 / 64) *
        (Real.eulerMascheroniConstant + 2 - Real.log (4 * Real.pi)) :=
      mul_le_mul_of_nonneg_left hMass (by positivity)
    _ = _ := by ring

theorem xi_distinct_finite_count_one_twentieth (S : Finset XiDistinctZero)
    (T : Real) (hT : 0 <= T)
    (hHeight : forall z : XiDistinctZero, Membership.mem S z -> abs z.val.im <= T) :
    S.sum (fun z => (xiZeroMultiplicity z.val : Real)) <=
      (T ^ 2 + 43 / 64) / 20 := by
  have h := xi_distinct_finite_count_le S T hT hHeight
  have hc := mul_le_mul_of_nonneg_right robin_zero_constant_le_one_twentieth
    (show 0 <= T ^ 2 + 43 / 64 by positivity)
  nlinarith only [h, hc]

end PrimeFactorOscillations

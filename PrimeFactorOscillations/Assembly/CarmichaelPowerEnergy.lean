/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Assembly.CarmichaelPowerSignal
import PrimeFactorOscillations.Helpers.ZetaPowerGeometry

/-!
# Uniform multiplicity-energy control from a real compensated residue

All original and reference multiplicities remain coupled. The functional
reflection gives the independent half-energy estimate, and an exact square
identity proves the uniform factor-twelve inverse bound without RH.
The full logarithmic-derivative readout permits any analytic correction
on the critical strip. This is a lower bound on detector response; an
independent upper estimate is still needed for a numerical multiplicity bound.
-/

set_option autoImplicit false
set_option Elab.async false

noncomputable section

namespace PrimeFactorOscillations.CarmichaelWeightedSignal

open DirichletCompensatedProbe

theorem finite_compensated_energy_lower {I : Type*} (S : Finset I)
    (a b : I -> Real)
    (hHalf : 2 * S.sum (fun i => (b i) ^ 2) <= S.sum (fun i => (a i) ^ 2)) :
    S.sum (fun i => (a i) ^ 2) / 12 <=
      S.sum (fun i => (a i - b i) ^ 2) := by
  have hp : forall i : I,
      12 * (a i - b i) ^ 2 =
        4 * (a i) ^ 2 + 2 * (2 * a i - 3 * b i) ^ 2 - 6 * (b i) ^ 2 := by
    intro i
    ring
  have hs : S.sum (fun i => 12 * (a i - b i) ^ 2) =
      S.sum (fun i => 4 * (a i) ^ 2 + 2 * (2 * a i - 3 * b i) ^ 2 -
        6 * (b i) ^ 2) := Finset.sum_congr rfl (fun i _ => hp i)
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib,
    <- Finset.mul_sum] at hs
  have hn : 0 <= S.sum (fun i => (2 * a i - 3 * b i) ^ 2) :=
    Finset.sum_nonneg (fun i _ => sq_nonneg (2 * a i - 3 * b i))
  nlinarith

def powerReferenceMass (d : Real) (rho : Complex) : Real :=
  d * (analyticOrderNatAt riemannZeta (powerMap d rho) : Real) / rho.im

private theorem powerMap_im_identity (d : Real) (hd : 0 < d) (rho : Complex) :
    (powerMap d rho).im * d = rho.im := by
  have hdC : Not ((d : Complex) = 0) := by exact_mod_cast hd.ne'
  have h : powerMap d rho * (d : Complex) = rho + (d : Complex) - 1 := by
    dsimp [powerMap]
    field_simp [hdC]
  simpa using congrArg Complex.im h

private theorem powerMap_injective (d : Real) (hd : 0 < d) :
    Function.Injective (powerMap d) := by
  have hdC : Not ((d : Complex) = 0) := by exact_mod_cast hd.ne'
  intro x y hxy
  have h := congrArg (fun z : Complex => z * (d : Complex)) hxy
  dsimp [powerMap] at h
  field_simp [hdC] at h
  linear_combination h

private theorem powerMap_window (d T : Real) (hd : 2 <= d) (rho : Complex)
    (hw : zetaZeroWindow T rho)
    (hm : 0 < analyticOrderNatAt riemannZeta (powerMap d rho)) :
    zetaZeroWindow T (powerMap d rho) /\ (1 / 2 : Real) < (powerMap d rho).re := by
  have hd0 : 0 < d := by linarith
  have hr := powerMap_real_identity d hd0 rho
  have hi := powerMap_im_identity d hd0 rho
  have hRight : (1 / 2 : Real) < (powerMap d rho).re := by
    by_contra h
    have hp := mul_nonneg (sub_nonneg.mpr (le_of_not_gt h)) hd0.le
    nlinarith [hw.2.1]
  have hUpper : (powerMap d rho).re < 1 := by
    by_contra h
    have hp := mul_nonneg (sub_nonneg.mpr (le_of_not_gt h)) hd0.le
    nlinarith [hw.2.2.1]
  have hIm : 0 < (powerMap d rho).im := by
    by_contra h
    have hp := mul_nonpos_of_nonpos_of_nonneg (le_of_not_gt h) hd0.le
    nlinarith [hw.2.2.2.1]
  have hHeight : (powerMap d rho).im <= T := by
    have hp := mul_nonneg hIm.le (show 0 <= d - 1 by linarith)
    nlinarith [hw.2.2.2.2]
  have hz : riemannZeta (powerMap d rho) = 0 :=
    apply_eq_zero_of_analyticOrderNatAt_ne_zero (Nat.ne_of_gt hm)
  exact And.intro (And.intro hz (And.intro (by linarith)
    (And.intro hUpper (And.intro hIm hHeight)))) hRight

private theorem powerReferenceMass_eq_heightMass (d : Real) (hd : 0 < d)
    (rho : Complex) (hIm : Not (rho.im = 0)) :
    powerReferenceMass d rho = zetaHeightMass (powerMap d rho) := by
  have hi := powerMap_im_identity d hd rho
  have hQne : Not ((powerMap d rho).im = 0) := by
    intro h
    rw [h, zero_mul] at hi
    exact hIm hi.symm
  unfold powerReferenceMass zetaHeightMass
  field_simp [hIm, hQne]
  linear_combination (analyticOrderNatAt riemannZeta (powerMap d rho) : Real) * hi

theorem power_reference_energy_half (d T : Real) (hd : 2 <= d) :
    2 * (upperZeroValues T).sum (fun rho => (powerReferenceMass d rho) ^ 2) <=
      (upperZeroValues T).sum (fun rho => (zetaHeightMass rho) ^ 2) := by
  classical
  let S := upperZeroValues T
  let P := S.filter (fun rho => 0 < analyticOrderNatAt riemannZeta (powerMap d rho))
  let Q := P.image (powerMap d)
  have hd0 : 0 < d := by linarith
  have hInj := powerMap_injective d hd0
  have hSubset : Q <= S.filter (fun rho => (1 / 2 : Real) < rho.re) := by
    intro rho hr
    choose tau ht he using Finset.mem_image.mp hr
    have hTau := Finset.mem_filter.mp ht
    have hw := (mem_upperZeroValues T tau).mp hTau.1
    have hq := powerMap_window d T hd tau hw hTau.2
    rw [<- he]
    exact Finset.mem_filter.mpr
      (And.intro ((mem_upperZeroValues T (powerMap d tau)).mpr hq.1) hq.2)
  have hRestrict : S.sum (fun rho => (powerReferenceMass d rho) ^ 2) =
      P.sum (fun rho => (powerReferenceMass d rho) ^ 2) := by
    dsimp only [P]
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro rho hr
    by_cases hm : 0 < analyticOrderNatAt riemannZeta (powerMap d rho)
    . simp only [if_pos hm]
    . have hn := Nat.eq_zero_of_not_pos hm
      simp [powerReferenceMass, hn, hm]
  have hImage : Q.sum (fun rho => (zetaHeightMass rho) ^ 2) =
      P.sum (fun rho => (zetaHeightMass (powerMap d rho)) ^ 2) := by
    dsimp only [Q]
    rw [Finset.sum_image (fun i _ j _ hij => hInj hij)]
  have hB : S.sum (fun rho => (powerReferenceMass d rho) ^ 2) =
      Q.sum (fun rho => (zetaHeightMass rho) ^ 2) := by
    rw [hRestrict, hImage]
    apply Finset.sum_congr rfl
    intro rho hr
    have hw := (mem_upperZeroValues T rho).mp (Finset.mem_filter.mp hr).1
    rw [powerReferenceMass_eq_heightMass d hd0 rho (ne_of_gt hw.2.2.2.1)]
  have hCompare : Q.sum (fun rho => (zetaHeightMass rho) ^ 2) <=
      (S.filter (fun rho => (1 / 2 : Real) < rho.re)).sum
        (fun rho => (zetaHeightMass rho) ^ 2) :=
    Finset.sum_le_sum_of_subset_of_nonneg hSubset
      (fun rho _ _ => sq_nonneg (zetaHeightMass rho))
  have hBound : S.sum (fun rho => (powerReferenceMass d rho) ^ 2) <=
      (S.filter (fun rho => (1 / 2 : Real) < rho.re)).sum
        (fun rho => (zetaHeightMass rho) ^ 2) := by
    rw [hB]
    exact hCompare
  exact le_trans (mul_le_mul_of_nonneg_left hBound (by norm_num))
    (zeta_right_half_energy_le T)

theorem zeta_power_multiplicity_energy_lower (d T : Real) (hd : 2 <= d) :
    (upperZeroValues T).sum (fun rho => (zetaHeightMass rho) ^ 2) / 12 <=
      (upperZeroValues T).sum
        (fun rho => (zetaHeightMass rho - powerReferenceMass d rho) ^ 2) := by
  exact finite_compensated_energy_lower (upperZeroValues T) zetaHeightMass
    (powerReferenceMass d) (power_reference_energy_half d T hd)

def zetaCanonicalPowerResidue (d : Real) (rho : Complex) : Complex :=
  -((analyticOrderNatAt riemannZeta rho : Real) : Complex) +
    (d : Complex) * rho / (rho + (d : Complex) - 1) *
      ((analyticOrderNatAt riemannZeta (powerMap d rho) : Real) : Complex)

theorem zetaCanonicalPowerResidue_projection (d : Real) (hd : 1 < d)
    (rho : Complex) (hIm : Not (rho.im = 0)) :
    (zetaCanonicalPowerResidue d rho * (rho + (d : Complex) - 1)).im /
        rho.im ^ 2 =
      powerReferenceMass d rho - zetaHeightMass rho := by
  let A : Real := (analyticOrderNatAt riemannZeta rho : Real)
  let B : Real := (analyticOrderNatAt riemannZeta (powerMap d rho) : Real)
  have hden : Not (rho + (d : Complex) - 1 = 0) := by
    intro he
    apply hIm
    simpa using congrArg Complex.im he
  have ha := power_residue_target_multiplicity d A B rho hd hIm hden
  have hb := power_residue_reference_multiplicity d A B rho hd hIm hden
  change powerTargetMultiplicity d rho (zetaCanonicalPowerResidue d rho) = A at ha
  change powerReferenceMultiplicity d rho (zetaCanonicalPowerResidue d rho) = B at hb
  unfold powerReferenceMultiplicity at hb
  rw [ha] at hb
  have hdiv := (div_eq_iff (ne_of_gt (zero_lt_one.trans hd))).mp hb
  have he : (zetaCanonicalPowerResidue d rho *
      (rho + (d : Complex) - 1)).im / rho.im = d * B - A := by
    linear_combination hdiv
  rw [pow_two, <- div_div, he]
  dsimp only [A, B, powerReferenceMass, zetaHeightMass]
  ring

theorem zeta_power_readout_energy_lower (d T : Real) (hd : 2 <= d) :
    (upperZeroValues T).sum (fun rho => (zetaHeightMass rho) ^ 2) / 12 <=
      (upperZeroValues T).sum (fun rho =>
        ((zetaCanonicalPowerResidue d rho *
          (rho + (d : Complex) - 1)).im / rho.im ^ 2) ^ 2) := by
  classical
  calc
    _ <= (upperZeroValues T).sum
        (fun rho => (zetaHeightMass rho - powerReferenceMass d rho) ^ 2) :=
      zeta_power_multiplicity_energy_lower d T hd
    _ = _ := by
      apply Finset.sum_congr rfl
      intro rho hr
      have hw := (mem_upperZeroValues T rho).mp hr
      rw [zetaCanonicalPowerResidue_projection d (by linarith) rho
        (ne_of_gt hw.2.2.2.1)]
      ring

def zetaMultiplicityReadout (G : Complex -> Complex) (s : Complex) : Complex :=
  -logDeriv riemannZeta s + G s

private theorem zeta_readout_scaled_limit (G : Complex -> Complex)
    (rho : Complex) (hOne : Not (rho = 1)) (hG : AnalyticAt Complex G rho) :
    Filter.Tendsto (fun s => (s - rho) * zetaMultiplicityReadout G s)
      (nhdsWithin rho (Set.compl {rho}))
      (nhds (-((analyticOrderNatAt riemannZeta rho : Real) : Complex))) := by
  classical
  choose n g hg hgn hEqL _hPos using
    L_factor_exists (1 : DirichletCharacter Complex 1) rho hOne
  have hEq : Filter.Eventually
      (fun s => riemannZeta s = (s - rho) ^ n * g s) (nhds rho) := by
    simpa only [DirichletCharacter.LFunction_modOne_eq] using hEqL
  have ha : AnalyticAt Complex riemannZeta rho := analyticOn_riemannZeta rho hOne
  have hOrder : analyticOrderAt riemannZeta rho = (n : ENat) := by
    apply ha.analyticOrderAt_eq_natCast.mpr
    exact Exists.intro g (And.intro hg (And.intro hgn
      (by simpa only [smul_eq_mul] using hEq)))
  have hn : analyticOrderNatAt riemannZeta rho = n := congrArg ENat.toNat hOrder
  have hW := weighted_limit (fun _ : Unit => riemannZeta)
    (fun _ : Unit => g) (fun _ : Unit => (1 : Complex)) (fun _ : Unit => n) rho
    (fun _ => hg) (fun _ => hgn) (fun _ => hEq) G hG
  simpa [readout, zetaMultiplicityReadout, <- hn] using hW

theorem zeta_power_readout_scaled_limit (G : Complex -> Complex)
    (hG : AnalyticOnNhd Complex G {s : Complex | 0 < s.re /\ s.re < 1})
    (d : Real) (hd : 1 < d) (rho : Complex)
    (hr : 0 < rho.re /\ rho.re < 1) (hIm : Not (rho.im = 0)) :
    Filter.Tendsto
      (fun s => (s - rho) * affinePowerReadout (zetaMultiplicityReadout G) d s)
      (nhdsWithin rho (Set.compl {rho}))
      (nhds (zetaCanonicalPowerResidue d rho)) := by
  have hd0 : 0 < d := zero_lt_one.trans hd
  have hRel := powerMap_real_identity d hd0 rho
  have hqr : 0 < (powerMap d rho).re /\ (powerMap d rho).re < 1 := by
    constructor
    . by_contra h
      have hp := mul_nonpos_of_nonpos_of_nonneg (le_of_not_gt h) hd0.le
      nlinarith [hr.1]
    . by_contra h
      have hp := mul_nonneg (sub_nonneg.mpr (le_of_not_gt h)) hd0.le
      nlinarith [hr.2]
  have hqi : Not ((powerMap d rho).im = 0) := by
    intro he
    have hi := powerMap_im_identity d hd0 rho
    rw [he, zero_mul] at hi
    exact hIm hi.symm
  have hOne : Not (rho = 1) := by
    intro he
    apply hIm
    rw [he, Complex.one_im]
  have hQOne : Not (powerMap d rho = 1) := by
    intro he
    apply hqi
    rw [he, Complex.one_im]
  have hden : Not (rho + (d : Complex) - 1 = 0) := by
    intro he
    apply hIm
    simpa using congrArg Complex.im he
  simpa only [zetaCanonicalPowerResidue] using
    affinePowerReadout_scaled_limit (zetaMultiplicityReadout G) d hd0 rho hden
      (analyticOrderNatAt riemannZeta rho : Real)
      (analyticOrderNatAt riemannZeta (powerMap d rho) : Real)
      (zeta_readout_scaled_limit G rho hOne (hG rho hr))
      (zeta_readout_scaled_limit G (powerMap d rho) hQOne (hG _ hqr))

theorem zeta_power_readout_residue_energy_lower
    (G : Complex -> Complex)
    (hG : AnalyticOnNhd Complex G {s : Complex | 0 < s.re /\ s.re < 1})
    (d T : Real) (hd : 2 <= d) (r : Complex -> Complex)
    (hr : forall rho : Complex, Membership.mem (upperZeroValues T) rho ->
      Filter.Tendsto
        (fun s => (s - rho) * affinePowerReadout (zetaMultiplicityReadout G) d s)
        (nhdsWithin rho (Set.compl {rho})) (nhds (r rho))) :
    (upperZeroValues T).sum (fun rho => (zetaHeightMass rho) ^ 2) / 12 <=
      (upperZeroValues T).sum (fun rho =>
        ((r rho * (rho + (d : Complex) - 1)).im / rho.im ^ 2) ^ 2) := by
  classical
  have hEq : forall rho : Complex, Membership.mem (upperZeroValues T) rho ->
      r rho = zetaCanonicalPowerResidue d rho := by
    intro rho hmem
    have hw := (mem_upperZeroValues T rho).mp hmem
    have hc := zeta_power_readout_scaled_limit G hG d (by linarith) rho
      (And.intro hw.2.1 hw.2.2.1) (ne_of_gt hw.2.2.2.1)
    haveI : Filter.NeBot (nhdsWithin rho (Set.compl {rho})) := by
      have h := PerfectSpace.univ_preperfect rho (Set.mem_univ rho)
      have he : Set.compl ({rho} : Set Complex) =
          Compl.compl ({rho} : Set Complex) := by rfl
      rw [he]
      simpa only [AccPt, Filter.principal_univ, inf_top_eq] using h
    exact tendsto_nhds_unique (hr rho hmem) hc
  calc
    _ <= (upperZeroValues T).sum (fun rho =>
        ((zetaCanonicalPowerResidue d rho *
          (rho + (d : Complex) - 1)).im / rho.im ^ 2) ^ 2) :=
      zeta_power_readout_energy_lower d T hd
    _ = _ := by
      apply Finset.sum_congr rfl
      intro rho hmem
      rw [hEq rho hmem]

end PrimeFactorOscillations.CarmichaelWeightedSignal

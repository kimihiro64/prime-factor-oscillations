/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Assembly.CarmichaelPowerEnergy

/-!
# Signed weighted multiplicity traces and surviving carriers

For every nonnegative height weight with a uniform dilation bound, reflection
controls the complete reference contribution. The resulting signed trace and
strict-sign carrier bounds apply to actual compensated logarithmic readouts.
All zero multiplicities, reference collisions and finite supports are retained.
This proves no new upper multiplicity estimate or zero-free boundary.
-/

set_option autoImplicit false
set_option Elab.async false

noncomputable section

namespace PrimeFactorOscillations.CarmichaelWeightedSignal

open DirichletCompensatedProbe

theorem zeta_right_half_weight_le (T : Real) (f : Complex -> Real)
    (hNonneg : forall rho : Complex, Membership.mem (upperZeroValues T) rho ->
      0 <= f rho)
    (hRef : forall rho : Complex, Membership.mem (upperZeroValues T) rho ->
      f (zeroReflection rho) = f rho) :
    2 * ((upperZeroValues T).filter (fun rho => (1 / 2 : Real) < rho.re)).sum f <=
      (upperZeroValues T).sum f := by
  classical
  let S := upperZeroValues T
  let R := S.filter (fun rho => (1 / 2 : Real) < rho.re)
  have hInj : Function.Injective zeroReflection := by
    intro x y hxy
    have h := congrArg zeroReflection hxy
    simpa only [zeroReflection_involutive] using h
  have hDisjoint : Disjoint R (R.image zeroReflection) := by
    apply Finset.disjoint_left.mpr
    intro rho hr hi
    choose tau ht he using Finset.mem_image.mp hi
    have hRho : (1 / 2 : Real) < rho.re := (Finset.mem_filter.mp hr).2
    have hTau : (1 / 2 : Real) < tau.re := (Finset.mem_filter.mp ht).2
    rw [<- he, zeroReflection_re] at hRho
    linarith
  have hSubset : Union.union R (R.image zeroReflection) <= S := by
    intro rho h
    apply Or.elim (Finset.mem_union.mp h)
    . intro hr
      exact (Finset.mem_filter.mp hr).1
    . intro hi
      choose tau ht he using Finset.mem_image.mp hi
      rw [<- he]
      exact reflection_mem_upperZeroValues (Finset.mem_filter.mp ht).1
  have hImageSum : (R.image zeroReflection).sum f = R.sum f := by
    rw [Finset.sum_image (fun i _ j _ hij => hInj hij)]
    apply Finset.sum_congr rfl
    intro rho hr
    exact hRef rho (Finset.mem_filter.mp hr).1
  have hSum := Finset.sum_le_sum_of_subset_of_nonneg hSubset
    (fun rho hr _ => hNonneg rho hr)
  rw [Finset.sum_union hDisjoint, hImageSum] at hSum
  change 2 * R.sum f <= S.sum f
  linarith

def zetaWeightedMultiplicity (w : Real -> Real) (rho : Complex) : Real :=
  (analyticOrderNatAt riemannZeta rho : Real) * w rho.im

def powerWeightedReference (d : Real) (w : Real -> Real)
    (rho : Complex) : Real :=
  d * (analyticOrderNatAt riemannZeta (powerMap d rho) : Real) * w rho.im

theorem zeta_weighted_right_half_le (T : Real) (w : Real -> Real)
    (hW : forall t : Real, 0 < t -> 0 <= w t) :
    2 * ((upperZeroValues T).filter (fun rho => (1 / 2 : Real) < rho.re)).sum
      (zetaWeightedMultiplicity w) <=
      (upperZeroValues T).sum (zetaWeightedMultiplicity w) := by
  apply zeta_right_half_weight_le
  . intro rho hr
    exact mul_nonneg (Nat.cast_nonneg _)
      (hW rho.im ((mem_upperZeroValues T rho).mp hr).2.2.2.1)
  . intro rho hr
    have hw := (mem_upperZeroValues T rho).mp hr
    simp only [zetaWeightedMultiplicity,
      zetaMultiplicity_reflection (And.intro hw.2.1 hw.2.2.1),
      zeroReflection_im]

theorem power_weighted_reference_half (d T c : Real) (hd : 2 <= d)
    (hc : 0 <= c) (w : Real -> Real)
    (hW : forall t : Real, 0 < t -> 0 <= w t)
    (hScale : forall t : Real, 0 < t -> d * w (d * t) <= c * w t) :
    2 * (upperZeroValues T).sum (powerWeightedReference d w) <=
      c * (upperZeroValues T).sum (zetaWeightedMultiplicity w) := by
  classical
  let S := upperZeroValues T
  let P := S.filter (fun rho => 0 < analyticOrderNatAt riemannZeta (powerMap d rho))
  let Q := P.image (powerMap d)
  let R := S.filter (fun rho => (1 / 2 : Real) < rho.re)
  have hd0 : 0 < d := by linarith
  have hInj := powerMap_injective d hd0
  have hSubset : Q <= R := by
    intro rho hr
    choose tau ht he using Finset.mem_image.mp hr
    have hTau := Finset.mem_filter.mp ht
    have hw := (mem_upperZeroValues T tau).mp hTau.1
    have hq := powerMap_window d T hd tau hw hTau.2
    rw [<- he]
    exact Finset.mem_filter.mpr
      (And.intro ((mem_upperZeroValues T (powerMap d tau)).mpr hq.1) hq.2)
  have hRestrict : S.sum (powerWeightedReference d w) =
      P.sum (powerWeightedReference d w) := by
    dsimp only [P]
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro rho hr
    by_cases hm : 0 < analyticOrderNatAt riemannZeta (powerMap d rho)
    . simp only [ite_eq_left hm]
    . have hn := Nat.eq_zero_of_not_pos hm
      simp [powerWeightedReference, hn]
  have hImage : Q.sum (zetaWeightedMultiplicity w) =
      P.sum (fun rho => zetaWeightedMultiplicity w (powerMap d rho)) := by
    dsimp only [Q]
    rw [Finset.sum_image (fun i _ j _ hij => hInj hij)]
  have hPoint : forall rho : Complex, Membership.mem P rho ->
      powerWeightedReference d w rho <=
        c * zetaWeightedMultiplicity w (powerMap d rho) := by
    intro rho hr
    have hRho := Finset.mem_filter.mp hr
    have hq := powerMap_window d T hd rho
      ((mem_upperZeroValues T rho).mp hRho.1) hRho.2
    have hs := hScale (powerMap d rho).im hq.1.2.2.2.1
    have hi : d * (powerMap d rho).im = rho.im := by
      simpa only [mul_comm] using powerMap_im_identity d hd0 rho
    rw [hi] at hs
    have hm : 0 <= (analyticOrderNatAt riemannZeta (powerMap d rho) : Real) :=
      Nat.cast_nonneg _
    have hp := mul_le_mul_of_nonneg_left hs hm
    unfold powerWeightedReference zetaWeightedMultiplicity
    nlinarith only [hp]
  have hCompare : Q.sum (zetaWeightedMultiplicity w) <=
      R.sum (zetaWeightedMultiplicity w) :=
    Finset.sum_le_sum_of_subset_of_nonneg hSubset
      (fun rho hr _ => mul_nonneg (Nat.cast_nonneg _)
        (hW rho.im ((mem_upperZeroValues T rho).mp
          (Finset.mem_filter.mp hr).1).2.2.2.1))
  have hBound : S.sum (powerWeightedReference d w) <=
      c * R.sum (zetaWeightedMultiplicity w) := by
    calc
      _ = P.sum (powerWeightedReference d w) := hRestrict
      _ <= P.sum (fun rho => c * zetaWeightedMultiplicity w (powerMap d rho)) :=
        Finset.sum_le_sum hPoint
      _ = c * Q.sum (zetaWeightedMultiplicity w) := by
        rw [hImage, Finset.mul_sum]
      _ <= c * R.sum (zetaWeightedMultiplicity w) :=
        mul_le_mul_of_nonneg_left hCompare hc
  calc
    _ <= 2 * (c * R.sum (zetaWeightedMultiplicity w)) :=
      mul_le_mul_of_nonneg_left hBound (by norm_num)
    _ = c * (2 * R.sum (zetaWeightedMultiplicity w)) := by ring
    _ <= c * S.sum (zetaWeightedMultiplicity w) :=
      mul_le_mul_of_nonneg_left (zeta_weighted_right_half_le T w hW) hc

theorem zeta_power_weighted_trace_lower (d T c : Real) (hd : 2 <= d)
    (hc : 0 <= c) (w : Real -> Real)
    (hW : forall t : Real, 0 < t -> 0 <= w t)
    (hScale : forall t : Real, 0 < t -> d * w (d * t) <= c * w t) :
    (2 - c) * (upperZeroValues T).sum (zetaWeightedMultiplicity w) <=
      2 * (upperZeroValues T).sum (fun rho =>
        zetaWeightedMultiplicity w rho - powerWeightedReference d w rho) := by
  have h := power_weighted_reference_half d T c hd hc w hW hScale
  rw [Finset.sum_sub_distrib]
  nlinarith only [h]

theorem zetaCanonicalPowerResidue_im (d : Real) (hd : 1 < d)
    (rho : Complex) (hIm : Not (rho.im = 0)) :
    (zetaCanonicalPowerResidue d rho * (rho + (d : Complex) - 1)).im =
      (d * (analyticOrderNatAt riemannZeta (powerMap d rho) : Real) -
        (analyticOrderNatAt riemannZeta rho : Real)) * rho.im := by
  have h := zetaCanonicalPowerResidue_projection d hd rho hIm
  unfold powerReferenceMass zetaHeightMass at h
  field_simp [hIm] at h
  nlinarith only [h]

theorem zetaCanonicalPowerResidue_weighted_projection (d : Real) (hd : 1 < d)
    (w : Real -> Real) (rho : Complex) (hIm : Not (rho.im = 0)) :
    zetaWeightedMultiplicity w rho - powerWeightedReference d w rho =
      -(w rho.im / rho.im *
        (zetaCanonicalPowerResidue d rho * (rho + (d : Complex) - 1)).im) := by
  rw [zetaCanonicalPowerResidue_im d hd rho hIm]
  unfold zetaWeightedMultiplicity powerWeightedReference
  field_simp [hIm]
  ring

theorem zeta_power_readout_residue_eq
    (G : Complex -> Complex)
    (hG : AnalyticOnNhd Complex G {s : Complex | 0 < s.re /\ s.re < 1})
    (d : Real) (hd : 1 < d) (rho : Complex)
    (hRe : 0 < rho.re /\ rho.re < 1) (hIm : Not (rho.im = 0))
    (r : Complex)
    (hr : Filter.Tendsto
      (fun s => (s - rho) * affinePowerReadout (zetaMultiplicityReadout G) d s)
      (nhdsWithin rho (Set.compl {rho})) (nhds r)) :
    r = zetaCanonicalPowerResidue d rho := by
  have hc := zeta_power_readout_scaled_limit G hG d hd rho hRe hIm
  haveI : Filter.NeBot (nhdsWithin rho (Set.compl {rho})) := by
    have h := PerfectSpace.univ_preperfect rho (Set.mem_univ rho)
    have he : Set.compl ({rho} : Set Complex) =
        Compl.compl ({rho} : Set Complex) := by rfl
    rw [he]
    simpa only [AccPt, Filter.principal_univ, inf_top_eq] using h
  exact tendsto_nhds_unique hr hc

theorem zeta_power_readout_weighted_trace_lower
    (G : Complex -> Complex)
    (hG : AnalyticOnNhd Complex G {s : Complex | 0 < s.re /\ s.re < 1})
    (d T c : Real) (hd : 2 <= d) (hc : 0 <= c) (w : Real -> Real)
    (hW : forall t : Real, 0 < t -> 0 <= w t)
    (hScale : forall t : Real, 0 < t -> d * w (d * t) <= c * w t)
    (r : Complex -> Complex)
    (hr : forall rho : Complex, Membership.mem (upperZeroValues T) rho ->
      Filter.Tendsto
        (fun s => (s - rho) * affinePowerReadout (zetaMultiplicityReadout G) d s)
        (nhdsWithin rho (Set.compl {rho})) (nhds (r rho))) :
    (2 - c) * (upperZeroValues T).sum (zetaWeightedMultiplicity w) <=
      -2 * (upperZeroValues T).sum (fun rho =>
        w rho.im / rho.im * (r rho * (rho + (d : Complex) - 1)).im) := by
  classical
  have hSum : (upperZeroValues T).sum (fun rho =>
      zetaWeightedMultiplicity w rho - powerWeightedReference d w rho) =
      -(upperZeroValues T).sum (fun rho =>
        w rho.im / rho.im * (r rho * (rho + (d : Complex) - 1)).im) := by
    calc
      _ = (upperZeroValues T).sum (fun rho =>
          -(w rho.im / rho.im * (r rho * (rho + (d : Complex) - 1)).im)) := by
        apply Finset.sum_congr rfl
        intro rho hmem
        have hw := (mem_upperZeroValues T rho).mp hmem
        have he := zeta_power_readout_residue_eq G hG d (by linarith) rho
          (And.intro hw.2.1 hw.2.2.1) (ne_of_gt hw.2.2.2.1) (r rho) (hr rho hmem)
        rw [he]
        exact zetaCanonicalPowerResidue_weighted_projection d (by linarith)
          w rho (ne_of_gt hw.2.2.2.1)
      _ = _ := by rw [Finset.sum_neg_distrib]
  have h := zeta_power_weighted_trace_lower d T c hd hc w hW hScale
  rw [hSum] at h
  simpa only [mul_neg, neg_mul] using h

theorem zeta_power_weak_weight_mass_upper (d T c : Real) (hd : 2 <= d)
    (hc : 0 <= c) (w : Real -> Real)
    (hW : forall t : Real, 0 < t -> 0 <= w t)
    (hScale : forall t : Real, 0 < t -> d * w (d * t) <= c * w t) :
    2 * ((upperZeroValues T).filter (fun rho =>
      (analyticOrderNatAt riemannZeta rho : Real) <=
        d * (analyticOrderNatAt riemannZeta (powerMap d rho) : Real))).sum
      (zetaWeightedMultiplicity w) <=
      c * (upperZeroValues T).sum (zetaWeightedMultiplicity w) := by
  classical
  let S := upperZeroValues T
  let B := S.filter (fun rho =>
    (analyticOrderNatAt riemannZeta rho : Real) <=
      d * (analyticOrderNatAt riemannZeta (powerMap d rho) : Real))
  have hSubset : B <= S := fun rho hr => (Finset.mem_filter.mp hr).1
  have hPoint : forall rho : Complex, Membership.mem B rho ->
      zetaWeightedMultiplicity w rho <= powerWeightedReference d w rho := by
    intro rho hr
    have h := Finset.mem_filter.mp hr
    exact mul_le_mul_of_nonneg_right h.2
      (hW rho.im ((mem_upperZeroValues T rho).mp h.1).2.2.2.1)
  have hNonneg : forall rho : Complex, Membership.mem S rho ->
      0 <= powerWeightedReference d w rho := by
    intro rho hr
    exact mul_nonneg (mul_nonneg (by linarith) (Nat.cast_nonneg _))
      (hW rho.im ((mem_upperZeroValues T rho).mp hr).2.2.2.1)
  calc
    _ <= 2 * B.sum (powerWeightedReference d w) :=
      mul_le_mul_of_nonneg_left (Finset.sum_le_sum hPoint) (by norm_num)
    _ <= 2 * S.sum (powerWeightedReference d w) :=
      mul_le_mul_of_nonneg_left
        (Finset.sum_le_sum_of_subset_of_nonneg hSubset
          (fun rho hr _ => hNonneg rho hr)) (by norm_num)
    _ <= _ := power_weighted_reference_half d T c hd hc w hW hScale

theorem zeta_power_readout_carrier_weight_lower
    (G : Complex -> Complex)
    (hG : AnalyticOnNhd Complex G {s : Complex | 0 < s.re /\ s.re < 1})
    (d T c : Real) (hd : 2 <= d) (hc : 0 <= c) (w : Real -> Real)
    (hW : forall t : Real, 0 < t -> 0 <= w t)
    (hScale : forall t : Real, 0 < t -> d * w (d * t) <= c * w t)
    (r : Complex -> Complex)
    (hr : forall rho : Complex, Membership.mem (upperZeroValues T) rho ->
      Filter.Tendsto
        (fun s => (s - rho) * affinePowerReadout (zetaMultiplicityReadout G) d s)
        (nhdsWithin rho (Set.compl {rho})) (nhds (r rho))) :
    (2 - c) * (upperZeroValues T).sum (zetaWeightedMultiplicity w) <=
      2 * ((upperZeroValues T).filter (fun rho =>
        (r rho * (rho + (d : Complex) - 1)).im < 0)).sum
        (zetaWeightedMultiplicity w) := by
  classical
  let S := upperZeroValues T
  let B := S.filter (fun rho =>
    (analyticOrderNatAt riemannZeta rho : Real) <=
      d * (analyticOrderNatAt riemannZeta (powerMap d rho) : Real))
  let C := S.filter (fun rho =>
    d * (analyticOrderNatAt riemannZeta (powerMap d rho) : Real) <
      (analyticOrderNatAt riemannZeta rho : Real))
  have hWeak : 2 * B.sum (zetaWeightedMultiplicity w) <=
      c * S.sum (zetaWeightedMultiplicity w) :=
    zeta_power_weak_weight_mass_upper d T c hd hc w hW hScale
  have hSplit : S.sum (zetaWeightedMultiplicity w) =
      B.sum (zetaWeightedMultiplicity w) + C.sum (zetaWeightedMultiplicity w) := by
    dsimp only [B, C]
    rw [Finset.sum_filter, Finset.sum_filter, <- Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro rho hmem
    by_cases h : (analyticOrderNatAt riemannZeta rho : Real) <=
        d * (analyticOrderNatAt riemannZeta (powerMap d rho) : Real)
    . simp [h, not_lt_of_ge h]
    . have ht := lt_of_not_ge h
      simp [h, ht]
  have hPred : forall rho : Complex, Membership.mem S rho ->
      ((r rho * (rho + (d : Complex) - 1)).im < 0 <->
        d * (analyticOrderNatAt riemannZeta (powerMap d rho) : Real) <
          (analyticOrderNatAt riemannZeta rho : Real)) := by
    intro rho hmem
    have hw := (mem_upperZeroValues T rho).mp hmem
    have he := zeta_power_readout_residue_eq G hG d (by linarith) rho
      (And.intro hw.2.1 hw.2.2.1) (ne_of_gt hw.2.2.2.1) (r rho) (hr rho hmem)
    rw [he, zetaCanonicalPowerResidue_im d (by linarith) rho
      (ne_of_gt hw.2.2.2.1)]
    constructor
    . intro h
      by_contra hn
      have hp := mul_nonneg (sub_nonneg.mpr (le_of_not_gt hn)) hw.2.2.2.1.le
      exact (not_le_of_gt h) hp
    . intro h
      exact mul_neg_of_neg_of_pos (sub_neg.mpr h) hw.2.2.2.1
  have hFilter : C = S.filter (fun rho =>
      (r rho * (rho + (d : Complex) - 1)).im < 0) := by
    dsimp only [C]
    apply Finset.ext
    intro rho
    simp only [Finset.mem_filter]
    constructor
    . intro h
      exact And.intro h.1 ((hPred rho h.1).mpr h.2)
    . intro h
      exact And.intro h.1 ((hPred rho h.1).mp h.2)
  have hCarrier : (2 - c) * S.sum (zetaWeightedMultiplicity w) <=
      2 * C.sum (zetaWeightedMultiplicity w) := by
    nlinarith only [hWeak, hSplit]
  rw [hFilter] at hCarrier
  exact hCarrier

theorem zeta_power_inverse_height_trace_lower (d T : Real) (hd : 2 <= d) :
    (upperZeroValues T).sum (zetaWeightedMultiplicity (fun t => 1 / t)) <=
      2 * (upperZeroValues T).sum (fun rho =>
        zetaWeightedMultiplicity (fun t => 1 / t) rho -
          powerWeightedReference d (fun t => 1 / t) rho) := by
  have hd0 : 0 < d := by linarith
  have hScale : forall t : Real, 0 < t ->
      d * (1 / (d * t)) <= 1 * (1 / t) := by
    intro t ht
    apply le_of_eq
    field_simp [hd0.ne', ht.ne']
  have h := zeta_power_weighted_trace_lower d T 1 hd (by norm_num)
    (fun t => 1 / t) (fun t ht => one_div_nonneg.mpr ht.le) hScale
  norm_num only at h
  simpa only [one_mul] using h

theorem zeta_power_inverse_square_height_trace_lower (d T : Real) (hd : 2 <= d) :
    (2 - 1 / d) *
      (upperZeroValues T).sum (zetaWeightedMultiplicity (fun t => 1 / t ^ 2)) <=
      2 * (upperZeroValues T).sum (fun rho =>
        zetaWeightedMultiplicity (fun t => 1 / t ^ 2) rho -
          powerWeightedReference d (fun t => 1 / t ^ 2) rho) := by
  have hd0 : 0 < d := by linarith
  have hScale : forall t : Real, 0 < t ->
      d * (1 / (d * t) ^ 2) <= (1 / d) * (1 / t ^ 2) := by
    intro t ht
    apply le_of_eq
    field_simp [hd0.ne', ht.ne']
  exact zeta_power_weighted_trace_lower d T (1 / d) hd
    (one_div_nonneg.mpr hd0.le) (fun t => 1 / t ^ 2)
    (fun t _ => one_div_nonneg.mpr (sq_nonneg t)) hScale


theorem zeta_power_inverse_square_height_carrier_lower
    (G : Complex -> Complex)
    (hG : AnalyticOnNhd Complex G {s : Complex | 0 < s.re /\ s.re < 1})
    (d T : Real) (hd : 2 <= d) (r : Complex -> Complex)
    (hr : forall rho : Complex, Membership.mem (upperZeroValues T) rho ->
      Filter.Tendsto
        (fun s => (s - rho) * affinePowerReadout (zetaMultiplicityReadout G) d s)
        (nhdsWithin rho (Set.compl {rho})) (nhds (r rho))) :
    (2 - 1 / d) *
      (upperZeroValues T).sum (zetaWeightedMultiplicity (fun t => 1 / t ^ 2)) <=
      2 * ((upperZeroValues T).filter (fun rho =>
        (r rho * (rho + (d : Complex) - 1)).im < 0)).sum
        (zetaWeightedMultiplicity (fun t => 1 / t ^ 2)) := by
  have hd0 : 0 < d := by linarith
  have hScale : forall t : Real, 0 < t ->
      d * (1 / (d * t) ^ 2) <= (1 / d) * (1 / t ^ 2) := by
    intro t ht
    apply le_of_eq
    field_simp [hd0.ne', ht.ne']
  exact zeta_power_readout_carrier_weight_lower G hG d T (1 / d) hd
    (one_div_nonneg.mpr hd0.le) (fun t => 1 / t ^ 2)
    (fun t _ => one_div_nonneg.mpr (sq_nonneg t)) hScale r hr

end PrimeFactorOscillations.CarmichaelWeightedSignal

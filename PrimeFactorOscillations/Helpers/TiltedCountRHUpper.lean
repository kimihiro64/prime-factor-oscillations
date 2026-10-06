/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.PrimeProfileUniformSign
import PrimeFactorOscillations.Helpers.TiltedReversalCount
import PrimeFactorOscillations.Mathlib.Algebra.Order.Floor.Interval

/-!
# Uniform RH upper comparison for prescribed local reversal counts

The rank floor(alpha L(X)) is fixed across the whole prime-prefix window
[X, 2X]. The unconditional PNT keeps the theta clocks within one unit,
and the uniform RH coefficient comparison gives one cutoff valid for all
ranks, finite selections, and tilt-grid resolutions. Dropping a failed
descent can only remove an actual prescribed witness.

This is the forward direction of the localized count criterion. It needs
no short-interval prime-pair supply. The reverse implication, and the
independent signed count bound equivalent to RH, are separate obligations.
-/

set_option autoImplicit false
set_option Elab.async false

noncomputable section

namespace PrimeFactorOscillations

open Filter PrimeFactorUnimodality

theorem eventually_theta_half_double :
    Filter.Eventually (fun x : Real => x / 2 <= Chebyshev.theta x /\
      Chebyshev.theta x <= 2 * x) atTop := by
  have hRatio : Tendsto (fun x : Real => Chebyshev.theta x / x)
      atTop (nhds (1 : Real)) := by
    exact (Asymptotics.isEquivalent_iff_tendsto_one
      (eventually_ne_atTop (0 : Real))).mp primeProfile_theta_isEquivalent_id
  have hNear := hRatio.eventually
    (Ioo_mem_nhds (by norm_num : (1 / 2 : Real) < 1) (by norm_num : (1 : Real) < 2))
  filter_upwards [hNear, eventually_gt_atTop (0 : Real)] with x hb hx
  have hCancel : (Chebyshev.theta x / x) * x = Chebyshev.theta x := by
    field_simp [hx.ne']
  have hLow := mul_le_mul_of_nonneg_right hb.1.le hx.le
  have hHigh := mul_le_mul_of_nonneg_right hb.2.le hx.le
  rw [hCancel] at hLow hHigh
  constructor <;> linarith

theorem eventually_thetaClock_dyadic_width :
    Filter.Eventually (fun x : Real => 8 <= Chebyshev.theta x /\
      forall y : Real, x <= y -> y <= 2 * x ->
        0 <= (Real.eulerMascheroniConstant +
          Real.log (Real.log (Chebyshev.theta y))) -
          (Real.eulerMascheroniConstant + Real.log (Real.log (Chebyshev.theta x))) /\
        (Real.eulerMascheroniConstant + Real.log (Real.log (Chebyshev.theta y))) -
          (Real.eulerMascheroniConstant + Real.log (Real.log (Chebyshev.theta x))) <= 1)
      atTop := by
  choose Z hZ using eventually_atTop.mp eventually_theta_half_double
  have hTheta : Tendsto Chebyshev.theta atTop atTop :=
    primeProfile_theta_isEquivalent_id.symm.tendsto_atTop tendsto_id
  filter_upwards [hTheta.eventually_ge_atTop 8,
    eventually_ge_atTop (max Z 1)] with x hEight hx
  have hxZ : Z <= x := (le_max_left Z 1).trans hx
  have hxOne : 1 <= x := (le_max_right Z 1).trans hx
  have hLow := (hZ x hxZ).1
  have hHigh := (hZ (2 * x) (by linarith)).2
  have hThetaXPos : 0 < Chebyshev.theta x := by linarith
  have hLogXPos : 0 < Real.log (Chebyshev.theta x) :=
    Real.log_pos (by linarith)
  refine And.intro hEight ?_
  intro y hxy hyx
  have hThetaLow := Chebyshev.theta_mono hxy
  have hThetaHigh := Chebyshev.theta_mono hyx
  have hThetaYPos : 0 < Chebyshev.theta y := hThetaXPos.trans_le hThetaLow
  have hLogLow := Real.log_le_log hThetaXPos hThetaLow
  have hLogYPos : 0 < Real.log (Chebyshev.theta y) := hLogXPos.trans_le hLogLow
  have hLow2 := Real.log_le_log hLogXPos hLogLow
  have hSquare : Chebyshev.theta y <= (Chebyshev.theta x) ^ 2 := by
    have hmul : 8 * Chebyshev.theta x <= (Chebyshev.theta x) ^ 2 := by
      nlinarith
    linarith
  have hLogHigh := Real.log_le_log hThetaYPos hSquare
  rw [Real.log_pow] at hLogHigh
  norm_num only [Nat.cast_ofNat] at hLogHigh
  have hHigh2 := Real.log_le_log hLogYPos hLogHigh
  rw [Real.log_mul (by norm_num : Not ((2 : Real) = 0)) hLogXPos.ne'] at hHigh2
  have hLogTwo : Real.log 2 <= (1 : Real) := by
    linarith [Real.log_le_sub_one_of_pos (by norm_num : (0 : Real) < 2)]
  constructor <;> linarith

theorem weightEsymm_positive_degree_supported (p r : Nat)
    (h : 0 < (weightEsymm (primesBelow p) r : Real)) :
    r <= (primesBelow p).length := by
  by_contra hn
  have hz : weightEsymm (primesBelow p) r = 0 := by
    unfold weightEsymm
    apply Multiset.esymm_of_card_lt
    simpa only [Multiset.coe_card, List.length_map] using Nat.lt_of_not_ge hn
  rw [hz, Rat.cast_zero] at h
  exact lt_irrefl 0 h


theorem prescribedTiltReversalCount_le_reference_of_ascent_comparison
    (H M r m : Nat) (d a : Fin m -> Nat) (U : Fin m -> Real)
    (hr : 1 <= r)
    (haSupport : forall i, r <= (primesBelow (primeAt (a i))).length)
    (hRU : forall i, (densityRatio (primesBelow (primeAt (a i))) r : Real) <= U i) :
    prescribedTiltReversalCount H M r m d a <= prescribedTiltReferenceCount H M m U a := by
  classical
  unfold prescribedTiltReversalCount prescribedTiltReferenceCount
  apply Finset.sum_le_sum
  intro i hi
  apply Finset.card_le_card
  intro j hj
  have hmem := Finset.mem_filter.mp hj
  have hAscent := hmem.2.2.2
  have hTest := (oddsTilt_rank_ascent_index_iff _ _ (a i) r hr (haSupport i)).mp hAscent
  apply Finset.mem_filter.mpr
  refine And.intro hmem.1 ?_
  have hRef := hTest.trans_le (hRU i)
  simpa only [tiltGridValue, add_assoc] using hRef

theorem eventually_prescribedTiltReversalCount_le_reference_of_RH
    (hRH : RiemannHypothesis) (alpha : Real) (ha : 0 < alpha) :
    Filter.Eventually (fun X : Real =>
      let L : Real -> Real := fun y => Real.eulerMascheroniConstant +
        Real.log (Real.log (Chebyshev.theta y))
      let r := Nat.floor (alpha * L X)
      forall H M m : Nat, forall d a : Fin m -> Nat,
        (forall i, X <= ((primeAt (a i) - 1 : Nat) : Real) /\
          ((primeAt (a i) - 1 : Nat) : Real) <= 2 * X) ->
        prescribedTiltReversalCount H M r m d a <=
          prescribedTiltReferenceCount H M m
            (fun i => Nat.factorialConvolution primeProfileRealCoefficient (r - 1)
                (L ((primeAt (a i) - 1 : Nat) : Real)) /
              Nat.factorialConvolution primeProfileRealCoefficient r
                (L ((primeAt (a i) - 1 : Nat) : Real))) a) atTop := by
  let L : Real -> Real := fun y => Real.eulerMascheroniConstant +
    Real.log (Real.log (Chebyshev.theta y))
  have hTheta : Tendsto Chebyshev.theta atTop atTop :=
    primeProfile_theta_isEquivalent_id.symm.tendsto_atTop tendsto_id
  have hClock : Tendsto L atTop atTop :=
    tendsto_const_nhds.add_atTop
      (Real.tendsto_log_atTop.comp (Real.tendsto_log_atTop.comp hTheta))
  choose Y hY using eventually_atTop.mp
    (eventually_densityRatio_thetaClock_lt_reference_uniform_of_RH hRH
      (alpha / 3) (2 * alpha) (by linarith) (by linarith))
  filter_upwards [eventually_thetaClock_dyadic_width,
    hClock.eventually_ge_atTop 2, hClock.eventually_ge_atTop (2 / alpha),
    eventually_ge_atTop Y] with X hWidth hLTwo hLarge hXY
  dsimp only
  intro H M m d a hEndpoints
  let r := Nat.floor (alpha * L X)
  have hAlphaL : 2 <= alpha * L X := by
    have hh := mul_le_mul_of_nonneg_left hLarge ha.le
    have heq : alpha * (2 / alpha) = 2 := by field_simp [ha.ne']
    rwa [heq] at hh
  have hr : 1 <= r := by
    have hRank := Nat.floor_mul_div_mem_compact_of_abs_sub_le_one
      alpha (L X) (L X) ha hLTwo hAlphaL (by simp)
    exact hRank.1
  have hPoint : forall i : Fin m,
      r <= (primesBelow (primeAt (a i))).length /\
      (densityRatio (primesBelow (primeAt (a i))) r : Real) <=
        Nat.factorialConvolution primeProfileRealCoefficient (r - 1)
          (L ((primeAt (a i) - 1 : Nat) : Real)) /
        Nat.factorialConvolution primeProfileRealCoefficient r
          (L ((primeAt (a i) - 1 : Nat) : Real)) := by
    intro i
    let y : Real := ((primeAt (a i) - 1 : Nat) : Real)
    have hyLow : X <= y := (hEndpoints i).1
    have hyHigh : y <= 2 * X := (hEndpoints i).2
    have hWidths := hWidth.2 y hyLow hyHigh
    change 0 <= L y - L X /\ L y - L X <= 1 at hWidths
    have hAbs : abs (L y - L X) <= 1 := by
      rw [abs_of_nonneg hWidths.1]
      exact hWidths.2
    have hRanks := Nat.floor_mul_div_mem_compact_of_abs_sub_le_one
      alpha (L y) (L X) ha hLTwo hAlphaL hAbs
    have hBand := hRanks.2 (L y) (And.intro (min_le_left _ _) (le_max_left _ _))
    have hCompare := (hY y (hXY.trans hyLow)).2.2 r hBand.2.1 hBand.2.2
    have hCut : Nat.floor y + 1 = primeAt (a i) := by
      dsimp [y]
      rw [Nat.floor_natCast, Nat.sub_add_cancel (prime_primeAt (a i)).one_lt.le]
    rw [hCut] at hCompare
    exact And.intro (weightEsymm_positive_degree_supported _ r hCompare.1) hCompare.2.2.le
  apply prescribedTiltReversalCount_le_reference_of_ascent_comparison
    H M r m d a _ hr (fun i => (hPoint i).1) (fun i => (hPoint i).2)

end PrimeFactorOscillations

/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import PrimeFactorOscillations.Helpers.ThresholdSelectedQuantum
import PrimeFactorOscillations.Helpers.ThresholdSelectedRotation

/-! # Complete fixed even-mass upper stability-rate classification -/

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 5000000

noncomputable section
namespace PrimeFactorOscillations

def thresholdEvenSplitError (m k : Nat) (d q : Real) : Real :=
  let v := thresholdModelHigh (2 * (m : Real)) (2 * (k : Real)) d
  abs (Finset.sum Finset.univ (fun i => 2 * (thresholdEvenSplitOrder m k i : Real) *
    abs (thresholdEvenSplitCoord m k d q i - v)) -
      thresholdTotalStatistic d v (2 * (m : Real) + 2 * (k : Real)) (2 * (k : Real))
        (fun z => abs (z - v)))

theorem thresholdEvenSplit_error_lower (m k : Nat) (d q : Real) (hk : 2 <= k)
    (hd : And (0 < d) (d < 1)) (hq : And (0 < q) (q <= 1)) (hqd : q ^ 2 < d) :
    2 * q <= thresholdEvenSplitError m k d q := by
  let v := thresholdModelHigh (2 * (m : Real)) (2 * (k : Real)) d
  let a := thresholdEvenSplitHigh m k d q
  let c := thresholdRotationCenter a q
  let R := thresholdRotationRadius a q
  let raw := Finset.sum Finset.univ (fun i => 2 * (thresholdEvenSplitOrder m k i : Real) *
    abs (thresholdEvenSplitCoord m k d q i - v)) -
      thresholdTotalStatistic d v (2 * (m : Real) + 2 * (k : Real)) (2 * (k : Real))
        (fun z => abs (z - v))
  have hkR : (2 : Real) <= (k : Real) := by exact_mod_cast hk
  have hv : 1 <= v := thresholdModelHigh_bounds _ _ d
    (mul_nonneg (by norm_num) (Nat.cast_nonneg m)) (by linarith only [hkR])
    (And.intro hd.1.le hd.2.le)
  have ha := thresholdEvenSplit_high_bounds m k d q hk hd hqd
  have hR : q / 2 <= R := thresholdRotation_radius_lower a q ha.1 (And.intro hq.1.le hq.2)
  have hRaw : raw = 2 * (m : Real) * q ^ 2 +
      2 * abs (c + R - v) + 2 * abs (c - R - v) +
      2 * ((k - 2 : Nat) : Real) * abs (a - v) := by
    dsimp only [raw]
    rw [thresholdEvenSplit_sum m k d q (fun z => abs (z - v))]
    unfold thresholdTotalStatistic
    dsimp only
    rw [show 2 * (m : Real) + 2 * (k : Real) - 2 * (k : Real) = 2 * (m : Real) by ring]
    rw [sub_self, abs_zero, mul_zero, add_zero]
    rw [abs_of_nonpos (show d - q ^ 2 - v <= 0 by nlinarith only [hv, hd.2, sq_nonneg q])]
    rw [abs_of_nonpos (show d - v <= 0 by linarith only [hv, hd.2])]
    change 2 * (m : Real) * -(d - q ^ 2 - v) +
      2 * abs (c + R - v) + 2 * abs (c - R - v) +
      2 * ((k - 2 : Nat) : Real) * abs (a - v) -
        2 * (m : Real) * -(d - v) = _
    ring
  have hA := le_abs_self (c + R - v)
  have hB := le_abs_self (v - (c - R))
  rw [abs_sub_comm v (c - R)] at hB
  have hLow : 0 <= 2 * (m : Real) * q ^ 2 :=
    mul_nonneg (mul_nonneg (by norm_num) (Nat.cast_nonneg m)) (sq_nonneg q)
  have hTail : 0 <= 2 * ((k - 2 : Nat) : Real) * abs (a - v) :=
    mul_nonneg (mul_nonneg (by norm_num) (Nat.cast_nonneg _)) (abs_nonneg _)
  have hLower : 2 * q <= raw := by
    rw [hRaw]
    linarith only [hA, hB, hLow, hTail, hR]
  exact le_trans hLower (le_abs_self raw)

theorem thresholdEvenSplit_arbitrarily_small (m k : Nat) (d eps : Real)
    (hk : 2 <= k) (hd : And (0 < d) (d < 1)) (heps : 0 < eps) :
    exists q : Real, And (0 < q)
      (And (thresholdTotalAdmissible d
        (thresholdTotalUpper d (2 * (m : Real) + 2 * (k : Real)) (2 * (k : Real)) -
          thresholdEvenSplitGap m k d q) (2 * (m : Real) + 2 * (k : Real)) (2 * (k : Real))
        (thresholdEvenSplitOrder m k) (thresholdEvenSplitCoord m k d q))
        (And (0 < thresholdEvenSplitGap m k d q)
          (And (thresholdEvenSplitGap m k d q < eps)
            (And (0 < thresholdEvenSplitError m k d q)
              (thresholdEvenSplitGap m k d q <=
                (2 * (m : Real) + 1) * (thresholdEvenSplitError m k d q) ^ 2))))) := by
  choose r hr hWindow using thresholdEvenSplit_window m k d hk hd
  let A := 8 * (m : Real) + 4
  let L := 2 * (m : Real) + 1
  have hNat : (0 : Real) <= (m : Real) := Nat.cast_nonneg m
  have hA : 0 < A := by dsimp only [A]; linarith only [hNat]
  have hL : 0 <= L := by dsimp only [L]; linarith only [hNat]
  let q := min (r / 2) (min (1 / 2) (eps / (2 * A)))
  have hq : 0 < q := lt_min (div_pos hr (by norm_num))
    (lt_min (by norm_num) (div_pos heps (mul_pos (by norm_num) hA)))
  have hqr : q <= r / 2 := min_le_left _ _
  have hqHalf : q <= 1 / 2 := le_trans (min_le_right _ _) (min_le_left _ _)
  have hqEps : q <= eps / (2 * A) := le_trans (min_le_right _ _) (min_le_right _ _)
  have hW := hWindow q (And.intro hq (by linarith only [hqr, hr]))
  have hGap := thresholdEvenSplit_gap_bounds m k d q hk hd hq hW.2.1
  have hError := thresholdEvenSplit_error_lower m k d q hk hd
    (And.intro hq hW.1.le) hW.2.1
  have hAd := thresholdEvenSplit_admissible m k d q hk hd
    (And.intro hq hW.2.1) hW.2.2.1 hW.2.2.2
  have hErrorPos : 0 < thresholdEvenSplitError m k d q := by linarith only [hError, hq]
  have hqSquare : q ^ 2 <= q := by nlinarith only [hq, hqHalf]
  have hMult := mul_le_mul_of_nonneg_left hqEps hA.le
  have hCancel : A * (eps / (2 * A)) = eps / 2 := by field_simp [hA.ne']
  rw [hCancel] at hMult
  have hScaled := mul_le_mul_of_nonneg_left hqSquare hA.le
  have hGapUpper : thresholdEvenSplitGap m k d q <= A * q ^ 2 := hGap.2
  have hSmall : thresholdEvenSplitGap m k d q < eps := by
    linarith only [hGapUpper, hMult, hScaled, heps]
  have hSquare : 4 * q ^ 2 <= (thresholdEvenSplitError m k d q) ^ 2 := by
    nlinarith only [hError, hErrorPos, hq]
  have hScale := mul_le_mul_of_nonneg_left hSquare hL
  have hLower : thresholdEvenSplitGap m k d q <=
      (2 * (m : Real) + 1) * (thresholdEvenSplitError m k d q) ^ 2 := by
    dsimp only [L] at hScale
    nlinarith only [hGap.2, hScale]
  exact Exists.intro q (And.intro hq (And.intro hAd
    (And.intro hGap.1 (And.intro hSmall (And.intro hErrorPos hLower)))))

theorem finiteEven_single_selected_diagonal {r : Nat} (d M : Real)
    (a : Fin r -> Nat) (y : Fin r -> Real) (hd : 0 < d)
    (hAd : thresholdTotalAdmissible d M 2 2 a y) :
    And (M = 2) (forall phi : Real -> Real,
      Finset.sum Finset.univ (fun i => 2 * (a i : Real) * phi (y i)) = 2 * phi 1) := by
  have hI0 : forall i : Fin r, momentRoundIndicator 0 (y i) = 1 := by
    intro i
    simp only [momentRoundIndicator, ite_eq_left (hAd.2.1 i)]
  have hZeroSelected : thresholdSelectedMass 0 Finset.univ
      (fun i => 2 * (a i : Real)) y = 2 := by
    unfold thresholdSelectedMass
    simp_rw [hI0, mul_one]
    exact hAd.1
  choose j hj hOne hZero hUnique hCollapse using
    finiteEven_selected_minimal Finset.univ a y 0 hZeroSelected
  simp_rw [hI0, mul_one] at hCollapse
  have hFirst : M = 2 * y j := hAd.2.2.1.symm.trans (hCollapse (fun z => z))
  have hSecond : M = 2 * (y j) ^ 2 := hAd.2.2.2.1.symm.trans (hCollapse (fun z => z ^ 2))
  have hSelect : 2 * momentRoundIndicator d (y j) = 2 :=
    (hCollapse (momentRoundIndicator d)).symm.trans hAd.2.2.2.2
  have hyCut : d <= y j := by
    by_contra hn
    simp only [momentRoundIndicator, ite_eq_right hn, mul_zero] at hSelect
    norm_num at hSelect
  have hyPos : 0 < y j := lt_of_lt_of_le hd hyCut
  have hyOne : y j = 1 := by
    have hRoot : y j * (y j - 1) = 0 := by nlinarith only [hFirst, hSecond]
    rcases mul_eq_zero.mp hRoot with hz | ho
    next =>
      exfalso
      linarith only [hz, hyPos]
    next => exact sub_eq_zero.mp ho
  refine And.intro (by simpa only [hyOne, mul_one] using hFirst) ?_
  intro phi
  simpa only [hyOne] using hCollapse phi

theorem thresholdEvenSplit_no_better_holder (m k : Nat) (d h C eps : Real)
    (hk : 2 <= k) (hd : And (0 < d) (d < 1))
    (hh : 1 / 2 < h) (hC : 0 <= C) (heps : 0 < eps) :
    exists q : Real, And (0 < q)
      (And (thresholdTotalAdmissible d
        (thresholdTotalUpper d (2 * (m : Real) + 2 * (k : Real)) (2 * (k : Real)) -
          thresholdEvenSplitGap m k d q) (2 * (m : Real) + 2 * (k : Real)) (2 * (k : Real))
        (thresholdEvenSplitOrder m k) (thresholdEvenSplitCoord m k d q))
        (And (0 < thresholdEvenSplitGap m k d q)
          (And (thresholdEvenSplitGap m k d q < eps)
            (C * (thresholdEvenSplitGap m k d q) ^ h < thresholdEvenSplitError m k d q)))) := by
  let L := 2 * (m : Real) + 1
  have hNat : (0 : Real) <= (m : Real) := Nat.cast_nonneg m
  have hL : 0 < L := by dsimp only [L]; linarith only [hNat]
  have hPowerPos : 0 < 2 * h - 1 := by linarith only [hh]
  have hCont : ContinuousAt (fun x : Real => L * C ^ 2 * x ^ (2 * h - 1)) 0 :=
    continuousAt_const.mul (Real.continuous_rpow_const hPowerPos.le).continuousAt
  have hZero : L * C ^ 2 * (0 : Real) ^ (2 * h - 1) < 1 := by
    rw [Real.zero_rpow hPowerPos.ne', mul_zero]
    norm_num
  have hEvent : Filter.Eventually (fun x : Real => L * C ^ 2 * x ^ (2 * h - 1) < 1) (nhds 0) :=
    hCont.tendsto.eventually (Iio_mem_nhds hZero)
  choose e he hBall using Metric.mem_nhds_iff.mp hEvent
  choose q hq hAd hDelta hSmall hD hLower using
    thresholdEvenSplit_arbitrarily_small m k d (min eps e) hk hd (lt_min heps he)
  have hEps : thresholdEvenSplitGap m k d q < eps :=
    lt_of_lt_of_le hSmall (min_le_left _ _)
  have hE : thresholdEvenSplitGap m k d q < e :=
    lt_of_lt_of_le hSmall (min_le_right _ _)
  have hNear : L * C ^ 2 * (thresholdEvenSplitGap m k d q) ^ (2 * h - 1) < 1 :=
    hBall (show Membership.mem (Metric.ball (0 : Real) e) (thresholdEvenSplitGap m k d q) by
      change dist (thresholdEvenSplitGap m k d q) 0 < e
      simpa only [Real.dist_eq, sub_zero, abs_of_pos hDelta] using hE)
  have hStrict : C * (thresholdEvenSplitGap m k d q) ^ h < thresholdEvenSplitError m k d q := by
    let delta := thresholdEvenSplitGap m k d q
    let D := thresholdEvenSplitError m k d q
    by_contra hn
    have hUpper : D <= C * delta ^ h := le_of_not_gt hn
    have hPower : delta ^ h * delta ^ h = delta * delta ^ (2 * h - 1) := by
      calc
        _ = delta ^ (h + h) := (Real.rpow_add hDelta h h).symm
        _ = delta ^ (1 + (2 * h - 1)) := by congr 1; ring
        _ = delta * delta ^ (2 * h - 1) := by rw [Real.rpow_add hDelta, Real.rpow_one]
    have hCD : 0 <= C * delta ^ h := mul_nonneg hC (Real.rpow_pos_of_pos hDelta h).le
    have hProduct := mul_nonneg (sub_nonneg.mpr hUpper) (add_nonneg hCD hD.le)
    have hSquare : D ^ 2 <= C ^ 2 * delta * delta ^ (2 * h - 1) := by
      calc
        _ <= (C * delta ^ h) ^ 2 := by nlinarith only [hProduct]
        _ = C ^ 2 * (delta ^ h * delta ^ h) := by ring
        _ = _ := by rw [hPower]; ring
    have hScale := mul_le_mul_of_nonneg_left hSquare hL.le
    have hSmallProduct : L * (C ^ 2 * delta * delta ^ (2 * h - 1)) < delta := by
      calc
        _ = delta * (L * C ^ 2 * delta ^ (2 * h - 1)) := by ring
        _ < delta * 1 := mul_lt_mul_of_pos_left hNear hDelta
        _ = _ := by ring
    nlinarith only [hLower, hScale, hSmallProduct]
  exact Exists.intro q (And.intro hq (And.intro hAd
    (And.intro hDelta (And.intro hEps hStrict))))

theorem finiteEven_upper_half_holder {r : Nat} (m k : Nat) (d M : Real)
    (a : Fin r -> Nat) (y : Fin r -> Real) (hk : 0 < k)
    (hd : And (0 < d) (d < 1))
    (hAd : thresholdTotalAdmissible d M (2 * (m : Real) + 2 * (k : Real)) (2 * (k : Real)) a y)
    (hSmall : thresholdTotalUpper d (2 * (m : Real) + 2 * (k : Real)) (2 * (k : Real)) - M <= 1) :
    let N := 2 * (m : Real) + 2 * (k : Real)
    let K := 2 * (k : Real)
    let v := thresholdModelHigh (2 * (m : Real)) K d
    let delta := thresholdTotalUpper d N K - M
    And (0 <= delta)
      (forall phi : Real -> Real,
        (forall u z : Real, abs (phi u - phi z) <= abs (u - z)) ->
        abs (Finset.sum Finset.univ (fun i => 2 * (a i : Real) * phi (y i)) -
          thresholdTotalStatistic d v N K phi) <=
            ((2 * v - 1) / (2 * (v - d)) + Real.sqrt (K * (2 * v - 1))) * Real.sqrt delta) := by
  dsimp only
  let N := 2 * (m : Real) + 2 * (k : Real)
  let K := 2 * (k : Real)
  let v := thresholdModelHigh (2 * (m : Real)) K d
  let delta := thresholdTotalUpper d N K - M
  have hkR : (0 : Real) < (k : Real) := by exact_mod_cast hk
  have hK : 0 < K := mul_pos (by norm_num) hkR
  have ha : forall i, Membership.mem (Finset.univ : Finset (Fin r)) i -> 0 <= 2 * (a i : Real) :=
    fun i _ => mul_nonneg (by norm_num) (Nat.cast_nonneg (a i))
  have hMoment := hAd.2.2.2.1.trans hAd.2.2.1.symm
  have hSelected : 0 < thresholdSelectedMass d Finset.univ (fun i => 2 * (a i : Real)) y := by
    rw [hAd.2.2.2.2]
    exact hK
  have hLedger := finiteWeighted_total_upper_ledger Finset.univ
    (fun i => 2 * (a i : Real)) y d hd ha hMoment hSelected
  rw [hAd.1, hAd.2.2.1, hAd.2.2.2.2] at hLedger
  dsimp only at hLedger
  rw [show 2 * (m : Real) + 2 * (k : Real) - 2 * (k : Real) = 2 * (m : Real) by ring] at hLedger
  have hv : 1 <= v := hLedger.1
  have hDelta : 0 <= delta := hLedger.2.1
  have hVD : 0 < v - d := by linarith only [hv, hd.2]
  have hSlope : 0 <= 2 * v - 1 := by linarith only [hv]
  have hA : 0 <= K * (2 * v - 1) := mul_nonneg hK.le hSlope
  have hRoot : (Real.sqrt delta) ^ 2 = delta := Real.sq_sqrt hDelta
  have hRootNonneg := Real.sqrt_nonneg delta
  have hDeltaSmall : delta <= 1 := hSmall
  have hRootSmall : Real.sqrt delta <= 1 := by nlinarith only [hRoot, hRootNonneg, hDeltaSmall]
  have hGapRoot : delta <= Real.sqrt delta := by nlinarith only [hRoot, hRootNonneg, hRootSmall]
  have hCoefficient : 0 <= (2 * v - 1) / (2 * (v - d)) :=
    div_nonneg hSlope (mul_nonneg (by norm_num) hVD.le)
  refine And.intro hDelta ?_
  intro phi hphi
  have hBound := (finiteWeighted_threshold_total_stability Finset.univ
    (fun i => 2 * (a i : Real)) y d hd ha hMoment hSelected).2.2 phi hphi
  rw [hAd.1, hAd.2.2.1, hAd.2.2.2.2] at hBound
  rw [show 2 * (m : Real) + 2 * (k : Real) - 2 * (k : Real) = 2 * (m : Real) by ring] at hBound
  change abs (Finset.sum Finset.univ (fun i => 2 * (a i : Real) * phi (y i)) -
    thresholdTotalStatistic d v N K phi) <=
      (2 * v - 1) * delta / (2 * (v - d)) + Real.sqrt (K * ((2 * v - 1) * delta)) at hBound
  have hSqrt : Real.sqrt (K * ((2 * v - 1) * delta)) =
      Real.sqrt (K * (2 * v - 1)) * Real.sqrt delta := by
    rw [<- mul_assoc, Real.sqrt_mul hA]
  have hLinear : (2 * v - 1) * delta / (2 * (v - d)) <=
      (2 * v - 1) / (2 * (v - d)) * Real.sqrt delta := by
    have hh := mul_le_mul_of_nonneg_left hGapRoot hCoefficient
    calc
      _ = (2 * v - 1) / (2 * (v - d)) * delta := by ring
      _ <= _ := hh
  calc
    _ <= (2 * v - 1) * delta / (2 * (v - d)) +
        Real.sqrt (K * ((2 * v - 1) * delta)) := hBound
    _ <= (2 * v - 1) / (2 * (v - d)) * Real.sqrt delta +
        Real.sqrt (K * (2 * v - 1)) * Real.sqrt delta := by rw [hSqrt]; linarith only [hLinear]
    _ = _ := by ring

theorem finiteEven_single_no_better_holder (m : Nat) (d h C eps : Real)
    (hm : 0 < m) (hd : And (0 < d) (d < 1)) (hh : 1 < h) (heps : 0 < eps) :
    exists e : Real,
      let a := thresholdPairWeights m 1
      let y := thresholdPairCoords (d - e) (thresholdSingleFamilyHigh (2 * (m : Real)) 2 d e)
      let delta := thresholdSingleFamilyGap (2 * (m : Real)) 2 d e
      let N := 2 * (m : Real) + 2
      let v := thresholdModelHigh (2 * (m : Real)) 2 d
      And (And (0 < delta) (delta < eps))
        (And (thresholdTotalAdmissible d (thresholdTotalUpper d N 2 - delta) N 2 a y)
          (C * delta ^ h < abs (Finset.sum Finset.univ (fun i => 2 * (a i : Real) *
            abs (y i - v)) - thresholdTotalStatistic d v N 2 (fun z => abs (z - v))))) := by
  have hPowerPos : 0 < h - 1 := sub_pos.mpr hh
  have hCont : ContinuousAt (fun x : Real => 2 * C * x ^ (h - 1)) 0 :=
    continuousAt_const.mul (Real.continuous_rpow_const hPowerPos.le).continuousAt
  have hZero : 2 * C * (0 : Real) ^ (h - 1) < 1 := by
    rw [Real.zero_rpow hPowerPos.ne', mul_zero]
    norm_num
  have hEvent : Filter.Eventually (fun x : Real => 2 * C * x ^ (h - 1) < 1) (nhds 0) :=
    hCont.tendsto.eventually (Iio_mem_nhds hZero)
  choose r hr hBall using Metric.mem_nhds_iff.mp hEvent
  have hCoeff : (1 / 2 : Real) <
      thresholdSingleCoefficient d (thresholdModelHigh (2 * (m : Real)) 2 d) :=
    lt_of_lt_of_le (by norm_num) (le_max_left _ _)
  choose e hGap hAd hCost using finiteEven_minimal_selected_sharp m d (1 / 2) (min eps r)
    hm hd (lt_min heps hr) hCoeff
  let delta := thresholdSingleFamilyGap (2 * (m : Real)) 2 d e
  have hSmall : delta < eps := lt_of_lt_of_le hGap.2 (min_le_left _ _)
  have hNear : 2 * C * delta ^ (h - 1) < 1 :=
    hBall (show Membership.mem (Metric.ball (0 : Real) r) delta by
      change dist delta 0 < r
      rw [Real.dist_eq, sub_zero, abs_of_pos (show 0 < delta from hGap.1)]
      exact lt_of_lt_of_le hGap.2 (min_le_right _ _))
  have hPower : delta ^ h = delta * delta ^ (h - 1) := by
    calc
      _ = delta ^ (1 + (h - 1)) := by congr 1; ring
      _ = _ := by rw [Real.rpow_add hGap.1, Real.rpow_one]
  have hProduct := mul_lt_mul_of_pos_left hNear hGap.1
  have hGain : C * delta ^ h < (1 / 2) * delta := by
    rw [hPower]
    nlinarith only [hProduct]
  exact Exists.intro e (And.intro (And.intro hGap.1 hSmall)
    (And.intro hAd (lt_trans hGain hCost)))

end PrimeFactorOscillations

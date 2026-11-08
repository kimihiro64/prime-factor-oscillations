/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.ThresholdTotalStability

/-! # Exact upper-boundary cost and sharp single-level linear stability -/

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 5000000

noncomputable section
namespace PrimeFactorOscillations

def thresholdSingleCoefficient (d v : Real) : Real :=
  max 1 ((v + d - 1) / (v - d))

def thresholdTotalOvershoot (v y : Real) : Real := max (y - v) 0

def thresholdSelectedDirac {Iota : Type*} (d : Real) (S : Finset Iota)
    (a y : Iota -> Real) (h : Real) : Prop :=
  forall phi : Real -> Real,
    Finset.sum S (fun i => a i * momentRoundIndicator d (y i) * phi (y i)) =
      thresholdSelectedMass d S a y * phi h

theorem thresholdAbsoluteProbe_lipschitz (v : Real) :
    forall u z : Real, abs (abs (u - v) - abs (z - v)) <= abs (u - z) := by
  intro u z
  calc
    _ <= abs ((u - v) - (z - v)) := abs_abs_sub_abs_le_abs_sub _ _
    _ = _ := by congr 1; ring

theorem thresholdTotal_absolute_potential (d v y : Real) (hdv : d <= v) :
    abs (y - v) = (v - d) * (1 - momentRoundIndicator d y) +
      thresholdTotalLowDistance d y + thresholdTotalHighDistance d v y := by
  by_cases hCut : d <= y
  case pos =>
    simp [thresholdTotalLowDistance, thresholdTotalHighDistance, momentRoundIndicator, hCut]
  case neg =>
    have hNeg : y - v <= 0 := by linarith only [le_of_not_ge hCut, hdv]
    simp only [thresholdTotalLowDistance, thresholdTotalHighDistance, momentRoundIndicator,
      ite_eq_right hCut, sub_zero, mul_one, mul_zero, add_zero]
    rw [abs_of_nonpos hNeg]
    ring

theorem finiteWeighted_total_potential_identity {Iota : Type*} (S : Finset Iota)
    (a y : Iota -> Real) (d v : Real) (hdv : d <= v) :
    Finset.sum S (fun i => a i * abs (y i - v)) -
      thresholdTotalStatistic d v (Finset.sum S a) (thresholdSelectedMass d S a y)
        (fun z => abs (z - v)) =
      Finset.sum S (fun i => a i * thresholdTotalLowDistance d (y i)) +
        Finset.sum S (fun i => a i * thresholdTotalHighDistance d v (y i)) := by
  let N := Finset.sum S a
  let K := thresholdSelectedMass d S a y
  let L := Finset.sum S (fun i => a i * thresholdTotalLowDistance d (y i))
  let H := Finset.sum S (fun i => a i * thresholdTotalHighDistance d v (y i))
  have hSum : Finset.sum S (fun i => a i * abs (y i - v)) =
      (v - d) * (N - K) + L + H := by
    calc
      _ = Finset.sum S (fun i => (v - d) * (a i - a i * momentRoundIndicator d (y i)) +
          a i * thresholdTotalLowDistance d (y i) +
          a i * thresholdTotalHighDistance d v (y i)) := by
        apply Finset.sum_congr rfl
        intro i _
        rw [thresholdTotal_absolute_potential d v (y i) hdv]
        ring
      _ = _ := by
        simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, <- Finset.mul_sum]
        rfl
  have hReference : thresholdTotalStatistic d v N K (fun z => abs (z - v)) =
      (N - K) * (v - d) := by
    dsimp only [thresholdTotalStatistic]
    rw [abs_of_nonpos (sub_nonpos.mpr hdv)]
    simp only [sub_self, abs_zero, mul_zero, add_zero]
    ring
  change Finset.sum S (fun i => a i * abs (y i - v)) -
    thresholdTotalStatistic d v N K (fun z => abs (z - v)) = L + H
  rw [hSum, hReference]
  ring

theorem finiteWeighted_total_exact_cost {Iota : Type*} (S : Finset Iota)
    (a y : Iota -> Real) (d v : Real) (hdv : d <= v)
    (ha : forall i, Membership.mem S i -> 0 <= a i) :
    let L := Finset.sum S (fun i => a i * thresholdTotalLowDistance d (y i))
    let H := Finset.sum S (fun i => a i * thresholdTotalHighDistance d v (y i))
    And (abs (Finset.sum S (fun i => a i * abs (y i - v)) -
      thresholdTotalStatistic d v (Finset.sum S a) (thresholdSelectedMass d S a y)
        (fun z => abs (z - v))) = L + H)
      (forall phi : Real -> Real,
        (forall u z : Real, abs (phi u - phi z) <= abs (u - z)) ->
        abs (Finset.sum S (fun i => a i * phi (y i)) -
          thresholdTotalStatistic d v (Finset.sum S a) (thresholdSelectedMass d S a y) phi) <=
            L + H) := by
  dsimp only
  have hL := Finset.sum_nonneg
    (fun i hi => mul_nonneg (ha i hi) (thresholdTotalLayer_nonneg d v (y i)).1)
  have hH := Finset.sum_nonneg
    (fun i hi => mul_nonneg (ha i hi) (thresholdTotalLayer_nonneg d v (y i)).2.1)
  refine And.intro ?_ (fun phi hphi => finiteWeighted_total_statistic_cost S a y d v phi ha hphi)
  rw [finiteWeighted_total_potential_identity S a y d v hdv, abs_of_nonneg (add_nonneg hL hH)]

theorem thresholdAbsoluteProbe_overshoot (v y : Real) :
    abs (y - v) = v - y + 2 * thresholdTotalOvershoot v y := by
  by_cases hp : 0 <= y - v
  case pos =>
    rw [abs_of_nonneg hp]
    dsimp only [thresholdTotalOvershoot]
    rw [max_eq_left hp]
    ring
  case neg =>
    have hn : y - v <= 0 := le_of_not_ge hp
    rw [abs_of_nonpos hn]
    dsimp only [thresholdTotalOvershoot]
    rw [max_eq_right hn]
    ring

theorem finiteWeighted_total_overshoot_identity {Iota : Type*} (S : Finset Iota)
    (a y : Iota -> Real) (d v : Real) (hdv : d <= v) :
    Finset.sum S (fun i => a i * abs (y i - v)) -
      thresholdTotalStatistic d v (Finset.sum S a) (thresholdSelectedMass d S a y)
        (fun z => abs (z - v)) =
      (Finset.sum S a - thresholdSelectedMass d S a y) * d +
        thresholdSelectedMass d S a y * v - Finset.sum S (fun i => a i * y i) +
          2 * Finset.sum S (fun i => a i * thresholdTotalOvershoot v (y i)) := by
  have hSum : Finset.sum S (fun i => a i * abs (y i - v)) =
      v * Finset.sum S a - Finset.sum S (fun i => a i * y i) +
        2 * Finset.sum S (fun i => a i * thresholdTotalOvershoot v (y i)) := by
    calc
      _ = Finset.sum S (fun i => v * a i - a i * y i +
          2 * (a i * thresholdTotalOvershoot v (y i))) := by
        apply Finset.sum_congr rfl
        intro i _
        rw [thresholdAbsoluteProbe_overshoot]
        ring
      _ = _ := by
        simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, <- Finset.mul_sum]
  rw [hSum]
  dsimp only [thresholdTotalStatistic]
  rw [abs_of_nonpos (sub_nonpos.mpr hdv)]
  simp only [sub_self, abs_zero, mul_zero, add_zero]
  ring

theorem thresholdSingle_linear_bound (d v Delta L : Real)
    (hdv : d < v) (hDelta : 0 <= Delta)
    (hLow : 2 * (v - d) * L <= (2 * v - 1) * Delta) :
    L + abs (Delta - L) <= thresholdSingleCoefficient d v * Delta := by
  let q := (v + d - 1) / (v - d)
  have hVD : 0 < v - d := sub_pos.mpr hdv
  by_cases hL : L <= Delta
  case pos =>
    rw [abs_of_nonneg (sub_nonneg.mpr hL)]
    have hC := mul_le_mul_of_nonneg_right (le_max_left (1 : Real) q) hDelta
    change L + (Delta - L) <= max 1 q * Delta
    nlinarith only [hC]
  case neg =>
    have hAbs : abs (Delta - L) = L - Delta := by
      rw [abs_of_nonpos (by linarith only [le_of_not_ge hL])]
      ring
    have hProduct : (q * Delta) * (v - d) = (v + d - 1) * Delta := by
      dsimp only [q]
      field_simp [hVD.ne']
    have hQ : 2 * L - Delta <= q * Delta := by
      by_contra hn
      have hBad := mul_pos hVD (sub_pos.mpr (lt_of_not_ge hn))
      nlinarith only [hLow, hProduct, hBad]
    rw [hAbs]
    exact le_trans (by linarith only [hQ])
      (mul_le_mul_of_nonneg_right (le_max_right (1 : Real) q) hDelta)

theorem thresholdSingleCoefficient_half (d v : Real) (hd : d <= 1 / 2) (hdv : d < v) :
    thresholdSingleCoefficient d v = 1 := by
  have hVD : 0 < v - d := sub_pos.mpr hdv
  have hProduct : (v + d - 1) / (v - d) * (v - d) = v + d - 1 := by
    field_simp [hVD.ne']
  have hQ : (v + d - 1) / (v - d) <= 1 := by
    by_contra hn
    have hBad := mul_pos hVD (sub_pos.mpr (lt_of_not_ge hn))
    nlinarith only [hProduct, hBad, hd]
  exact max_eq_left hQ

theorem finiteWeighted_single_level_linear {Iota : Type*} (S : Finset Iota)
    (a y : Iota -> Real) (d h : Real) (hd : And (0 < d) (d < 1))
    (ha : forall i, Membership.mem S i -> 0 <= a i)
    (hMoment : Finset.sum S (fun i => a i * (y i) ^ 2) = Finset.sum S (fun i => a i * y i))
    (hK : 0 < thresholdSelectedMass d S a y)
    (hDirac : thresholdSelectedDirac d S a y h) :
    let N := Finset.sum S a
    let K := thresholdSelectedMass d S a y
    let M := Finset.sum S (fun i => a i * y i)
    let v := thresholdModelHigh (N - K) K d
    let Delta := thresholdTotalUpper d N K - M
    let L := Finset.sum S (fun i => a i * thresholdTotalLowDistance d (y i))
    And (0 <= Delta)
      (And (abs (Finset.sum S (fun i => a i * abs (y i - v)) -
        thresholdTotalStatistic d v N K (fun z => abs (z - v))) = L + abs (Delta - L))
        (And (forall phi : Real -> Real,
          (forall u z : Real, abs (phi u - phi z) <= abs (u - z)) ->
          abs (Finset.sum S (fun i => a i * phi (y i)) -
            thresholdTotalStatistic d v N K phi) <= L + abs (Delta - L))
          (forall phi : Real -> Real,
            (forall u z : Real, abs (phi u - phi z) <= abs (u - z)) ->
            abs (Finset.sum S (fun i => a i * phi (y i)) -
              thresholdTotalStatistic d v N K phi) <= thresholdSingleCoefficient d v * Delta))) := by
  dsimp only
  let N := Finset.sum S a
  let K := thresholdSelectedMass d S a y
  let M := Finset.sum S (fun i => a i * y i)
  let v := thresholdModelHigh (N - K) K d
  let Delta := thresholdTotalUpper d N K - M
  let L := Finset.sum S (fun i => a i * thresholdTotalLowDistance d (y i))
  let H := Finset.sum S (fun i => a i * thresholdTotalHighDistance d v (y i))
  have hLedger := finiteWeighted_total_upper_ledger S a y d hd ha hMoment hK
  have hdv : d < v := lt_of_lt_of_le hd.2 hLedger.1
  have hLowIdentity : L = d * (N - K) - M + K * h := by
    calc
      _ = Finset.sum S (fun i => d * (a i - a i * momentRoundIndicator d (y i)) -
          a i * y i + a i * momentRoundIndicator d (y i) * y i) := by
        apply Finset.sum_congr rfl
        intro i _
        dsimp only [thresholdTotalLowDistance]
        ring
      _ = d * (N - K) - M +
          Finset.sum S (fun i => a i * momentRoundIndicator d (y i) * y i) := by
        simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, <- Finset.mul_sum]
        rfl
      _ = _ := by rw [hDirac (fun z => z)]
  have hH : H = K * abs (h - v) := by
    calc
      _ = Finset.sum S (fun i => a i * momentRoundIndicator d (y i) * abs (y i - v)) := by
        apply Finset.sum_congr rfl
        intro i _
        dsimp only [thresholdTotalHighDistance]
        ring
      _ = _ := hDirac (fun z => abs (z - v))
  have hDrift : Delta - L = K * (v - h) := by
    change thresholdTotalUpper d N K - M - L = _
    change (N - K) * d + K * v - M - L = _
    rw [hLowIdentity]
    ring
  have hHDelta : H = abs (Delta - L) := by
    rw [hH, hDrift, abs_mul, abs_of_nonneg hK.le, abs_sub_comm v h]
  have hExact := finiteWeighted_total_exact_cost S a y d v hdv.le ha
  have hAt : abs (Finset.sum S (fun i => a i * abs (y i - v)) -
      thresholdTotalStatistic d v N K (fun z => abs (z - v))) = L + abs (Delta - L) := by
    calc
      _ = L + H := hExact.1
      _ = _ := by rw [hHDelta]
  have hAll : forall phi : Real -> Real,
      (forall u z : Real, abs (phi u - phi z) <= abs (u - z)) ->
      abs (Finset.sum S (fun i => a i * phi (y i)) -
        thresholdTotalStatistic d v N K phi) <= L + abs (Delta - L) := by
    intro phi hphi
    calc
      _ <= L + H := hExact.2 phi hphi
      _ = _ := by rw [hHDelta]
  have hControl := finiteWeighted_total_layer_control S a y d v hdv ha
  rw [hLedger.2.2] at hControl
  have hScalar := thresholdSingle_linear_bound d v Delta L hdv hLedger.2.1 hControl.2.2.2.1
  exact And.intro hLedger.2.1 (And.intro hAt (And.intro hAll
    (fun phi hphi => le_trans (hAll phi hphi) hScalar)))

theorem finiteWeighted_single_level_half {Iota : Type*} (S : Finset Iota)
    (a y : Iota -> Real) (d h : Real) (hd : And (0 < d) (d <= 1 / 2))
    (ha : forall i, Membership.mem S i -> 0 <= a i)
    (hMoment : Finset.sum S (fun i => a i * (y i) ^ 2) = Finset.sum S (fun i => a i * y i))
    (hK : 0 < thresholdSelectedMass d S a y)
    (hDirac : thresholdSelectedDirac d S a y h) :
    let N := Finset.sum S a
    let K := thresholdSelectedMass d S a y
    let M := Finset.sum S (fun i => a i * y i)
    let v := thresholdModelHigh (N - K) K d
    let Delta := thresholdTotalUpper d N K - M
    And (abs (Finset.sum S (fun i => a i * abs (y i - v)) -
      thresholdTotalStatistic d v N K (fun z => abs (z - v))) = Delta)
      (forall phi : Real -> Real,
        (forall u z : Real, abs (phi u - phi z) <= abs (u - z)) ->
        abs (Finset.sum S (fun i => a i * phi (y i)) -
          thresholdTotalStatistic d v N K phi) <= Delta) := by
  dsimp only
  have hd1 : And (0 < d) (d < 1) := And.intro hd.1 (by linarith only [hd.2])
  let N := Finset.sum S a
  let K := thresholdSelectedMass d S a y
  let v := thresholdModelHigh (N - K) K d
  let Delta := thresholdTotalUpper d N K - Finset.sum S (fun i => a i * y i)
  let L := Finset.sum S (fun i => a i * thresholdTotalLowDistance d (y i))
  have hMain := finiteWeighted_single_level_linear S a y d h hd1 ha hMoment hK hDirac
  have hLedger := finiteWeighted_total_upper_ledger S a y d hd1 ha hMoment hK
  have hCoeff := thresholdSingleCoefficient_half d v hd.2 (lt_of_lt_of_le hd1.2 hLedger.1)
  have hUpper := hMain.2.2.2 (fun z => abs (z - v)) (thresholdAbsoluteProbe_lipschitz v)
  rw [hCoeff, one_mul] at hUpper
  have hLower : Delta <= abs (Finset.sum S (fun i => a i * abs (y i - v)) -
      thresholdTotalStatistic d v N K (fun z => abs (z - v))) := by
    rw [hMain.2.1]
    change Delta <= L + abs (Delta - L)
    linarith only [le_abs_self (Delta - L)]
  refine And.intro (le_antisymm hUpper hLower) ?_
  intro phi hphi
  have hb := hMain.2.2.2 phi hphi
  rw [hCoeff, one_mul] at hb
  exact hb
end PrimeFactorOscillations

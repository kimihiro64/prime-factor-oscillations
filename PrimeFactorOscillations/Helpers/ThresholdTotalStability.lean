/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.ThresholdTotalBoundary

/-! # Quantitative two-layer stability at the fixed-total upper boundary -/

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 5000000

noncomputable section
namespace PrimeFactorOscillations

def thresholdTotalLowDistance (d y : Real) : Real :=
  (d - y) * (1 - momentRoundIndicator d y)

def thresholdTotalHighDistance (d v y : Real) : Real :=
  abs (y - v) * momentRoundIndicator d y

def thresholdTotalHighSquare (d v y : Real) : Real :=
  (y - v) ^ 2 * momentRoundIndicator d y

def thresholdTotalStatistic (d v N K : Real) (phi : Real -> Real) : Real :=
  (N - K) * phi d + K * phi v

theorem thresholdTotalPacket_layers (d v y : Real) :
    thresholdTotalPacket d v y =
      (d - y) ^ 2 * (1 - momentRoundIndicator d y) +
        2 * (v - d) * thresholdTotalLowDistance d y +
        thresholdTotalHighSquare d v y := by
  by_cases hCut : d <= y
  case pos =>
    simp [thresholdTotalPacket, thresholdTotalLowDistance, thresholdTotalHighSquare,
      momentRoundIndicator, hCut]
  case neg =>
    simp only [thresholdTotalPacket, thresholdTotalLowDistance, thresholdTotalHighSquare,
      momentRoundIndicator, ite_eq_right hCut, sub_zero, mul_one, mul_zero, add_zero]
    ring

theorem thresholdTotalLayer_nonneg (d v y : Real) :
    And (0 <= thresholdTotalLowDistance d y)
      (And (0 <= thresholdTotalHighDistance d v y)
        (0 <= thresholdTotalHighSquare d v y)) := by
  by_cases hCut : d <= y
  case pos =>
    simp only [thresholdTotalLowDistance, thresholdTotalHighDistance, thresholdTotalHighSquare,
      momentRoundIndicator, ite_eq_left hCut, sub_self, mul_zero, mul_one]
    exact And.intro le_rfl (And.intro (abs_nonneg _) (sq_nonneg _))
  case neg =>
    simp only [thresholdTotalLowDistance, thresholdTotalHighDistance, thresholdTotalHighSquare,
      momentRoundIndicator, ite_eq_right hCut, sub_zero, mul_one, mul_zero]
    exact And.intro (sub_nonneg.mpr (le_of_not_ge hCut)) (And.intro le_rfl le_rfl)

theorem finiteWeighted_total_layer_control {Iota : Type*} (S : Finset Iota)
    (a y : Iota -> Real) (d v : Real) (hdv : d < v)
    (ha : forall i, Membership.mem S i -> 0 <= a i) :
    let E := Finset.sum S (fun i => a i * thresholdTotalPacket d v (y i))
    let L := Finset.sum S (fun i => a i * thresholdTotalLowDistance d (y i))
    let Q := Finset.sum S (fun i => a i * thresholdTotalHighSquare d v (y i))
    And (0 <= E) (And (0 <= L) (And (0 <= Q)
      (And (2 * (v - d) * L <= E) (Q <= E)))) := by
  dsimp only
  have hE := Finset.sum_nonneg
    (fun i hi => mul_nonneg (ha i hi) (thresholdTotalPacket_nonneg d v (y i) hdv))
  have hL := Finset.sum_nonneg
    (fun i hi => mul_nonneg (ha i hi) (thresholdTotalLayer_nonneg d v (y i)).1)
  have hQ := Finset.sum_nonneg
    (fun i hi => mul_nonneg (ha i hi) (thresholdTotalLayer_nonneg d v (y i)).2.2)
  have hOther : forall z : Real, 0 <= (d - z) ^ 2 * (1 - momentRoundIndicator d z) := by
    intro z
    by_cases hCut : d <= z
    case pos => simp [momentRoundIndicator, hCut]
    case neg => simpa [momentRoundIndicator, hCut] using sq_nonneg (d - z)
  have hLowEach : forall z : Real,
      2 * (v - d) * thresholdTotalLowDistance d z <= thresholdTotalPacket d v z := by
    intro z
    rw [thresholdTotalPacket_layers]
    linarith only [hOther z, (thresholdTotalLayer_nonneg d v z).2.2]
  have hHighEach : forall z : Real,
      thresholdTotalHighSquare d v z <= thresholdTotalPacket d v z := by
    intro z
    have hProd := mul_nonneg
      (mul_nonneg (by norm_num : (0 : Real) <= 2) (sub_nonneg.mpr hdv.le))
      (thresholdTotalLayer_nonneg d v z).1
    rw [thresholdTotalPacket_layers]
    linarith only [hOther z, hProd]
  have hLowSum := Finset.sum_le_sum
    (fun i hi => mul_le_mul_of_nonneg_left (hLowEach (y i)) (ha i hi))
  have hLowIdentity : Finset.sum S (fun i =>
      a i * (2 * (v - d) * thresholdTotalLowDistance d (y i))) =
      2 * (v - d) * Finset.sum S (fun i => a i * thresholdTotalLowDistance d (y i)) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [hLowIdentity] at hLowSum
  exact And.intro hE (And.intro hL (And.intro hQ (And.intro hLowSum
    (Finset.sum_le_sum (fun i hi => mul_le_mul_of_nonneg_left (hHighEach (y i)) (ha i hi))))))

theorem finiteWeighted_total_high_distance {Iota : Type*} (S : Finset Iota)
    (a y : Iota -> Real) (d v : Real)
    (ha : forall i, Membership.mem S i -> 0 <= a i)
    (hK : 0 < thresholdSelectedMass d S a y) :
    (Finset.sum S (fun i => a i * thresholdTotalHighDistance d v (y i))) ^ 2 <=
      thresholdSelectedMass d S a y *
        Finset.sum S (fun i => a i * thresholdTotalHighSquare d v (y i)) := by
  let K := thresholdSelectedMass d S a y
  let H := Finset.sum S (fun i => a i * thresholdTotalHighDistance d v (y i))
  let Q := Finset.sum S (fun i => a i * thresholdTotalHighSquare d v (y i))
  have hI : forall z : Real, 0 <= momentRoundIndicator d z := by
    intro z
    unfold momentRoundIndicator
    split_ifs <;> norm_num
  have hVar : 0 <= Finset.sum S (fun i =>
      a i * momentRoundIndicator d (y i) * (K * abs (y i - v) - H) ^ 2) :=
    Finset.sum_nonneg (fun i hi => mul_nonneg (mul_nonneg (ha i hi) (hI (y i))) (sq_nonneg _))
  have hExpand : Finset.sum S (fun i =>
      a i * momentRoundIndicator d (y i) * (K * abs (y i - v) - H) ^ 2) =
      K ^ 2 * Q - K * H ^ 2 := by
    calc
      _ = Finset.sum S (fun i =>
          K ^ 2 * (a i * thresholdTotalHighSquare d v (y i)) -
            2 * K * H * (a i * thresholdTotalHighDistance d v (y i)) +
            H ^ 2 * (a i * momentRoundIndicator d (y i))) := by
        apply Finset.sum_congr rfl
        intro i _
        dsimp only [thresholdTotalHighSquare, thresholdTotalHighDistance]
        rw [sub_sq, mul_pow, sq_abs]
        ring
      _ = K ^ 2 * Q - 2 * K * H * H + H ^ 2 * K := by
        simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, <- Finset.mul_sum]
        rfl
      _ = _ := by ring
  rw [hExpand] at hVar
  change H ^ 2 <= K * Q
  by_contra hn
  have hBad := mul_pos hK (sub_pos.mpr (lt_of_not_ge hn))
  nlinarith only [hVar, hBad]

theorem thresholdTotal_residual_bound (d v y : Real) (phi : Real -> Real)
    (hphi : forall u w : Real, abs (phi u - phi w) <= abs (u - w)) :
    abs (phi y - (1 - momentRoundIndicator d y) * phi d -
      momentRoundIndicator d y * phi v) <=
      thresholdTotalLowDistance d y + thresholdTotalHighDistance d v y := by
  by_cases hCut : d <= y
  case pos =>
    simpa [thresholdTotalLowDistance, thresholdTotalHighDistance, momentRoundIndicator, hCut]
      using hphi y v
  case neg =>
    have hAbs : abs (y - d) = d - y := by
      rw [abs_of_nonpos (by linarith only [le_of_not_ge hCut])]
      ring
    simpa [thresholdTotalLowDistance, thresholdTotalHighDistance, momentRoundIndicator, hCut, hAbs]
      using hphi y d

theorem finiteWeighted_total_statistic_cost {Iota : Type*} (S : Finset Iota)
    (a y : Iota -> Real) (d v : Real) (phi : Real -> Real)
    (ha : forall i, Membership.mem S i -> 0 <= a i)
    (hphi : forall u w : Real, abs (phi u - phi w) <= abs (u - w)) :
    abs (Finset.sum S (fun i => a i * phi (y i)) -
      thresholdTotalStatistic d v (Finset.sum S a) (thresholdSelectedMass d S a y) phi) <=
      Finset.sum S (fun i => a i * thresholdTotalLowDistance d (y i)) +
        Finset.sum S (fun i => a i * thresholdTotalHighDistance d v (y i)) := by
  let f := fun i => phi (y i) - (1 - momentRoundIndicator d (y i)) * phi d -
    momentRoundIndicator d (y i) * phi v
  have hIdentity : Finset.sum S (fun i => a i * f i) =
      Finset.sum S (fun i => a i * phi (y i)) -
        thresholdTotalStatistic d v (Finset.sum S a) (thresholdSelectedMass d S a y) phi := by
    calc
      _ = Finset.sum S (fun i => a i * phi (y i) - a i * phi d +
          (a i * momentRoundIndicator d (y i)) * (phi d - phi v)) := by
        apply Finset.sum_congr rfl
        intro i _
        dsimp only [f]
        ring
      _ = Finset.sum S (fun i => a i * phi (y i)) -
          (Finset.sum S a) * phi d +
          (Finset.sum S (fun i => a i * momentRoundIndicator d (y i))) * (phi d - phi v) := by
        rw [Finset.sum_add_distrib, Finset.sum_sub_distrib,
          <- Finset.sum_mul, <- Finset.sum_mul]
      _ = _ := by
        dsimp only [thresholdTotalStatistic, thresholdSelectedMass]
        ring
  rw [<- hIdentity]
  calc
    _ <= Finset.sum S (fun i => abs (a i * f i)) := Finset.abs_sum_le_sum_abs _ _
    _ = Finset.sum S (fun i => a i * abs (f i)) := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [abs_mul, abs_of_nonneg (ha i hi)]
    _ <= Finset.sum S (fun i => a i *
        (thresholdTotalLowDistance d (y i) + thresholdTotalHighDistance d v (y i))) :=
      Finset.sum_le_sum (fun i hi => mul_le_mul_of_nonneg_left
        (thresholdTotal_residual_bound d v (y i) phi hphi) (ha i hi))
    _ = _ := by simp only [mul_add, Finset.sum_add_distrib]

theorem finiteWeighted_total_packet_stability {Iota : Type*} (S : Finset Iota)
    (a y : Iota -> Real) (d v : Real) (hdv : d < v)
    (ha : forall i, Membership.mem S i -> 0 <= a i)
    (hK : 0 < thresholdSelectedMass d S a y) (phi : Real -> Real)
    (hphi : forall u w : Real, abs (phi u - phi w) <= abs (u - w)) :
    let E := Finset.sum S (fun i => a i * thresholdTotalPacket d v (y i))
    abs (Finset.sum S (fun i => a i * phi (y i)) -
      thresholdTotalStatistic d v (Finset.sum S a) (thresholdSelectedMass d S a y) phi) <=
      E / (2 * (v - d)) + Real.sqrt (thresholdSelectedMass d S a y * E) := by
  dsimp only
  let E := Finset.sum S (fun i => a i * thresholdTotalPacket d v (y i))
  let K := thresholdSelectedMass d S a y
  let L := Finset.sum S (fun i => a i * thresholdTotalLowDistance d (y i))
  let H := Finset.sum S (fun i => a i * thresholdTotalHighDistance d v (y i))
  let Q := Finset.sum S (fun i => a i * thresholdTotalHighSquare d v (y i))
  have hControl := finiteWeighted_total_layer_control S a y d v hdv ha
  have hDen : 0 < 2 * (v - d) := mul_pos (by norm_num) (sub_pos.mpr hdv)
  have hLBound : L <= E / (2 * (v - d)) := by
    have hProduct : E / (2 * (v - d)) * (2 * (v - d)) = E := by
      field_simp [sub_ne_zero.mpr (ne_of_gt hdv)]
    by_contra hn
    have hBad := mul_pos hDen (sub_pos.mpr (lt_of_not_ge hn))
    nlinarith only [hBad, hProduct, hControl.2.2.2.1]
  have hCauchy := finiteWeighted_total_high_distance S a y d v ha hK
  have hSquare : H ^ 2 <= K * E := le_trans hCauchy
    (mul_le_mul_of_nonneg_left hControl.2.2.2.2 hK.le)
  have hRadical := Real.sq_sqrt (mul_nonneg hK.le hControl.1)
  have hHBound : H <= Real.sqrt (K * E) := by
    nlinarith only [hSquare, hRadical, Real.sqrt_nonneg (K * E)]
  exact le_trans (finiteWeighted_total_statistic_cost S a y d v phi ha hphi)
    (add_le_add hLBound hHBound)

theorem finiteWeighted_total_upper_ledger {Iota : Type*} (S : Finset Iota)
    (a y : Iota -> Real) (d : Real) (hd : And (0 < d) (d < 1))
    (ha : forall i, Membership.mem S i -> 0 <= a i)
    (hMoment : Finset.sum S (fun i => a i * (y i) ^ 2) = Finset.sum S (fun i => a i * y i))
    (hK : 0 < thresholdSelectedMass d S a y) :
    let N := Finset.sum S a
    let K := thresholdSelectedMass d S a y
    let M := Finset.sum S (fun i => a i * y i)
    let v := thresholdModelHigh (N - K) K d
    And (1 <= v) (And (0 <= thresholdTotalUpper d N K - M)
      (Finset.sum S (fun i => a i * thresholdTotalPacket d v (y i)) =
        (2 * v - 1) * (thresholdTotalUpper d N K - M))) := by
  dsimp only
  let N := Finset.sum S a
  let K := thresholdSelectedMass d S a y
  let M := Finset.sum S (fun i => a i * y i)
  let J := N - K
  let v := thresholdModelHigh J K d
  have hKN : K <= N := by
    apply Finset.sum_le_sum
    intro i hi
    by_cases hCut : d <= y i
    case pos =>
      simpa only [momentRoundIndicator, ite_eq_left hCut, mul_one] using (_root_.le_refl (a i))
    case neg =>
      simpa only [momentRoundIndicator, ite_eq_right hCut, mul_zero] using ha i hi
  have hV : 1 <= v := thresholdModelHigh_bounds J K d (sub_nonneg.mpr hKN) hK
    (And.intro hd.1.le hd.2.le)
  have hBalance := thresholdModelHigh_moment J K d (sub_nonneg.mpr hKN) hK
    (And.intro hd.1.le hd.2.le)
  change J * d ^ 2 + K * v ^ 2 = J * d + K * v at hBalance
  have hN : N = J + K := by dsimp only [J]; ring
  have hIdentity : Finset.sum S (fun i => a i * thresholdTotalPacket d v (y i)) =
      (2 * v - 1) * (thresholdTotalUpper d N K - M) := by
    rw [finiteWeighted_total_packet_ledger S a y d v hMoment]
    change (1 - 2 * v) * M + v ^ 2 * N - (d - v) ^ 2 * J =
      (2 * v - 1) * (J * d + K * v - M)
    rw [hN]
    nlinarith only [hBalance]
  have hdv : d < v := lt_of_lt_of_le hd.2 hV
  have hNonneg := Finset.sum_nonneg
    (fun i hi => mul_nonneg (ha i hi) (thresholdTotalPacket_nonneg d v (y i) hdv))
  have hGap : 0 <= thresholdTotalUpper d N K - M := by
    by_contra hn
    have hBad := mul_neg_of_pos_of_neg
      (show 0 < 2 * v - 1 by linarith only [hV]) (lt_of_not_ge hn)
    rw [<- hIdentity] at hBad
    exact (not_lt_of_ge hNonneg) hBad
  exact And.intro hV (And.intro hGap hIdentity)

theorem finiteWeighted_threshold_total_stability {Iota : Type*} (S : Finset Iota)
    (a y : Iota -> Real) (d : Real) (hd : And (0 < d) (d < 1))
    (ha : forall i, Membership.mem S i -> 0 <= a i)
    (hMoment : Finset.sum S (fun i => a i * (y i) ^ 2) = Finset.sum S (fun i => a i * y i))
    (hK : 0 < thresholdSelectedMass d S a y) :
    let N := Finset.sum S a
    let K := thresholdSelectedMass d S a y
    let M := Finset.sum S (fun i => a i * y i)
    let v := thresholdModelHigh (N - K) K d
    let D := (2 * v - 1) * (thresholdTotalUpper d N K - M)
    And (2 * (v - d) * Finset.sum S (fun i => a i * thresholdTotalLowDistance d (y i)) <= D)
      (And (Finset.sum S (fun i => a i * thresholdTotalHighSquare d v (y i)) <= D)
        (forall phi : Real -> Real,
          (forall u w : Real, abs (phi u - phi w) <= abs (u - w)) ->
          abs (Finset.sum S (fun i => a i * phi (y i)) -
            thresholdTotalStatistic d v N K phi) <=
              D / (2 * (v - d)) + Real.sqrt (K * D))) := by
  dsimp only
  let N := Finset.sum S a
  let K := thresholdSelectedMass d S a y
  let v := thresholdModelHigh (N - K) K d
  have hLedger := finiteWeighted_total_upper_ledger S a y d hd ha hMoment hK
  have hdv : d < v := lt_of_lt_of_le hd.2 hLedger.1
  have hControl := finiteWeighted_total_layer_control S a y d v hdv ha
  rw [hLedger.2.2] at hControl
  refine And.intro hControl.2.2.2.1 (And.intro hControl.2.2.2.2 ?_)
  intro phi hphi
  have hBound := finiteWeighted_total_packet_stability S a y d v hdv ha hK phi hphi
  rw [hLedger.2.2] at hBound
  exact hBound
end PrimeFactorOscillations

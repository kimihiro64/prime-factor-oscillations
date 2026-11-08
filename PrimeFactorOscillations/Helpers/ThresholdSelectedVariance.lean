/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.ThresholdSingleLevelCost

/-! # Exact selected-variance budget at the fixed-total upper boundary -/

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 5000000

noncomputable section
namespace PrimeFactorOscillations

def thresholdSelectedMean {Iota : Type*} (d : Real) (S : Finset Iota)
    (a y : Iota -> Real) : Real :=
  Finset.sum S (fun i => a i * momentRoundIndicator d (y i) * y i) /
    thresholdSelectedMass d S a y

def thresholdSelectedVariance {Iota : Type*} (d : Real) (S : Finset Iota)
    (a y : Iota -> Real) : Real :=
  Finset.sum S (fun i => a i * momentRoundIndicator d (y i) *
    (y i - thresholdSelectedMean d S a y) ^ 2)

def thresholdTotalLowSquare (d y : Real) : Real :=
  (d - y) ^ 2 * (1 - momentRoundIndicator d y)

def thresholdVarianceBudget (d v K delta : Real) : Real :=
  (2 * v - 1) * delta - delta ^ 2 / K +
    (max (delta - K * (v - d)) 0) ^ 2 / K

theorem finiteWeighted_selected_parallel_axis {Iota : Type*} (S : Finset Iota)
    (a y : Iota -> Real) (d v : Real)
    (hK : 0 < thresholdSelectedMass d S a y) :
    Finset.sum S (fun i => a i * thresholdTotalHighSquare d v (y i)) =
      thresholdSelectedVariance d S a y +
        thresholdSelectedMass d S a y * (thresholdSelectedMean d S a y - v) ^ 2 := by
  let b := fun i => a i * momentRoundIndicator d (y i)
  let K := thresholdSelectedMass d S a y
  let H := Finset.sum S (fun i => b i * y i)
  have hMass : Finset.sum S b = K := rfl
  have hMu : thresholdSelectedMean d S a y = H / K := rfl
  have hV := finiteWeightedVariance_expansion S b y (H / K)
  have hQ := finiteWeightedVariance_expansion S b y v
  have hQeq : Finset.sum S (fun i => a i * thresholdTotalHighSquare d v (y i)) =
      Finset.sum S (fun i => b i * (y i - v) ^ 2) := by
    apply Finset.sum_congr rfl
    intro i _
    dsimp only [b, thresholdTotalHighSquare]
    ring
  rw [hQeq, hQ]
  change _ = Finset.sum S (fun i => b i * (y i - thresholdSelectedMean d S a y) ^ 2) +
    K * (thresholdSelectedMean d S a y - v) ^ 2
  rw [hMu, hV, hMass]
  change Finset.sum S (fun i => b i * (y i) ^ 2) - 2 * v * H + v ^ 2 * K =
    Finset.sum S (fun i => b i * (y i) ^ 2) - 2 * (H / K) * H +
      (H / K) ^ 2 * K + K * (H / K - v) ^ 2
  have hKn : Not (K = 0) := ne_of_gt hK
  field_simp [hKn]
  ring

theorem finiteWeighted_selected_mean_ledger {Iota : Type*} (S : Finset Iota)
    (a y : Iota -> Real) (d v : Real)
    (hK : 0 < thresholdSelectedMass d S a y) :
    let N := Finset.sum S a
    let K := thresholdSelectedMass d S a y
    let M := Finset.sum S (fun i => a i * y i)
    let L := Finset.sum S (fun i => a i * thresholdTotalLowDistance d (y i))
    (N - K) * d + K * v - M - L =
      K * (v - thresholdSelectedMean d S a y) := by
  dsimp only
  have hEach : forall i, a i * y i =
      d * (a i - a i * momentRoundIndicator d (y i)) -
        a i * thresholdTotalLowDistance d (y i) +
          a i * momentRoundIndicator d (y i) * y i := by
    intro i
    by_cases hCut : d <= y i
    case pos => simp [thresholdTotalLowDistance, momentRoundIndicator, hCut]
    case neg =>
      simp only [thresholdTotalLowDistance, momentRoundIndicator, ite_eq_right hCut,
        mul_zero, sub_zero, mul_one]
      ring
  have hM : Finset.sum S (fun i => a i * y i) =
      d * (Finset.sum S a - thresholdSelectedMass d S a y) -
        Finset.sum S (fun i => a i * thresholdTotalLowDistance d (y i)) +
          Finset.sum S (fun i => a i * momentRoundIndicator d (y i) * y i) := by
    calc
      _ = Finset.sum S (fun i => d * (a i - a i * momentRoundIndicator d (y i)) -
          a i * thresholdTotalLowDistance d (y i) +
            a i * momentRoundIndicator d (y i) * y i) := Finset.sum_congr rfl (fun i _ => hEach i)
      _ = _ := by
        rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, <- Finset.mul_sum,
          Finset.sum_sub_distrib]
        rfl
  rw [hM]
  dsimp only [thresholdSelectedMean]
  field_simp [ne_of_gt hK]
  ring

theorem finiteWeighted_selected_variance_ledger {Iota : Type*} (S : Finset Iota)
    (a y : Iota -> Real) (d : Real) (hd : And (0 < d) (d < 1))
    (ha : forall i, Membership.mem S i -> 0 <= a i)
    (hMoment : Finset.sum S (fun i => a i * (y i) ^ 2) = Finset.sum S (fun i => a i * y i))
    (hK : 0 < thresholdSelectedMass d S a y) :
    let N := Finset.sum S a
    let K := thresholdSelectedMass d S a y
    let M := Finset.sum S (fun i => a i * y i)
    let v := thresholdModelHigh (N - K) K d
    let delta := thresholdTotalUpper d N K - M
    let L := Finset.sum S (fun i => a i * thresholdTotalLowDistance d (y i))
    let Q := Finset.sum S (fun i => a i * thresholdTotalLowSquare d (y i))
    And (1 <= v) (And (0 <= delta) (And (0 <= L) (And (0 <= Q)
      ((2 * v - 1) * delta =
        thresholdSelectedVariance d S a y + Q + 2 * (v - d) * L +
          (L - delta) ^ 2 / K)))) := by
  dsimp only
  let N := Finset.sum S a
  let K := thresholdSelectedMass d S a y
  let M := Finset.sum S (fun i => a i * y i)
  let v := thresholdModelHigh (N - K) K d
  let delta := thresholdTotalUpper d N K - M
  let L := Finset.sum S (fun i => a i * thresholdTotalLowDistance d (y i))
  let Q := Finset.sum S (fun i => a i * thresholdTotalLowSquare d (y i))
  have hLedger := finiteWeighted_total_upper_ledger S a y d hd ha hMoment hK
  have hL := (finiteWeighted_total_layer_control S a y d v
    (lt_of_lt_of_le hd.2 hLedger.1) ha).2.1
  have hQ : 0 <= Q := by
    apply Finset.sum_nonneg
    intro i hi
    apply mul_nonneg (ha i hi)
    unfold thresholdTotalLowSquare
    by_cases hCut : d <= y i
    case pos => simp [momentRoundIndicator, hCut]
    case neg => simpa [momentRoundIndicator, hCut] using sq_nonneg (d - y i)
  have hLayers : Finset.sum S (fun i => a i * thresholdTotalPacket d v (y i)) =
      Q + 2 * (v - d) * L +
        Finset.sum S (fun i => a i * thresholdTotalHighSquare d v (y i)) := by
    calc
      _ = Finset.sum S (fun i => a i * thresholdTotalLowSquare d (y i) +
          2 * (v - d) * (a i * thresholdTotalLowDistance d (y i)) +
            a i * thresholdTotalHighSquare d v (y i)) := by
        apply Finset.sum_congr rfl
        intro i _
        rw [thresholdTotalPacket_layers]
        dsimp only [thresholdTotalLowSquare]
        ring
      _ = _ := by rw [Finset.sum_add_distrib, Finset.sum_add_distrib, <- Finset.mul_sum]
  have hMean := finiteWeighted_selected_mean_ledger S a y d v hK
  change delta - L = K * (v - thresholdSelectedMean d S a y) at hMean
  have hShift : K * (thresholdSelectedMean d S a y - v) ^ 2 = (L - delta) ^ 2 / K := by
    have hDiff : L - delta = K * (thresholdSelectedMean d S a y - v) := by
      linarith only [hMean]
    rw [hDiff]
    field_simp [ne_of_gt hK]
  have hExact := hLedger.2.2
  rw [hLayers, finiteWeighted_selected_parallel_axis S a y d v hK] at hExact
  change _ = (2 * v - 1) * delta at hExact
  refine And.intro hLedger.1 (And.intro hLedger.2.1
    (And.intro hL (And.intro hQ ?_)))
  rw [hShift] at hExact
  linarith only [hExact]

theorem thresholdVarianceBudget_from_ledger (d v K delta L Q V : Real)
    (hK : 0 < K) (hL : 0 <= L) (hQ : 0 <= Q)
    (hLedger : (2 * v - 1) * delta = V + Q + 2 * (v - d) * L + (L - delta) ^ 2 / K) :
    V <= thresholdVarianceBudget d v K delta := by
  let t := delta - K * (v - d)
  have hQuad : -L ^ 2 + 2 * t * L <= (max t 0) ^ 2 := by
    by_cases ht : 0 <= t
    case pos =>
      rw [max_eq_left ht]
      nlinarith only [sq_nonneg (L - t)]
    case neg =>
      rw [max_eq_right (le_of_not_ge ht)]
      have hProd := mul_nonpos_of_nonpos_of_nonneg (le_of_not_ge ht) hL
      nlinarith only [sq_nonneg L, hProd]
  have hScaled := congrArg (fun z : Real => K * z) hLedger
  have hDen : K * ((L - delta) ^ 2 / K) = (L - delta) ^ 2 := by
    field_simp [ne_of_gt hK]
  have hQK := mul_nonneg hK.le hQ
  have hTarget : K * thresholdVarianceBudget d v K delta =
      K * ((2 * v - 1) * delta) - delta ^ 2 + (max t 0) ^ 2 := by
    dsimp only [thresholdVarianceBudget, t]
    field_simp [ne_of_gt hK]
  have hBound : K * V <= K * thresholdVarianceBudget d v K delta := by
    rw [hTarget]
    dsimp only [t] at hQuad
    nlinarith only [hScaled, hDen, hQuad, hQK]
  by_contra hn
  have hp := mul_pos hK (sub_pos.mpr (lt_of_not_ge hn))
  nlinarith only [hp, hBound]

theorem finiteWeighted_selected_variance_budget {Iota : Type*} (S : Finset Iota)
    (a y : Iota -> Real) (d : Real) (hd : And (0 < d) (d < 1))
    (ha : forall i, Membership.mem S i -> 0 <= a i)
    (hMoment : Finset.sum S (fun i => a i * (y i) ^ 2) = Finset.sum S (fun i => a i * y i))
    (hK : 0 < thresholdSelectedMass d S a y) :
    let N := Finset.sum S a
    let K := thresholdSelectedMass d S a y
    let M := Finset.sum S (fun i => a i * y i)
    let v := thresholdModelHigh (N - K) K d
    thresholdSelectedVariance d S a y <=
      thresholdVarianceBudget d v K (thresholdTotalUpper d N K - M) := by
  dsimp only
  have h := finiteWeighted_selected_variance_ledger S a y d hd ha hMoment hK
  exact thresholdVarianceBudget_from_ledger _ _ _ _ _ _ _ hK h.2.2.1 h.2.2.2.1 h.2.2.2.2

end PrimeFactorOscillations

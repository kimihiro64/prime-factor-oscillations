/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.NegativeThresholdTransport

/-! # Exact rational splitting of the negative-root extremizer -/

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 5000000

noncomputable section
namespace PrimeFactorOscillations

private theorem negativeSplit_first_identity (d z K B q : Real) :
    let v := 1 + q ^ 2
    let u := (z - d) * q ^ 2 / v
    let r := (z - d) * q / v
    let b := B * v
    (K - b) * d + (b / 2) * (z - u - r) + (b / 2) * (z - u + r) =
      (K - B) * d + B * z := by
  dsimp only
  have hv : Not (1 + q ^ 2 = 0) := ne_of_gt (by nlinarith only [sq_nonneg q])
  field_simp [hv]
  ring

private theorem negativeSplit_second_identity (d z K B q : Real) :
    let v := 1 + q ^ 2
    let u := (z - d) * q ^ 2 / v
    let r := (z - d) * q / v
    let b := B * v
    (K - b) * d ^ 2 + (b / 2) * (z - u - r) ^ 2 + (b / 2) * (z - u + r) ^ 2 =
      (K - B) * d ^ 2 + B * z ^ 2 := by
  dsimp only
  have hv : Not (1 + q ^ 2 = 0) := ne_of_gt (by nlinarith only [sq_nonneg q])
  field_simp [hv]
  ring

private theorem negativeSplit_energy_identity (d z K B q : Real) :
    let v := 1 + q ^ 2
    let u := (z - d) * q ^ 2 / v
    let r := (z - d) * q / v
    let b := B * v
    (K - b) * d * (d - 1) ^ 2 +
        (b / 2) * (z - u - r) * (z - u - r - 1) ^ 2 +
        (b / 2) * (z - u + r) * (z - u + r - 1) ^ 2 =
      (K - B) * d * (d - 1) ^ 2 + B * z * (z - 1) ^ 2 +
        B * (z - d) ^ 3 * q ^ 2 * (1 - q ^ 2) / (1 + q ^ 2) ^ 2 := by
  dsimp only
  have hv : Not (1 + q ^ 2 = 0) := ne_of_gt (by nlinarith only [sq_nonneg q])
  field_simp [hv]
  ring


def thresholdNegativeSplitCoords (d M K q : Real) (i : Fin 4) : Real :=
  let z := thresholdNegativeRoot d M K
  let u := (z - d) * q ^ 2 / (1 + q ^ 2)
  let r := (z - d) * q / (1 + q ^ 2)
  if i.val = 0 then 0 else if i.val = 1 then d else if i.val = 2 then z - u - r else z - u + r

def thresholdNegativeSplitWeights (d M K N q : Real) (i : Fin 4) : Real :=
  let z := thresholdNegativeRoot d M K
  let b := (M - d * K) / (z - d) * (1 + q ^ 2)
  if i.val = 0 then N - K else if i.val = 1 then K - b else b / 2

def thresholdNegativeSplitWindow (d M K : Real) : Real :=
  let z := thresholdNegativeRoot d M K
  min (1 / 4) (((K * z - M) / (z - d)) / (2 * K))

theorem thresholdNegativeSplit_sum (d M K N q : Real) (f : Real -> Real) :
    let z := thresholdNegativeRoot d M K
    let u := (z - d) * q ^ 2 / (1 + q ^ 2)
    let r := (z - d) * q / (1 + q ^ 2)
    let b := (M - d * K) / (z - d) * (1 + q ^ 2)
    Finset.sum Finset.univ (fun i => thresholdNegativeSplitWeights d M K N q i *
      f (thresholdNegativeSplitCoords d M K q i)) =
      (N - K) * f 0 + (K - b) * f d + (b / 2) * f (z - u - r) + (b / 2) * f (z - u + r) := by
  dsimp only
  norm_num [Fin.sum_univ_succ, thresholdNegativeSplitWeights, thresholdNegativeSplitCoords, add_assoc]

theorem thresholdNegativeSplit_constants (d M K : Real)
    (hd : And (0 < d) (d < 1)) (hM : 0 < M) (hMK : M < K) (hDomain : d * K < M) :
    let z := thresholdNegativeRoot d M K
    let B := (M - d * K) / (z - d)
    And (0 < z - d) (And (0 < B) (And (0 < K - B) (0 < thresholdNegativeSplitWindow d M K))) := by
  dsimp only
  let z := thresholdNegativeRoot d M K
  let B := (M - d * K) / (z - d)
  have hK : 0 < K := lt_trans hM hMK
  have hz : 1 <= z := thresholdNegativeRoot_ge_one d M K hd.1 hDomain hMK.le
  have hg : 0 < z - d := by linarith only [hd.2, hz]
  have hB : 0 < B := div_pos (sub_pos.mpr hDomain) hg
  have hp := mul_nonneg hK.le (sub_nonneg.mpr hz)
  have hNum : 0 < K * z - M := by nlinarith only [hp, hMK]
  have hAlpha : 0 < (K * z - M) / (z - d) := div_pos hNum hg
  have hIdentity : K - B = (K * z - M) / (z - d) := by
    dsimp [B]
    field_simp [hg.ne']
    ring
  have hLow : 0 < K - B := by rw [hIdentity]; exact hAlpha
  have hWindow : 0 < thresholdNegativeSplitWindow d M K := by
    unfold thresholdNegativeSplitWindow
    exact lt_min (by norm_num) (div_pos hAlpha (by linarith only [hK]))
  exact And.intro hg (And.intro hB (And.intro hLow hWindow))

theorem thresholdNegativeSplit_admissible (d M K N q : Real)
    (hd : And (0 < d) (d < 1)) (hM : 0 < M) (hMK : M < K) (hDomain : d * K < M)
    (hN : K <= N) (hq : And (0 < q) (q <= thresholdNegativeSplitWindow d M K)) :
    And (forall i, 0 <= thresholdNegativeSplitWeights d M K N q i)
      (And (forall i, 0 <= thresholdNegativeSplitCoords d M K q i)
        (And (Finset.sum Finset.univ (thresholdNegativeSplitWeights d M K N q) = N)
          (thresholdSelectedMass d Finset.univ (thresholdNegativeSplitWeights d M K N q)
            (thresholdNegativeSplitCoords d M K q) = K))) := by
  let z := thresholdNegativeRoot d M K
  let g := z - d
  let B := (M - d * K) / g
  let v := 1 + q ^ 2
  let u := g * q ^ 2 / v
  let r := g * q / v
  let b := B * v
  have hc := thresholdNegativeSplit_constants d M K hd hM hMK hDomain
  have hg : 0 < g := hc.1
  have hB : 0 < B := hc.2.1
  have hAlpha : 0 < K - B := hc.2.2.1
  have hK : 0 < K := lt_trans hM hMK
  have hv : 0 < v := by dsimp [v]; nlinarith only [sq_nonneg q]
  have hqFull : q <= min (1 / 4) (((K * z - M) / g) / (2 * K)) := hq.2
  have hSmall : q <= 1 / 4 := le_trans hqFull (min_le_left _ _)
  have hqOne : q <= 1 := by linarith only [hSmall]
  have hQA := le_trans hqFull (min_le_right _ _)
  have hMultiply := mul_le_mul_of_nonneg_right hQA (show 0 <= 2 * K by linarith only [hK])
  have hCancel : (((K * z - M) / g) / (2 * K)) * (2 * K) = (K * z - M) / g := by
    field_simp [hK.ne']
  have hIdentity : (K * z - M) / g = K - B := by
    have hGap : Not (z - d = 0) := hg.ne'
    dsimp [g, B]
    field_simp [hGap]
    ring
  rw [hCancel, hIdentity] at hMultiply
  have hQSquare : q ^ 2 <= q := by
    have hp := mul_nonneg hq.1.le (sub_nonneg.mpr hqOne)
    nlinarith only [hp]
  have hBSquare := mul_le_mul_of_nonneg_left hQSquare hB.le
  have hBK := mul_le_mul_of_nonneg_right (show B <= K by linarith only [hAlpha]) hq.1.le
  have hLowWeight : 0 < K - b := by
    dsimp [b, v]
    nlinarith only [hBSquare, hBK, hMultiply, hAlpha]
  have hb : 0 < b := mul_pos hB hv
  have hr : 0 <= r := div_nonneg (mul_nonneg hg.le hq.1.le) hv.le
  have hLow : d <= z - u - r := by
    have hMargin : 0 <= g * (1 - q) / v :=
      div_nonneg (mul_nonneg hg.le (sub_nonneg.mpr hqOne)) hv.le
    have hId : z - u - r - d = g * (1 - q) / v := by
      have hV : Not (1 + q ^ 2 = 0) := hv.ne'
      dsimp [u, r, v, g]
      field_simp [hV]
      ring
    rw [<- hId] at hMargin
    linarith only [hMargin]
  have hHigh : d <= z - u + r := by linarith only [hLow, hr]
  have hWeights : forall i, 0 <= thresholdNegativeSplitWeights d M K N q i := by
    intro i
    by_cases h0 : i.val = 0
    case pos => simpa only [thresholdNegativeSplitWeights, ite_eq_left h0] using sub_nonneg.mpr hN
    case neg =>
      by_cases h1 : i.val = 1
      case pos => simpa only [thresholdNegativeSplitWeights, ite_eq_right h0, ite_eq_left h1] using hLowWeight.le
      case neg => simpa only [thresholdNegativeSplitWeights, ite_eq_right h0, ite_eq_right h1] using (div_pos hb (show (0 : Real) < 2 by norm_num)).le
  have hCoords : forall i, 0 <= thresholdNegativeSplitCoords d M K q i := by
    intro i
    by_cases h0 : i.val = 0
    case pos => simp only [thresholdNegativeSplitCoords, ite_eq_left h0]; exact le_refl 0
    case neg =>
      by_cases h1 : i.val = 1
      case pos => simpa only [thresholdNegativeSplitCoords, ite_eq_right h0, ite_eq_left h1] using hd.1.le
      case neg =>
        by_cases h2 : i.val = 2
        case pos => simpa only [thresholdNegativeSplitCoords, ite_eq_right h0, ite_eq_right h1, ite_eq_left h2] using le_trans hd.1.le hLow
        case neg => simpa only [thresholdNegativeSplitCoords, ite_eq_right h0, ite_eq_right h1, ite_eq_right h2] using le_trans hd.1.le hHigh
  have hTotal : Finset.sum Finset.univ (thresholdNegativeSplitWeights d M K N q) = N := by
    have hs := thresholdNegativeSplit_sum d M K N q (fun _ => 1)
    simp only [mul_one] at hs
    linarith only [hs]
  have hSelected : thresholdSelectedMass d Finset.univ (thresholdNegativeSplitWeights d M K N q)
      (thresholdNegativeSplitCoords d M K q) = K := by
    have hs := thresholdNegativeSplit_sum d M K N q (momentRoundIndicator d)
    change Finset.sum Finset.univ (fun i => thresholdNegativeSplitWeights d M K N q i *
      momentRoundIndicator d (thresholdNegativeSplitCoords d M K q i)) =
        (N - K) * momentRoundIndicator d 0 + (K - b) * momentRoundIndicator d d +
          (b / 2) * momentRoundIndicator d (z - u - r) +
          (b / 2) * momentRoundIndicator d (z - u + r) at hs
    have hI0 : momentRoundIndicator d 0 = 0 := ite_eq_right (not_le.mpr hd.1)
    have hId : momentRoundIndicator d d = 1 := ite_eq_left le_rfl
    have hIL : momentRoundIndicator d (z - u - r) = 1 := ite_eq_left hLow
    have hIH : momentRoundIndicator d (z - u + r) = 1 := ite_eq_left hHigh
    rw [hI0, hId, hIL, hIH] at hs
    simp only [mul_zero, mul_one, zero_add] at hs
    unfold thresholdSelectedMass
    linarith only [hs]

  exact And.intro hWeights (And.intro hCoords (And.intro hTotal hSelected))


theorem thresholdNegativeSplit_moments (d M K N q : Real)
    (hd : And (0 < d) (d < 1)) (hM : 0 < M) (hMK : M < K) (hDomain : d * K < M) :
    let a := thresholdNegativeSplitWeights d M K N q
    let y := thresholdNegativeSplitCoords d M K q
    let g := thresholdNegativeRoot d M K - d
    And (Finset.sum Finset.univ (fun i => a i * y i) = M)
      (And (Finset.sum Finset.univ (fun i => a i * (y i) ^ 2) = M)
        (Finset.sum Finset.univ (fun i => a i * y i * (y i - 1) ^ 2) =
          thresholdNegativeCost d M K +
            (M - d * K) * g ^ 2 * q ^ 2 * (1 - q ^ 2) / (1 + q ^ 2) ^ 2)) := by
  dsimp only
  let z := thresholdNegativeRoot d M K
  let g := z - d
  let B := (M - d * K) / g
  let v := 1 + q ^ 2
  let u := g * q ^ 2 / v
  let r := g * q / v
  let b := B * v
  have hg : 0 < g := (thresholdNegativeSplit_constants d M K hd hM hMK hDomain).1
  have hGap : Not (z - d = 0) := hg.ne'
  have hAlpha : (K * z - M) / g = K - B := by
    dsimp [B, g]
    field_simp [hGap]
    ring
  have hBase := thresholdNegativeCanonical_moments d M K hd hDomain hMK.le
  change And ((K * z - M) / g + B = K)
    (And (((K * z - M) / g) * d + B * z = M)
      (And (((K * z - M) / g) * d ^ 2 + B * z ^ 2 = M)
        (((K * z - M) / g) * d * (d - 1) ^ 2 + B * z * (z - 1) ^ 2 =
          thresholdNegativeCost d M K))) at hBase
  rw [hAlpha] at hBase
  have hFirst := negativeSplit_first_identity d z K B q
  have hSecond := negativeSplit_second_identity d z K B q
  have hEnergy := negativeSplit_energy_identity d z K B q
  change (K - b) * d + (b / 2) * (z - u - r) + (b / 2) * (z - u + r) =
    (K - B) * d + B * z at hFirst
  change (K - b) * d ^ 2 + (b / 2) * (z - u - r) ^ 2 + (b / 2) * (z - u + r) ^ 2 =
    (K - B) * d ^ 2 + B * z ^ 2 at hSecond
  change (K - b) * d * (d - 1) ^ 2 + (b / 2) * (z - u - r) * (z - u - r - 1) ^ 2 +
    (b / 2) * (z - u + r) * (z - u + r - 1) ^ 2 =
      (K - B) * d * (d - 1) ^ 2 + B * z * (z - 1) ^ 2 +
        B * g ^ 3 * q ^ 2 * (1 - q ^ 2) / (1 + q ^ 2) ^ 2 at hEnergy
  have hScale : B * g ^ 3 = (M - d * K) * g ^ 2 := by
    dsimp [B]
    field_simp [hg.ne']
  rw [hBase.2.2.2, hScale] at hEnergy
  have hS1 := thresholdNegativeSplit_sum d M K N q (fun y => y)
  have hS2 := thresholdNegativeSplit_sum d M K N q (fun y => y ^ 2)
  have hSE := thresholdNegativeSplit_sum d M K N q (fun y => y * (y - 1) ^ 2)
  change Finset.sum Finset.univ (fun i => thresholdNegativeSplitWeights d M K N q i *
    thresholdNegativeSplitCoords d M K q i) =
      (N - K) * 0 + (K - b) * d + (b / 2) * (z - u - r) + (b / 2) * (z - u + r) at hS1
  change Finset.sum Finset.univ (fun i => thresholdNegativeSplitWeights d M K N q i *
    (thresholdNegativeSplitCoords d M K q i) ^ 2) =
      (N - K) * 0 ^ 2 + (K - b) * d ^ 2 +
        (b / 2) * (z - u - r) ^ 2 + (b / 2) * (z - u + r) ^ 2 at hS2
  change Finset.sum Finset.univ (fun i => thresholdNegativeSplitWeights d M K N q i *
    (thresholdNegativeSplitCoords d M K q i * (thresholdNegativeSplitCoords d M K q i - 1) ^ 2)) =
      (N - K) * (0 * (0 - 1) ^ 2) + (K - b) * (d * (d - 1) ^ 2) +
        (b / 2) * ((z - u - r) * (z - u - r - 1) ^ 2) +
        (b / 2) * ((z - u + r) * (z - u + r - 1) ^ 2) at hSE
  simp only [mul_zero, zero_add] at hS1
  norm_num at hS2
  simp only [zero_mul, mul_zero, zero_add] at hSE
  rw [hFirst, hBase.2.1] at hS1
  rw [hSecond, hBase.2.2.1] at hS2
  have hSE' : Finset.sum Finset.univ (fun i => thresholdNegativeSplitWeights d M K N q i *
      thresholdNegativeSplitCoords d M K q i * (thresholdNegativeSplitCoords d M K q i - 1) ^ 2) =
      (K - b) * d * (d - 1) ^ 2 +
        (b / 2) * (z - u - r) * (z - u - r - 1) ^ 2 +
        (b / 2) * (z - u + r) * (z - u + r - 1) ^ 2 := by
    calc
      _ = Finset.sum Finset.univ (fun i => thresholdNegativeSplitWeights d M K N q i *
          (thresholdNegativeSplitCoords d M K q i * (thresholdNegativeSplitCoords d M K q i - 1) ^ 2)) := by
        apply Finset.sum_congr rfl
        intro i _
        ring
      _ = _ := hSE
      _ = _ := by ring
  rw [hEnergy] at hSE'
  exact And.intro hS1 (And.intro hS2 hSE')

theorem thresholdNegativeSplit_statistic (d M K N q : Real)
    (hd : And (0 < d) (d < 1)) (hM : 0 < M) (hMK : M < K) (hDomain : d * K < M)
    (hq : And (0 <= q) (q <= 1)) :
    let z := thresholdNegativeRoot d M K
    Finset.sum Finset.univ (fun i => thresholdNegativeSplitWeights d M K N q i *
      abs (thresholdNegativeSplitCoords d M K q i - z)) -
      negativeThresholdCanonicalStatistic d z M K N (fun y => abs (y - z)) =
        (M - d * K) * q * (1 - q) := by
  dsimp only
  let z := thresholdNegativeRoot d M K
  let g := z - d
  let B := (M - d * K) / g
  let v := 1 + q ^ 2
  let u := g * q ^ 2 / v
  let r := g * q / v
  let b := B * v
  have hg : 0 < g := (thresholdNegativeSplit_constants d M K hd hM hMK hDomain).1
  have hv : 0 < v := by dsimp [v]; nlinarith only [sq_nonneg q]
  have hGap : Not (z - d = 0) := hg.ne'
  have hV : Not (1 + q ^ 2 = 0) := hv.ne'
  have hu : 0 <= u := div_nonneg (mul_nonneg hg.le (sq_nonneg q)) hv.le
  have hr : 0 <= r := div_nonneg (mul_nonneg hg.le hq.1) hv.le
  have hRU : 0 <= r - u := by
    have hh := div_nonneg (mul_nonneg (mul_nonneg hg.le hq.1) (sub_nonneg.mpr hq.2)) hv.le
    have hId : r - u = g * q * (1 - q) / v := by
      dsimp [r, u, v]
      field_simp [hV]
    rw [<- hId] at hh
    exact hh
  have hAbsD : abs (d - z) = g := by
    have hId : d - z = -g := by dsimp [g]; ring
    rw [hId, abs_neg, abs_of_pos hg]
  have hAbsL : abs (z - u - r - z) = u + r := by
    have hId : z - u - r - z = -(u + r) := by ring
    rw [hId, abs_neg, abs_of_nonneg (add_nonneg hu hr)]
  have hAbsH : abs (z - u + r - z) = r - u := by
    have hId : z - u + r - z = r - u := by ring
    rw [hId, abs_of_nonneg hRU]
  have hAlpha : (K * z - M) / g = K - B := by
    dsimp [B, g]
    field_simp [hGap]
    ring
  have hSum := thresholdNegativeSplit_sum d M K N q (fun y => abs (y - z))
  change Finset.sum Finset.univ (fun i => thresholdNegativeSplitWeights d M K N q i *
    abs (thresholdNegativeSplitCoords d M K q i - z)) =
      (N - K) * abs (0 - z) + (K - b) * abs (d - z) +
        (b / 2) * abs (z - u - r - z) + (b / 2) * abs (z - u + r - z) at hSum
  rw [hAbsD, hAbsL, hAbsH] at hSum
  have hCanonical := negativeThresholdCanonicalStatistic_three_atoms d z M K N
    (fun y => abs (y - z)) hGap
  change negativeThresholdCanonicalStatistic d z M K N (fun y => abs (y - z)) =
    (N - K) * abs (0 - z) + ((K * z - M) / g) * abs (d - z) + B * abs (z - z) at hCanonical
  rw [hAlpha, hAbsD] at hCanonical
  simp only [sub_self, abs_zero, mul_zero, add_zero] at hCanonical
  rw [hSum, hCanonical]
  dsimp [b, B, u, r, v, g]
  field_simp [hGap, hV]
  ring

end PrimeFactorOscillations

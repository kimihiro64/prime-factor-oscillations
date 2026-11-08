/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.ThresholdNonlinearRigidity
import PrimeFactorOscillations.Helpers.ThresholdTotalPackets

/-! # Quantitative Lipschitz inverse stability of threshold moment profiles -/

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 5000000

noncomputable section
namespace PrimeFactorOscillations

def thresholdAffineResidual (d z : Real) (phi : Real -> Real) (y : Real) : Real :=
  phi y - phi 0 - y * ((phi d - phi 0) / d) -
    momentRoundIndicator d y * (phi z - phi 0 - z * ((phi d - phi 0) / d))

private theorem affine_difference_lipschitz (d : Real) (phi : Real -> Real)
    (hd : 0 < d) (hphi : forall u v : Real, abs (phi u - phi v) <= abs (u - v))
    (u v : Real) :
    abs ((phi u - phi v) - (u - v) * ((phi d - phi 0) / d)) <=
      2 * abs (u - v) := by
  have hSlope : abs ((phi d - phi 0) / d) <= 1 := by
    rw [abs_div, abs_of_pos hd]
    apply (div_le_one hd).mpr
    simpa only [sub_zero, abs_of_pos hd] using hphi d 0
  calc
    _ <= abs (phi u - phi v) + abs ((u - v) * ((phi d - phi 0) / d)) :=
      abs_sub _ _
    _ = abs (phi u - phi v) + abs (u - v) * abs ((phi d - phi 0) / d) := by
      rw [abs_mul]
    _ <= abs (u - v) + abs (u - v) * 1 :=
      add_le_add (hphi u v) (mul_le_mul_of_nonneg_left hSlope (abs_nonneg _))
    _ = _ := by ring

theorem thresholdAffineResidual_bound (d z y : Real) (phi : Real -> Real)
    (hd : 0 < d) (hphi : forall u v : Real, abs (phi u - phi v) <= abs (u - v)) :
    abs (thresholdAffineResidual d z phi y) <=
      2 * abs (y - z * momentRoundIndicator d y - d * thresholdBandIndicator d y) := by
  classical
  by_cases hCut : d <= y
  case pos =>
    have hBand : thresholdBandIndicator d y = 0 :=
      ite_eq_right (fun h => (not_lt.mpr hCut) h.2)
    have hRes : thresholdAffineResidual d z phi y =
        (phi y - phi z) - (y - z) * ((phi d - phi 0) / d) := by
      simp only [thresholdAffineResidual, momentRoundIndicator, ite_eq_left hCut, one_mul]
      ring
    rw [hRes, hBand]
    simp only [momentRoundIndicator, ite_eq_left hCut, mul_one, mul_zero, sub_zero]
    exact affine_difference_lipschitz d phi hd hphi y z
  case neg =>
    have hLow : y < d := lt_of_not_ge hCut
    by_cases hHalf : d / 2 <= y
    case pos =>
      have hBand : thresholdBandIndicator d y = 1 := ite_eq_left (And.intro hHalf hLow)
      have hRes : thresholdAffineResidual d z phi y =
          (phi y - phi d) - (y - d) * ((phi d - phi 0) / d) := by
        simp only [thresholdAffineResidual, momentRoundIndicator, ite_eq_right hCut, zero_mul, sub_zero]
        field_simp [hd.ne']
        ring
      rw [hRes, hBand]
      simp only [momentRoundIndicator, ite_eq_right hCut, mul_zero, mul_one, sub_zero]
      exact affine_difference_lipschitz d phi hd hphi y d
    case neg =>
      have hBand : thresholdBandIndicator d y = 0 := ite_eq_right (fun h => hHalf h.1)
      have hRes : thresholdAffineResidual d z phi y =
          (phi y - phi 0) - (y - 0) * ((phi d - phi 0) / d) := by
        simp only [thresholdAffineResidual, momentRoundIndicator, ite_eq_right hCut, zero_mul, sub_zero]
      rw [hRes, hBand]
      simp only [momentRoundIndicator, ite_eq_right hCut, mul_zero, sub_zero]
      simpa only [sub_zero] using affine_difference_lipschitz d phi hd hphi y 0


def thresholdCanonicalStatistic (d z M K N : Real) (phi : Real -> Real) : Real :=
  N * phi 0 + ((M - K * z) / d) * (phi d - phi 0) + K * (phi z - phi 0)

theorem thresholdAffineResidual_tilt (d z y l : Real) (phi : Real -> Real)
    (hd : And (0 < d) (d < 1)) (hz : 1 <= z) (hy : 0 <= y)
    (hl : And (0 <= l) (l <= thresholdBandSlope d z))
    (hphi : forall u v : Real, abs (phi u - phi v) <= abs (u - v)) :
    l * abs (thresholdAffineResidual d z phi y) <=
      2 * thresholdPositivePacket d z y +
        l ^ 2 / (2 * thresholdBandCurvature d z) * momentRoundIndicator d y := by
  let t := y - z * momentRoundIndicator d y - d * thresholdBandIndicator d y
  have hAbs : l * abs t <= thresholdPositivePacket d z y +
      l ^ 2 / (4 * thresholdBandCurvature d z) * momentRoundIndicator d y := by
    by_cases hSign : 0 <= t
    case pos =>
      have hh := thresholdBand_tilted_packet d z y l 1 hd hz hy hl (Or.inl rfl)
      change 0 <= thresholdPositivePacket d z y +
        l ^ 2 / (4 * thresholdBandCurvature d z) * momentRoundIndicator d y - l * 1 * t at hh
      rw [abs_of_nonneg hSign]
      linarith only [hh]
    case neg =>
      have hh := thresholdBand_tilted_packet d z y l (-1) hd hz hy hl (Or.inr rfl)
      change 0 <= thresholdPositivePacket d z y +
        l ^ 2 / (4 * thresholdBandCurvature d z) * momentRoundIndicator d y - l * (-1) * t at hh
      rw [abs_of_nonpos (le_of_not_ge hSign)]
      linarith only [hh]
  have hR := mul_le_mul_of_nonneg_left (thresholdAffineResidual_bound d z y phi hd.1 hphi) hl.1
  have hC := (thresholdBand_constants_pos d z hd hz).2
  calc
    _ <= l * (2 * abs t) := hR
    _ <= 2 * (thresholdPositivePacket d z y +
        l ^ 2 / (4 * thresholdBandCurvature d z) * momentRoundIndicator d y) := by
      linarith only [hAbs]
    _ = _ := by field_simp [hC.ne']; ring

theorem finiteWeightedThreshold_residual_sum {Iota : Type*} (S : Finset Iota)
    (a y : Iota -> Real) (d z : Real) (phi : Real -> Real) :
    Finset.sum S (fun i => a i * thresholdAffineResidual d z phi (y i)) =
      Finset.sum S (fun i => a i * phi (y i)) -
        thresholdCanonicalStatistic d z (Finset.sum S (fun i => a i * y i))
          (thresholdSelectedMass d S a y) (Finset.sum S a) phi := by
  have hExpand : Finset.sum S (fun i => a i * thresholdAffineResidual d z phi (y i)) =
      Finset.sum S (fun i => a i * phi (y i) - phi 0 * a i -
        ((phi d - phi 0) / d) * (a i * y i) -
        (phi z - phi 0 - z * ((phi d - phi 0) / d)) *
          (a i * momentRoundIndicator d (y i))) := by
    apply Finset.sum_congr rfl
    intro i _
    unfold thresholdAffineResidual
    ring
  rw [hExpand]
  simp only [Finset.sum_sub_distrib, <- Finset.mul_sum]
  unfold thresholdCanonicalStatistic thresholdSelectedMass
  ring

theorem finiteWeightedThreshold_lipschitz_packet {Iota : Type*} (S : Finset Iota)
    (a y : Iota -> Real) (d z l : Real) (phi : Real -> Real)
    (hd : And (0 < d) (d < 1)) (hz : 1 <= z)
    (ha : forall i, Membership.mem S i -> 0 <= a i)
    (hy : forall i, Membership.mem S i -> 0 <= y i)
    (hl : And (0 <= l) (l <= thresholdBandSlope d z))
    (hphi : forall u v : Real, abs (phi u - phi v) <= abs (u - v)) :
    l * abs (Finset.sum S (fun i => a i * thresholdAffineResidual d z phi (y i))) <=
      2 * Finset.sum S (fun i => a i * thresholdPositivePacket d z (y i)) +
        thresholdSelectedMass d S a y * l ^ 2 / (2 * thresholdBandCurvature d z) := by
  have hAbs : abs (Finset.sum S (fun i => a i * thresholdAffineResidual d z phi (y i))) <=
      Finset.sum S (fun i => a i * abs (thresholdAffineResidual d z phi (y i))) := by
    calc
      _ <= Finset.sum S (fun i => abs (a i * thresholdAffineResidual d z phi (y i))) :=
        Finset.abs_sum_le_sum_abs _ _
      _ = _ := by
        apply Finset.sum_congr rfl
        intro i hi
        rw [abs_mul, abs_of_nonneg (ha i hi)]
  have hEach : forall i, Membership.mem S i ->
      a i * (l * abs (thresholdAffineResidual d z phi (y i))) <=
        a i * (2 * thresholdPositivePacket d z (y i) +
          l ^ 2 / (2 * thresholdBandCurvature d z) * momentRoundIndicator d (y i)) := by
    intro i hi
    exact mul_le_mul_of_nonneg_left
      (thresholdAffineResidual_tilt d z (y i) l phi hd hz (hy i hi) hl hphi) (ha i hi)
  have hSum := Finset.sum_le_sum hEach
  have hLeft : Finset.sum S (fun i => a i * (l * abs (thresholdAffineResidual d z phi (y i)))) =
      l * Finset.sum S (fun i => a i * abs (thresholdAffineResidual d z phi (y i))) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    ring
  have hRight : Finset.sum S (fun i => a i * (2 * thresholdPositivePacket d z (y i) +
      l ^ 2 / (2 * thresholdBandCurvature d z) * momentRoundIndicator d (y i))) =
      2 * Finset.sum S (fun i => a i * thresholdPositivePacket d z (y i)) +
        thresholdSelectedMass d S a y * l ^ 2 / (2 * thresholdBandCurvature d z) := by
    calc
      _ = Finset.sum S (fun i => 2 * (a i * thresholdPositivePacket d z (y i)) +
          (l ^ 2 / (2 * thresholdBandCurvature d z)) *
            (a i * momentRoundIndicator d (y i))) := by
        apply Finset.sum_congr rfl
        intro i _
        ring
      _ = 2 * Finset.sum S (fun i => a i * thresholdPositivePacket d z (y i)) +
          (l ^ 2 / (2 * thresholdBandCurvature d z)) *
            Finset.sum S (fun i => a i * momentRoundIndicator d (y i)) := by
        rw [Finset.sum_add_distrib, <- Finset.mul_sum, <- Finset.mul_sum]
      _ = _ := by unfold thresholdSelectedMass; ring
  rw [hLeft, hRight] at hSum
  exact le_trans (mul_le_mul_of_nonneg_left hAbs hl.1) hSum

theorem finiteWeightedThreshold_lipschitz_stability {Iota : Type*} (S : Finset Iota)
    (a y : Iota -> Real) (d l : Real) (phi : Real -> Real)
    (hd : And (0 < d) (d < 1))
    (ha : forall i, Membership.mem S i -> 0 <= a i)
    (hy : forall i, Membership.mem S i -> 0 <= y i)
    (hMoment : Finset.sum S (fun i => a i * (y i) ^ 2) = Finset.sum S (fun i => a i * y i))
    (hMass : 0 < Finset.sum S (fun i => a i * y i))
    (hKM : thresholdSelectedMass d S a y <= Finset.sum S (fun i => a i * y i))
    (hl : And (0 <= l) (l <= thresholdBandSlope d
      (thresholdPositiveRoot d (Finset.sum S (fun i => a i * y i)) (thresholdSelectedMass d S a y))))
    (hphi : forall u v : Real, abs (phi u - phi v) <= abs (u - v)) :
    l * abs (Finset.sum S (fun i => a i * phi (y i)) -
      thresholdCanonicalStatistic d
        (thresholdPositiveRoot d (Finset.sum S (fun i => a i * y i)) (thresholdSelectedMass d S a y))
        (Finset.sum S (fun i => a i * y i)) (thresholdSelectedMass d S a y) (Finset.sum S a) phi) <=
      2 * (Finset.sum S (fun i => a i * y i * (y i - 1) ^ 2) -
        thresholdPositiveCost d (Finset.sum S (fun i => a i * y i)) (thresholdSelectedMass d S a y)) +
        thresholdSelectedMass d S a y * l ^ 2 / (2 * thresholdBandCurvature d
          (thresholdPositiveRoot d (Finset.sum S (fun i => a i * y i)) (thresholdSelectedMass d S a y))) := by
  let M := Finset.sum S (fun i => a i * y i)
  let K := thresholdSelectedMass d S a y
  let z := thresholdPositiveRoot d M K
  have hK := (finiteWeightedThreshold_domain S a y d hd.2 ha hy hMoment hMass).1
  have hz := (thresholdPositiveRoot_bounds d M K hd hMass hK hKM).2
  have hPacket := finiteWeightedThreshold_lipschitz_packet S a y d z l phi hd hz ha hy hl hphi
  rw [finiteWeightedThreshold_residual_sum] at hPacket
  have hDefect := finiteWeightedThreshold_exact_positive_defect S a y d hd ha hy hMoment hMass hKM
  change Finset.sum S (fun i => a i * thresholdPositivePacket d z (y i)) =
    Finset.sum S (fun i => a i * y i * (y i - 1) ^ 2) - thresholdPositiveCost d M K at hDefect
  rw [hDefect] at hPacket
  exact hPacket


theorem finiteWeightedThreshold_canonical_weights {Iota : Type*} (S : Finset Iota)
    (a y : Iota -> Real) (d : Real) (hd : And (0 < d) (d < 1))
    (ha : forall i, Membership.mem S i -> 0 <= a i)
    (hy : forall i, Membership.mem S i -> 0 <= y i)
    (hMoment : Finset.sum S (fun i => a i * (y i) ^ 2) = Finset.sum S (fun i => a i * y i))
    (hMass : 0 < Finset.sum S (fun i => a i * y i))
    (hKM : thresholdSelectedMass d S a y < Finset.sum S (fun i => a i * y i)) :
    let M := Finset.sum S (fun i => a i * y i)
    let K := thresholdSelectedMass d S a y
    let N := Finset.sum S a
    let z := thresholdPositiveRoot d M K
    And (0 < (M - K * z) / d) (0 < N - K - (M - K * z) / d) := by
  dsimp only
  let M := Finset.sum S (fun i => a i * y i)
  let K := thresholdSelectedMass d S a y
  let N := Finset.sum S a
  let z := thresholdPositiveRoot d M K
  have hK := (finiteWeightedThreshold_domain S a y d hd.2 ha hy hMoment hMass).1
  have hz : 1 < z := thresholdPositiveRoot_gt_one d M K hd hMass hK hKM
  have hRel : K * z * (z - d) = (1 - d) * M :=
    thresholdPositiveRoot_relation d M K hd hMass hK
  have hZD : 0 < 2 * z - d := by linarith only [hz, hd.2]
  have hLow : K < N := lt_of_lt_of_le hKM (finiteWeighted_equal_moment_le_total S a y ha hMoment)
  have hTotal := finiteWeighted_total_packet_pos S a y d z
    (by linarith only [hz, hd.2]) ha hLow
  have hLedger := finiteWeighted_total_packet_ledger S a y d z hMoment
  have hIdentity : Finset.sum S (fun i => a i * thresholdTotalPacket d z (y i)) =
      (2 * z - d) * (d * (N - K) - M + K * z) := by
    rw [hLedger]
    change (1 - 2 * z) * M + z ^ 2 * N - (d - z) ^ 2 * (N - K) = _
    nlinarith only [hRel]
  have hBracket : 0 < d * (N - K) - M + K * z := by
    rw [hIdentity] at hTotal
    exact (mul_pos_iff_of_pos_left hZD).mp hTotal
  have hNum : 0 < M - K * z := by
    have hP : 0 < K * z * (z - 1) :=
      mul_pos (mul_pos hK (by linarith only [hz])) (sub_pos.mpr hz)
    have hIdentity' : (1 - d) * (M - K * z) = K * z * (z - 1) := by
      nlinarith only [hRel]
    rw [<- hIdentity'] at hP
    exact (mul_pos_iff_of_pos_left (sub_pos.mpr hd.2)).mp hP
  constructor
  case left => exact div_pos hNum hd.1
  case right =>
    have hId : d * (N - K - (M - K * z) / d) = d * (N - K) - M + K * z := by
      field_simp [hd.1.ne']
      ring
    apply (mul_pos_iff_of_pos_left hd.1).mp
    rw [hId]
    exact hBracket

private theorem threshold_tilt_small_square (x e k c s : Real)
    (hx : 0 <= x) (hk : 0 < k) (hc : 0 < c) (hs : 0 < s)
    (he : e <= k * s ^ 2 / (4 * c))
    (hTilt : forall l : Real, And (0 <= l) (l <= s) ->
      l * x <= 2 * e + k * l ^ 2 / (2 * c)) :
    c * x ^ 2 <= 4 * k * e := by
  have hsTilt := hTilt s (And.intro hs.le le_rfl)
  have hDiv : (k * s ^ 2 / (2 * c)) * (2 * c) = k * s ^ 2 := by
    field_simp [hc.ne']
  have he' := mul_le_mul_of_nonneg_right he (show 0 <= 4 * c by positivity)
  have hCancel : (k * s ^ 2 / (4 * c)) * (4 * c) = k * s ^ 2 := by
    field_simp [hc.ne']
  rw [hCancel] at he'
  have hs' := mul_le_mul_of_nonneg_right hsTilt (show 0 <= 2 * c by positivity)
  have hCap : c * x <= k * s := by
    by_contra hn
    have hP := mul_pos hs (sub_pos.mpr (lt_of_not_ge hn))
    nlinarith only [hs', hDiv, he', hP]
  let l := c * x / k
  have hl : And (0 <= l) (l <= s) := by
    constructor
    case left => exact div_nonneg (mul_nonneg hc.le hx) hk.le
    case right =>
      have hh := mul_le_mul_of_nonneg_right hCap (show 0 <= 1 / k by positivity)
      have hL : c * x * (1 / k) = l := by dsimp [l]; ring
      have hR : k * s * (1 / k) = s := by field_simp [hk.ne']
      rwa [hL, hR] at hh
  have ht := hTilt l hl
  have hMultiply := mul_le_mul_of_nonneg_right ht (show 0 <= 2 * c * k by positivity)
  have hLeft : (l * x) * (2 * c * k) = 2 * c ^ 2 * x ^ 2 := by
    dsimp [l]
    field_simp [hk.ne']
  have hRight : (2 * e + k * l ^ 2 / (2 * c)) * (2 * c * k) =
      4 * c * k * e + c ^ 2 * x ^ 2 := by
    dsimp [l]
    field_simp [hk.ne', hc.ne']
    ring
  rw [hLeft, hRight] at hMultiply
  by_contra hn
  have hP := mul_pos hc (sub_pos.mpr (lt_of_not_ge hn))
  nlinarith only [hMultiply, hP]


theorem thresholdCanonicalStatistic_three_atoms (d z M K N : Real) (phi : Real -> Real) :
    thresholdCanonicalStatistic d z M K N phi =
      (N - K - (M - K * z) / d) * phi 0 +
        ((M - K * z) / d) * phi d + K * phi z := by
  unfold thresholdCanonicalStatistic
  ring

theorem finiteWeightedThreshold_lipschitz_inverse {Iota : Type*} (S : Finset Iota)
    (a y : Iota -> Real) (d : Real) (phi : Real -> Real)
    (hd : And (0 < d) (d < 1))
    (ha : forall i, Membership.mem S i -> 0 <= a i)
    (hy : forall i, Membership.mem S i -> 0 <= y i)
    (hMoment : Finset.sum S (fun i => a i * (y i) ^ 2) = Finset.sum S (fun i => a i * y i))
    (hMass : 0 < Finset.sum S (fun i => a i * y i))
    (hKM : thresholdSelectedMass d S a y <= Finset.sum S (fun i => a i * y i))
    (hphi : forall u v : Real, abs (phi u - phi v) <= abs (u - v)) :
    let M := Finset.sum S (fun i => a i * y i)
    let K := thresholdSelectedMass d S a y
    let N := Finset.sum S a
    let z := thresholdPositiveRoot d M K
    let e := Finset.sum S (fun i => a i * y i * (y i - 1) ^ 2) - thresholdPositiveCost d M K
    let c := thresholdBandCurvature d z
    let s := thresholdBandSlope d z
    abs (Finset.sum S (fun i => a i * phi (y i)) - thresholdCanonicalStatistic d z M K N phi) <=
      if e <= K * s ^ 2 / (4 * c) then 2 * Real.sqrt (K * e / c)
      else 2 * e / s + K * s / (2 * c) := by
  dsimp only
  let M := Finset.sum S (fun i => a i * y i)
  let K := thresholdSelectedMass d S a y
  let N := Finset.sum S a
  let z := thresholdPositiveRoot d M K
  let e := Finset.sum S (fun i => a i * y i * (y i - 1) ^ 2) - thresholdPositiveCost d M K
  let c := thresholdBandCurvature d z
  let s := thresholdBandSlope d z
  let R := Finset.sum S (fun i => a i * phi (y i)) - thresholdCanonicalStatistic d z M K N phi
  change abs R <= if e <= K * s ^ 2 / (4 * c) then 2 * Real.sqrt (K * e / c)
    else 2 * e / s + K * s / (2 * c)
  have hK : 0 < K := (finiteWeightedThreshold_domain S a y d hd.2 ha hy hMoment hMass).1
  have hz := (thresholdPositiveRoot_bounds d M K hd hMass hK hKM).2
  have hConstants := thresholdBand_constants_pos d z hd hz
  have hc : 0 < c := hConstants.2
  have hs : 0 < s := hConstants.1
  have he : 0 <= e :=
    sub_nonneg.mpr (finiteWeightedThreshold_positive_cost S a y d hd ha hy hMoment hMass hKM)
  have hTilt : forall l : Real, And (0 <= l) (l <= s) ->
      l * abs R <= 2 * e + K * l ^ 2 / (2 * c) := by
    intro l hl
    exact finiteWeightedThreshold_lipschitz_stability S a y d l phi hd ha hy hMoment hMass hKM hl hphi
  by_cases hSmall : e <= K * s ^ 2 / (4 * c)
  case pos =>
    rw [ite_eq_left hSmall]
    have hSquare := threshold_tilt_small_square (abs R) e K c s (abs_nonneg _) hK hc hs hSmall hTilt
    have hQ : 0 <= K * e / c := div_nonneg (mul_nonneg hK.le he) hc.le
    have hRoot : c * (2 * Real.sqrt (K * e / c)) ^ 2 = 4 * K * e := by
      calc
        _ = 4 * c * (Real.sqrt (K * e / c)) ^ 2 := by ring
        _ = 4 * c * (K * e / c) := by rw [Real.sq_sqrt hQ]
        _ = _ := by field_simp [hc.ne']
    by_contra hn
    have hlt : 2 * Real.sqrt (K * e / c) < abs R := lt_of_not_ge hn
    have hP : 0 < c * (abs R - 2 * Real.sqrt (K * e / c)) *
        (abs R + 2 * Real.sqrt (K * e / c)) :=
      mul_pos (mul_pos hc (sub_pos.mpr hlt))
        (by linarith only [hlt, Real.sqrt_nonneg (K * e / c)])
    nlinarith only [hSquare, hRoot, hP]
  case neg =>
    rw [ite_eq_right hSmall]
    have ht := hTilt s (And.intro hs.le le_rfl)
    have hIdentity : s * (2 * e / s + K * s / (2 * c)) =
        2 * e + K * s ^ 2 / (2 * c) := by
      field_simp [hs.ne', hc.ne']
    have hScaled : s * abs R <= s * (2 * e / s + K * s / (2 * c)) := by
      rw [hIdentity]
      exact ht
    by_contra hn
    have hP := mul_pos hs (sub_pos.mpr (lt_of_not_ge hn))
    nlinarith only [hScaled, hP]

end PrimeFactorOscillations

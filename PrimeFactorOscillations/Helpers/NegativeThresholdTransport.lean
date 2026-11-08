/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.NegativeThresholdIntegerCost
import PrimeFactorOscillations.Mathlib.Algebra.Order.QuadraticControl

/-! # Quantitative inverse stability on the negative threshold branch -/

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 5000000

noncomputable section
namespace PrimeFactorOscillations

def negativeThresholdAffineResidual (d z : Real) (phi : Real -> Real) (y : Real) : Real :=
  phi y - phi 0 - y * ((phi z - phi d) / (z - d)) -
    momentRoundIndicator d y * (phi d - phi 0 - d * ((phi z - phi d) / (z - d)))

def negativeThresholdCanonicalStatistic (d z M K N : Real) (phi : Real -> Real) : Real :=
  N * phi 0 + K * (phi d - phi 0) + (M - d * K) * ((phi z - phi d) / (z - d))

theorem negativeThresholdAffineResidual_bound (d z y : Real) (phi : Real -> Real)
    (hdz : d < z)
    (hphi : forall u v : Real, abs (phi u - phi v) <= abs (u - v)) :
    abs (negativeThresholdAffineResidual d z phi y) <=
      2 * abs (y - d * momentRoundIndicator d y -
        (z - d) * momentRoundIndicator (negativeThresholdHigh d z) y) := by
  have hGap : 0 < z - d := sub_pos.mpr hdz
  have hSlope : abs ((phi z - phi d) / (z - d)) <= 1 := by
    rw [abs_div, abs_of_pos hGap]
    apply (div_le_one hGap).mpr
    simpa only [abs_of_pos hGap] using hphi z d
  have hBound : forall u v : Real,
      abs ((phi u - phi v) - (u - v) * ((phi z - phi d) / (z - d))) <=
        2 * abs (u - v) := by
    intro u v
    calc
      _ <= abs (phi u - phi v) + abs ((u - v) * ((phi z - phi d) / (z - d))) :=
        abs_sub _ _
      _ = abs (phi u - phi v) + abs (u - v) * abs ((phi z - phi d) / (z - d)) := by
        rw [abs_mul]
      _ <= abs (u - v) + abs (u - v) * 1 :=
        add_le_add (hphi u v) (mul_le_mul_of_nonneg_left hSlope (abs_nonneg _))
      _ = _ := by ring
  by_cases hHigh : negativeThresholdHigh d z <= y
  case pos =>
    have hCut : d <= y := by
      dsimp [negativeThresholdHigh] at hHigh
      linarith only [hdz, hHigh]
    have hRes : negativeThresholdAffineResidual d z phi y =
        (phi y - phi z) - (y - z) * ((phi z - phi d) / (z - d)) := by
      simp only [negativeThresholdAffineResidual, momentRoundIndicator, ite_eq_left hCut, one_mul]
      field_simp [hGap.ne']
      ring
    rw [hRes]
    simp only [momentRoundIndicator, ite_eq_left hCut, ite_eq_left hHigh, mul_one]
    have hIdentity : y - d - (z - d) = y - z := by ring
    rw [hIdentity]
    exact hBound y z
  case neg =>
    by_cases hCut : d <= y
    case pos =>
      have hRes : negativeThresholdAffineResidual d z phi y =
          (phi y - phi d) - (y - d) * ((phi z - phi d) / (z - d)) := by
        simp only [negativeThresholdAffineResidual, momentRoundIndicator, ite_eq_left hCut, one_mul]
        ring
      rw [hRes]
      simp only [momentRoundIndicator, ite_eq_left hCut, ite_eq_right hHigh, mul_one, mul_zero, sub_zero]
      exact hBound y d
    case neg =>
      have hRes : negativeThresholdAffineResidual d z phi y =
          (phi y - phi 0) - (y - 0) * ((phi z - phi d) / (z - d)) := by
        simp only [negativeThresholdAffineResidual, momentRoundIndicator, ite_eq_right hCut,
          zero_mul, sub_zero]
      rw [hRes]
      simp only [momentRoundIndicator, ite_eq_right hCut, ite_eq_right hHigh, mul_zero, sub_zero]
      simpa only [sub_zero] using hBound y 0

theorem negativeThresholdAffineResidual_tilt (d z y l : Real) (phi : Real -> Real)
    (hd : And (0 < d) (d < 1)) (hz : 1 <= z) (hy : 0 <= y)
    (hl : And (0 <= l) (l <= negativeThresholdSlope d z))
    (hphi : forall u v : Real, abs (phi u - phi v) <= abs (u - v)) :
    l * abs (negativeThresholdAffineResidual d z phi y) <=
      2 * thresholdNegativePacket d z y +
        l ^ 2 / (2 * negativeThresholdCurvature d z) *
          momentRoundIndicator (negativeThresholdHigh d z) y := by
  let t := y - d * momentRoundIndicator d y -
    (z - d) * momentRoundIndicator (negativeThresholdHigh d z) y
  have hAbs : l * abs t <= thresholdNegativePacket d z y +
      l ^ 2 / (4 * negativeThresholdCurvature d z) *
        momentRoundIndicator (negativeThresholdHigh d z) y := by
    by_cases hSign : 0 <= t
    case pos =>
      have hh := negativeThreshold_tilted_packet d z y l 1 hd hz hy hl (Or.inl rfl)
      change 0 <= thresholdNegativePacket d z y +
        l ^ 2 / (4 * negativeThresholdCurvature d z) *
          momentRoundIndicator (negativeThresholdHigh d z) y - l * 1 * t at hh
      rw [abs_of_nonneg hSign]
      linarith only [hh]
    case neg =>
      have hh := negativeThreshold_tilted_packet d z y l (-1) hd hz hy hl (Or.inr rfl)
      change 0 <= thresholdNegativePacket d z y +
        l ^ 2 / (4 * negativeThresholdCurvature d z) *
          momentRoundIndicator (negativeThresholdHigh d z) y - l * (-1) * t at hh
      rw [abs_of_nonpos (le_of_not_ge hSign)]
      linarith only [hh]
  have hR := mul_le_mul_of_nonneg_left
    (negativeThresholdAffineResidual_bound d z y phi (by linarith only [hd.2, hz]) hphi) hl.1
  have hc := (negativeThreshold_constants d z hd hz).2.1
  calc
    _ <= l * (2 * abs t) := hR
    _ <= 2 * (thresholdNegativePacket d z y +
        l ^ 2 / (4 * negativeThresholdCurvature d z) *
          momentRoundIndicator (negativeThresholdHigh d z) y) := by linarith only [hAbs]
    _ = _ := by field_simp [hc.ne']; ring


theorem finiteWeightedNegative_residual_sum {Iota : Type*} (S : Finset Iota)
    (a y : Iota -> Real) (d z : Real) (phi : Real -> Real) :
    Finset.sum S (fun i => a i * negativeThresholdAffineResidual d z phi (y i)) =
      Finset.sum S (fun i => a i * phi (y i)) -
        negativeThresholdCanonicalStatistic d z (Finset.sum S (fun i => a i * y i))
          (thresholdSelectedMass d S a y) (Finset.sum S a) phi := by
  have hExpand : Finset.sum S (fun i => a i * negativeThresholdAffineResidual d z phi (y i)) =
      Finset.sum S (fun i => a i * phi (y i) - phi 0 * a i -
        ((phi z - phi d) / (z - d)) * (a i * y i) -
        (phi d - phi 0 - d * ((phi z - phi d) / (z - d))) *
          (a i * momentRoundIndicator d (y i))) := by
    apply Finset.sum_congr rfl
    intro i _
    unfold negativeThresholdAffineResidual
    ring
  rw [hExpand]
  simp only [Finset.sum_sub_distrib, <- Finset.mul_sum]
  unfold negativeThresholdCanonicalStatistic thresholdSelectedMass
  ring

theorem finiteWeightedNegative_lipschitz_packet {Iota : Type*} (S : Finset Iota)
    (a y : Iota -> Real) (d z l : Real) (phi : Real -> Real)
    (hd : And (0 < d) (d < 1)) (hz : 1 <= z)
    (ha : forall i, Membership.mem S i -> 0 <= a i)
    (hy : forall i, Membership.mem S i -> 0 <= y i)
    (hl : And (0 <= l) (l <= negativeThresholdSlope d z))
    (hphi : forall u v : Real, abs (phi u - phi v) <= abs (u - v)) :
    l * abs (Finset.sum S (fun i => a i * negativeThresholdAffineResidual d z phi (y i))) <=
      2 * Finset.sum S (fun i => a i * thresholdNegativePacket d z (y i)) +
        thresholdSelectedMass d S a y * l ^ 2 / (2 * negativeThresholdCurvature d z) := by
  have hAbs : abs (Finset.sum S (fun i => a i * negativeThresholdAffineResidual d z phi (y i))) <=
      Finset.sum S (fun i => a i * abs (negativeThresholdAffineResidual d z phi (y i))) := by
    calc
      _ <= Finset.sum S (fun i => abs (a i * negativeThresholdAffineResidual d z phi (y i))) :=
        Finset.abs_sum_le_sum_abs _ _
      _ = _ := by
        apply Finset.sum_congr rfl
        intro i hi
        rw [abs_mul, abs_of_nonneg (ha i hi)]
  have hEach : forall i, Membership.mem S i ->
      a i * (l * abs (negativeThresholdAffineResidual d z phi (y i))) <=
        a i * (2 * thresholdNegativePacket d z (y i) +
          l ^ 2 / (2 * negativeThresholdCurvature d z) *
            momentRoundIndicator (negativeThresholdHigh d z) (y i)) := by
    intro i hi
    exact mul_le_mul_of_nonneg_left
      (negativeThresholdAffineResidual_tilt d z (y i) l phi hd hz (hy i hi) hl hphi) (ha i hi)
  have hSum := Finset.sum_le_sum hEach
  have hLeft : Finset.sum S (fun i => a i * (l * abs (negativeThresholdAffineResidual d z phi (y i)))) =
      l * Finset.sum S (fun i => a i * abs (negativeThresholdAffineResidual d z phi (y i))) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    ring
  have hRight : Finset.sum S (fun i => a i * (2 * thresholdNegativePacket d z (y i) +
      l ^ 2 / (2 * negativeThresholdCurvature d z) *
        momentRoundIndicator (negativeThresholdHigh d z) (y i))) =
      2 * Finset.sum S (fun i => a i * thresholdNegativePacket d z (y i)) +
        thresholdSelectedMass (negativeThresholdHigh d z) S a y * l ^ 2 /
          (2 * negativeThresholdCurvature d z) := by
    calc
      _ = Finset.sum S (fun i => 2 * (a i * thresholdNegativePacket d z (y i)) +
          (l ^ 2 / (2 * negativeThresholdCurvature d z)) *
            (a i * momentRoundIndicator (negativeThresholdHigh d z) (y i))) := by
        apply Finset.sum_congr rfl
        intro i _
        ring
      _ = _ := by
        unfold thresholdSelectedMass
        rw [Finset.sum_add_distrib, <- Finset.mul_sum, <- Finset.mul_sum]
        ring
  rw [hLeft, hRight] at hSum
  have hc := negativeThreshold_constants d z hd hz
  have hCount := finiteWeightedThreshold_cutoff_antitone S a y d (negativeThresholdHigh d z) hc.2.2.le ha
  have hScale := mul_le_mul_of_nonneg_right hCount
    (div_nonneg (sq_nonneg l) (show 0 <= 2 * negativeThresholdCurvature d z by linarith only [hc.2.1]))
  calc
    _ <= 2 * Finset.sum S (fun i => a i * thresholdNegativePacket d z (y i)) +
        thresholdSelectedMass (negativeThresholdHigh d z) S a y * l ^ 2 /
          (2 * negativeThresholdCurvature d z) :=
      le_trans (mul_le_mul_of_nonneg_left hAbs hl.1) hSum
    _ <= _ := by
      simpa only [mul_div_assoc] using
        add_le_add (le_refl (2 * Finset.sum S (fun i => a i * thresholdNegativePacket d z (y i)))) hScale

theorem finiteWeightedNegative_lipschitz_stability {Iota : Type*} (S : Finset Iota)
    (a y : Iota -> Real) (d l : Real) (phi : Real -> Real)
    (hd : And (0 < d) (d < 1))
    (ha : forall i, Membership.mem S i -> 0 <= a i)
    (hy : forall i, Membership.mem S i -> 0 <= y i)
    (hMoment : Finset.sum S (fun i => a i * (y i) ^ 2) = Finset.sum S (fun i => a i * y i))
    (hMass : 0 < Finset.sum S (fun i => a i * y i))
    (hMK : Finset.sum S (fun i => a i * y i) < thresholdSelectedMass d S a y)
    (hl : And (0 <= l) (l <= negativeThresholdSlope d
      (thresholdNegativeRoot d (Finset.sum S (fun i => a i * y i)) (thresholdSelectedMass d S a y))))
    (hphi : forall u v : Real, abs (phi u - phi v) <= abs (u - v)) :
    l * abs (Finset.sum S (fun i => a i * phi (y i)) -
      negativeThresholdCanonicalStatistic d
        (thresholdNegativeRoot d (Finset.sum S (fun i => a i * y i)) (thresholdSelectedMass d S a y))
        (Finset.sum S (fun i => a i * y i)) (thresholdSelectedMass d S a y) (Finset.sum S a) phi) <=
      2 * (Finset.sum S (fun i => a i * y i * (y i - 1) ^ 2) -
        thresholdNegativeCost d (Finset.sum S (fun i => a i * y i)) (thresholdSelectedMass d S a y)) +
        thresholdSelectedMass d S a y * l ^ 2 / (2 * negativeThresholdCurvature d
          (thresholdNegativeRoot d (Finset.sum S (fun i => a i * y i)) (thresholdSelectedMass d S a y))) := by
  let M := Finset.sum S (fun i => a i * y i)
  let K := thresholdSelectedMass d S a y
  let z := thresholdNegativeRoot d M K
  have hDomain := finiteWeightedThreshold_domain S a y d hd.2 ha hy hMoment hMass
  have hz := thresholdNegativeRoot_ge_one d M K hd.1 hDomain.2 hMK.le
  have hPacket := finiteWeightedNegative_lipschitz_packet S a y d z l phi hd hz ha hy hl hphi
  rw [finiteWeightedNegative_residual_sum] at hPacket
  have hDefect := finiteWeightedThreshold_exact_negative_defect S a y d hMoment hDomain.2
  change Finset.sum S (fun i => a i * thresholdNegativePacket d z (y i)) =
    Finset.sum S (fun i => a i * y i * (y i - 1) ^ 2) - thresholdNegativeCost d M K at hDefect
  rw [hDefect] at hPacket
  exact hPacket

theorem negativeThresholdCanonicalStatistic_three_atoms (d z M K N : Real) (phi : Real -> Real)
    (hdz : Not (z - d = 0)) :
    negativeThresholdCanonicalStatistic d z M K N phi =
      (N - K) * phi 0 + ((K * z - M) / (z - d)) * phi d +
        ((M - d * K) / (z - d)) * phi z := by
  unfold negativeThresholdCanonicalStatistic
  field_simp [hdz]
  ring

theorem finiteWeightedNegative_canonical_weights {Iota : Type*} (S : Finset Iota)
    (a y : Iota -> Real) (d : Real) (hd : And (0 < d) (d < 1))
    (ha : forall i, Membership.mem S i -> 0 <= a i)
    (hy : forall i, Membership.mem S i -> 0 <= y i)
    (hMoment : Finset.sum S (fun i => a i * (y i) ^ 2) = Finset.sum S (fun i => a i * y i))
    (hMass : 0 < Finset.sum S (fun i => a i * y i))
    (hMK : Finset.sum S (fun i => a i * y i) < thresholdSelectedMass d S a y) :
    let M := Finset.sum S (fun i => a i * y i)
    let K := thresholdSelectedMass d S a y
    let N := Finset.sum S a
    let z := thresholdNegativeRoot d M K
    And (0 <= N - K) (And (0 < (K * z - M) / (z - d)) (0 < (M - d * K) / (z - d))) := by
  dsimp only
  let M := Finset.sum S (fun i => a i * y i)
  let K := thresholdSelectedMass d S a y
  let N := Finset.sum S a
  let z := thresholdNegativeRoot d M K
  have hDomain := finiteWeightedThreshold_domain S a y d hd.2 ha hy hMoment hMass
  have hz : 1 <= z := thresholdNegativeRoot_ge_one d M K hd.1 hDomain.2 hMK.le
  have hg : 0 < z - d := by linarith only [hz, hd.2]
  have hKN : K <= N := by
    unfold K N thresholdSelectedMass
    apply Finset.sum_le_sum
    intro i hi
    by_cases hCut : d <= y i
    case pos => simp only [momentRoundIndicator, ite_eq_left hCut, mul_one]; exact le_rfl
    case neg => simp only [momentRoundIndicator, ite_eq_right hCut, mul_zero]; exact ha i hi
  have hK : 0 < K := hDomain.1
  have hProduct := mul_nonneg hK.le (sub_nonneg.mpr hz)
  have hNum : 0 < K * z - M := by
    change M < K at hMK
    nlinarith only [hProduct, hMK]
  exact And.intro (sub_nonneg.mpr hKN)
    (And.intro (div_pos hNum hg) (div_pos (sub_pos.mpr hDomain.2) hg))


theorem thresholdNegativeCanonical_moments (d M K : Real)
    (hd : And (0 < d) (d < 1)) (hDomain : d * K < M) (hMK : M <= K) :
    let z := thresholdNegativeRoot d M K
    let a := (K * z - M) / (z - d)
    let b := (M - d * K) / (z - d)
    And (a + b = K) (And (a * d + b * z = M)
      (And (a * d ^ 2 + b * z ^ 2 = M)
        (a * d * (d - 1) ^ 2 + b * z * (z - 1) ^ 2 = thresholdNegativeCost d M K))) := by
  dsimp only
  let z := thresholdNegativeRoot d M K
  let a := (K * z - M) / (z - d)
  let b := (M - d * K) / (z - d)
  have hz : 1 <= z := thresholdNegativeRoot_ge_one d M K hd.1 hDomain hMK
  have hg : 0 < z - d := by linarith only [hd.2, hz]
  have hRel : d * z * K = M * (z - 1 + d) := thresholdNegativeRoot_relation d M K hDomain
  have hSum : a + b = K := by dsimp [a, b]; field_simp [hg.ne']; ring
  have hFirst : a * d + b * z = M := by dsimp [a, b]; field_simp [hg.ne']; ring
  have hSecond : a * d ^ 2 + b * z ^ 2 = M := by
    calc
      _ = (d + z) * (a * d + b * z) - d * z * (a + b) := by ring
      _ = M := by rw [hFirst, hSum]; nlinarith only [hRel]
  have hThird : a * d ^ 3 + b * z ^ 3 = (d + z) * M - d * z * M := by
    calc
      _ = (d + z) * (a * d ^ 2 + b * z ^ 2) - d * z * (a * d + b * z) := by ring
      _ = _ := by rw [hSecond, hFirst]
  have hEnergy : a * d * (d - 1) ^ 2 + b * z * (z - 1) ^ 2 =
      (d + z - 1 - d * z) * M := by
    calc
      _ = (a * d ^ 3 + b * z ^ 3) - 2 * (a * d ^ 2 + b * z ^ 2) + (a * d + b * z) := by ring
      _ = _ := by rw [hThird, hSecond, hFirst]; ring
  constructor
  case left => exact hSum
  case right =>
    refine And.intro hFirst (And.intro hSecond ?_)
    change a * d * (d - 1) ^ 2 + b * z * (z - 1) ^ 2 = thresholdNegativeCost d M K
    rw [hEnergy, thresholdNegativeCost_root]
    change (d + z - 1 - d * z) * M = d * z * (K - M)
    nlinarith only [hRel]

theorem finiteWeightedNegative_lipschitz_inverse {Iota : Type*} (S : Finset Iota)
    (a y : Iota -> Real) (d : Real) (phi : Real -> Real)
    (hd : And (0 < d) (d < 1))
    (ha : forall i, Membership.mem S i -> 0 <= a i)
    (hy : forall i, Membership.mem S i -> 0 <= y i)
    (hMoment : Finset.sum S (fun i => a i * (y i) ^ 2) = Finset.sum S (fun i => a i * y i))
    (hMass : 0 < Finset.sum S (fun i => a i * y i))
    (hMK : Finset.sum S (fun i => a i * y i) < thresholdSelectedMass d S a y)
    (hphi : forall u v : Real, abs (phi u - phi v) <= abs (u - v)) :
    let M := Finset.sum S (fun i => a i * y i)
    let K := thresholdSelectedMass d S a y
    let N := Finset.sum S a
    let z := thresholdNegativeRoot d M K
    let e := Finset.sum S (fun i => a i * y i * (y i - 1) ^ 2) - thresholdNegativeCost d M K
    let c := negativeThresholdCurvature d z
    let s := negativeThresholdSlope d z
    abs (Finset.sum S (fun i => a i * phi (y i)) - negativeThresholdCanonicalStatistic d z M K N phi) <=
      if e <= K * s ^ 2 / (4 * c) then 2 * Real.sqrt (K * e / c)
      else 2 * e / s + K * s / (2 * c) := by
  dsimp only
  let M := Finset.sum S (fun i => a i * y i)
  let K := thresholdSelectedMass d S a y
  let N := Finset.sum S a
  let z := thresholdNegativeRoot d M K
  let e := Finset.sum S (fun i => a i * y i * (y i - 1) ^ 2) - thresholdNegativeCost d M K
  let c := negativeThresholdCurvature d z
  let s := negativeThresholdSlope d z
  let R := Finset.sum S (fun i => a i * phi (y i)) - negativeThresholdCanonicalStatistic d z M K N phi
  change abs R <= if e <= K * s ^ 2 / (4 * c) then 2 * Real.sqrt (K * e / c)
    else 2 * e / s + K * s / (2 * c)
  have hDomain := finiteWeightedThreshold_domain S a y d hd.2 ha hy hMoment hMass
  have hz := thresholdNegativeRoot_ge_one d M K hd.1 hDomain.2 hMK.le
  have hConstants := negativeThreshold_constants d z hd hz
  have he : 0 <= e := sub_nonneg.mpr
    (finiteWeightedThreshold_negative_cost S a y d hd ha hy hMoment hMass hMK.le)
  apply Real.le_piecewise_of_quadratic_tilt (abs R) e K c s
    (abs_nonneg _) he hDomain.1 hConstants.2.1 hConstants.1
  intro l hl
  exact finiteWeightedNegative_lipschitz_stability S a y d l phi hd ha hy hMoment hMass hMK hl hphi

end PrimeFactorOscillations

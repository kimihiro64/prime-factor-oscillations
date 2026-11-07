/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.ThresholdRadialCard

/-! # Exact two-layer inverse, uniqueness, and the complete real-weight domain -/

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 5000000

noncomputable section
namespace PrimeFactorOscillations

def thresholdTwoLayer (d M N K u v : Real) : Prop :=
  And (And (0 <= u) (And (u < d) (d <= v)))
    (And ((N - K) * u + K * v = M) ((N - K) * u ^ 2 + K * v ^ 2 = M))

def thresholdTwoLow (N M K : Real) : Real :=
  (M - Real.sqrt (K * M * (N - M) / (N - K))) / N

def thresholdTwoHigh (N M K : Real) : Real :=
  (M + Real.sqrt ((N - K) * M * (N - M) / K)) / N

theorem thresholdTwoLayer_bounds (d M N K u v : Real)
    (hd : And (0 < d) (d < 1)) (hK : 0 < K) (hKN : K < N)
    (hLayer : thresholdTwoLayer d M N K u v) :
    And (0 < M) (And (K <= M) (M < N)) := by
  let J := N - K
  have hJ : 0 < J := sub_pos.mpr hKN
  have hu0 := hLayer.1.1
  have hu1 : u < 1 := lt_trans hLayer.1.2.1 hd.2
  have hv0 : 0 < v := lt_of_lt_of_le hd.1 hLayer.1.2.2
  have hFirst : J * u + K * v = M := hLayer.2.1
  have hSecond : J * u ^ 2 + K * v ^ 2 = M := hLayer.2.2
  have hBalance : K * v * (v - 1) = J * u * (1 - u) := by nlinarith only [hFirst, hSecond]
  have hLow := mul_nonneg (mul_nonneg hJ.le hu0) (sub_nonneg.mpr hu1.le)
  have hV : 1 <= v := by
    by_contra hn
    have hp := mul_neg_of_pos_of_neg (mul_pos hK hv0) (sub_neg.mpr (lt_of_not_ge hn))
    linarith only [hBalance, hLow, hp]
  have hMK : K <= M := by
    have hA := mul_nonneg hJ.le hu0
    have hB := mul_nonneg hK.le (sub_nonneg.mpr hV)
    nlinarith only [hFirst, hA, hB]
  have hVariance : N - M = J * (u - 1) ^ 2 + K * (v - 1) ^ 2 := by
    calc
      _ = (J * u ^ 2 + K * v ^ 2) - 2 * (J * u + K * v) + (J + K) := by
        rw [hFirst, hSecond]
        dsimp [J]
        ring
      _ = _ := by ring
  have hStrict := mul_pos hJ (sq_pos_of_ne_zero (sub_ne_zero.mpr (ne_of_lt hu1)))
  have hOther := mul_nonneg hK.le (sq_nonneg (v - 1))
  exact And.intro (lt_of_lt_of_le hK hMK) (And.intro hMK (by linarith only [hVariance, hStrict, hOther]))

theorem thresholdTwoLayer_inverse (d M N K u v : Real)
    (hK : 0 < K) (hKN : K < N) (hLayer : thresholdTwoLayer d M N K u v) :
    And (u = thresholdTwoLow N M K) (v = thresholdTwoHigh N M K) := by
  let J := N - K
  have hJ : 0 < J := sub_pos.mpr hKN
  have hN : 0 < N := lt_trans hK hKN
  have hGap : 0 < v - u := by linarith only [hLayer.1.2.1, hLayer.1.2.2]
  have hFirst : J * u + K * v = M := hLayer.2.1
  have hSecond : J * u ^ 2 + K * v ^ 2 = M := hLayer.2.2
  have hVariance : N * M - M ^ 2 = J * K * (v - u) ^ 2 := by
    calc
      _ = (J + K) * (J * u ^ 2 + K * v ^ 2) - (J * u + K * v) ^ 2 := by
        rw [hFirst, hSecond]
        dsimp [J]
        ring
      _ = _ := by ring
  have hRadLow : K * M * (N - M) / J = (K * (v - u)) ^ 2 := by
    calc
      _ = K * (N * M - M ^ 2) / J := by ring
      _ = K * (J * K * (v - u) ^ 2) / J := by rw [hVariance]
      _ = _ := by field_simp [hJ.ne']
  have hRadHigh : J * M * (N - M) / K = (J * (v - u)) ^ 2 := by
    calc
      _ = J * (N * M - M ^ 2) / K := by ring
      _ = J * (J * K * (v - u) ^ 2) / K := by rw [hVariance]
      _ = _ := by field_simp [hK.ne']
  have hRootLow : Real.sqrt (K * M * (N - M) / J) = K * (v - u) := by
    rw [hRadLow]
    exact Real.sqrt_sq (mul_nonneg hK.le hGap.le)
  have hRootHigh : Real.sqrt (J * M * (N - M) / K) = J * (v - u) := by
    rw [hRadHigh]
    exact Real.sqrt_sq (mul_nonneg hJ.le hGap.le)
  have hFirstExpanded : (N - K) * u + K * v = M := hFirst
  have hNumLow : M - K * (v - u) = N * u := by nlinarith only [hFirstExpanded]
  have hNumHigh : M + J * (v - u) = N * v := by dsimp [J]; nlinarith only [hFirstExpanded]
  constructor
  case left =>
    unfold thresholdTwoLow
    change u = (M - Real.sqrt (K * M * (N - M) / J)) / N
    rw [hRootLow, hNumLow]
    field_simp [hN.ne']
    <;> ring
  case right =>
    unfold thresholdTwoHigh
    change v = (M + Real.sqrt (J * M * (N - M) / K)) / N
    rw [hRootHigh, hNumHigh]
    field_simp [hN.ne']
    <;> ring

theorem thresholdTwoLayer_unique (d M N K u v p q : Real)
    (hK : 0 < K) (hKN : K < N)
    (hLayer : thresholdTwoLayer d M N K u v) (hOther : thresholdTwoLayer d M N K p q) :
    And (p = u) (q = v) := by
  have h := thresholdTwoLayer_inverse d M N K u v hK hKN hLayer
  have hOtherInverse := thresholdTwoLayer_inverse d M N K p q hK hKN hOther
  exact And.intro (hOtherInverse.1.trans h.1.symm) (hOtherInverse.2.trans h.2.symm)

theorem thresholdTwoLayer_upper (d M N K u v : Real)
    (hd : And (0 < d) (d < 1)) (hK : 0 < K) (hKN : K < N)
    (hLayer : thresholdTwoLayer d M N K u v) : M < thresholdTotalUpper d N K := by
  classical
  let a : Fin 2 -> Real := fun i => if i.val = 0 then N - K else K
  let y := thresholdPairCoords u v
  have ha : forall i, Membership.mem Finset.univ i -> 0 <= a i := by
    intro i _
    dsimp [a]
    split_ifs
    case pos => exact sub_nonneg.mpr hKN.le
    case neg => exact hK.le
  have hFirst : Finset.sum Finset.univ (fun i => a i * y i) = M := by
    simpa [a, y, thresholdPairCoords, Fin.sum_univ_succ] using hLayer.2.1
  have hSecond : Finset.sum Finset.univ (fun i => a i * (y i) ^ 2) = M := by
    simpa [a, y, thresholdPairCoords, Fin.sum_univ_succ] using hLayer.2.2
  have hTotal : Finset.sum Finset.univ a = N := by simp [a, Fin.sum_univ_succ]
  have hCut : Not (d <= u) := not_le.mpr hLayer.1.2.1
  have hSelected : thresholdSelectedMass d Finset.univ a y = K := by
    simp [thresholdSelectedMass, a, y, thresholdPairCoords, Fin.sum_univ_succ,
      momentRoundIndicator, hCut, hLayer.1.2.2]
  have h := finiteWeighted_threshold_total_upper Finset.univ a y d hd ha
    (by rw [hFirst, hSecond]) (by rw [hSelected]; exact hK)
    (by rw [hSelected, hTotal]; exact hKN)
  simpa only [hFirst, hTotal, hSelected] using h

theorem thresholdTwoLayer_exists (d M N K : Real)
    (hd : And (0 < d) (d < 1)) (hK : 0 < K) (hKN : K < N)
    (hLow : K <= M) (hHigh : M < thresholdTotalUpper d N K) :
    exists u, exists v, thresholdTwoLayer d M N K u v := by
  let J := N - K
  let F := fun u : Real => thresholdModelMass J K u / 2
  have hJ : 0 < J := sub_pos.mpr hKN
  have hCont : Continuous F := (thresholdModelMass_continuous J K).div_const 2
  have hZero : F 0 = K := by dsimp [F]; rw [thresholdModelMass_zero]; ring
  have hEnd : F d = thresholdTotalUpper d N K := by
    unfold F thresholdModelMass thresholdTotalUpper
    change (2 * J * d + 2 * K * thresholdModelHigh J K d) / 2 = J * d + K * thresholdModelHigh J K d
    ring
  have hBetween : Membership.mem (Set.Icc (F 0) (F d)) M := by
    rw [hZero, hEnd]
    exact And.intro hLow hHigh.le
  choose u hu using intermediate_value_Icc hd.1.le hCont.continuousOn hBetween
  have huLt : u < d := by
    by_contra hn
    have heq : u = d := le_antisymm hu.1.2 (le_of_not_gt hn)
    have hValue := hu.2
    rw [heq, hEnd] at hValue
    linarith only [hValue, hHigh]
  let v := thresholdModelHigh J K u
  have huDomain : And (0 <= u) (u <= 1) := And.intro hu.1.1 (le_trans hu.1.2 hd.2.le)
  have hV : 1 <= v := thresholdModelHigh_bounds J K u hJ.le hK huDomain
  have hValue := hu.2
  change (2 * J * u + 2 * K * v) / 2 = M at hValue
  have hFirst : J * u + K * v = M := by linarith only [hValue]
  have hSecond := thresholdModelHigh_moment J K u hJ.le hK huDomain
  change J * u ^ 2 + K * v ^ 2 = J * u + K * v at hSecond
  exact Exists.intro u (Exists.intro v
    (And.intro (And.intro hu.1.1 (And.intro huLt (le_trans hd.2.le hV)))
      (And.intro hFirst (hSecond.trans hFirst))))

theorem thresholdTwoLayer_feasibility_iff (d M N K : Real)
    (hd : And (0 < d) (d < 1)) (hK : 0 < K) (hKN : K < N) :
    (exists u, exists v, thresholdTwoLayer d M N K u v) <->
      And (K <= M) (M < thresholdTotalUpper d N K) := by
  constructor
  case mp =>
    intro h
    choose u v hLayer using h
    exact And.intro (thresholdTwoLayer_bounds d M N K u v hd hK hKN hLayer).2.1
      (thresholdTwoLayer_upper d M N K u v hd hK hKN hLayer)
  case mpr => intro h; exact thresholdTwoLayer_exists d M N K hd hK hKN h.1 h.2

theorem thresholdTwoLayer_unique_exists (d M N K : Real)
    (hd : And (0 < d) (d < 1)) (hK : 0 < K) (hKN : K < N)
    (hLow : K <= M) (hHigh : M < thresholdTotalUpper d N K) :
    exists u, exists v, And (thresholdTwoLayer d M N K u v)
      (forall p q, thresholdTwoLayer d M N K p q -> And (p = u) (q = v)) := by
  choose u v hLayer using thresholdTwoLayer_exists d M N K hd hK hKN hLow hHigh
  exact Exists.intro u (Exists.intro v (And.intro hLayer
    (fun p q hOther => thresholdTwoLayer_unique d M N K u v p q hK hKN hLayer hOther)))

theorem finiteWeighted_two_layer_function {Iota : Type*} (S : Finset Iota)
    (a y : Iota -> Real) (d u v : Real) (f : Real -> Real)
    (ha : forall i, Membership.mem S i -> 0 <= a i) (hu : u < d) (hv : d <= v)
    (hCover : forall i, Membership.mem S i -> 0 < a i -> Or (y i = u) (y i = v)) :
    Finset.sum S (fun i => a i * f (y i)) =
      (Finset.sum S a - thresholdSelectedMass d S a y) * f u + thresholdSelectedMass d S a y * f v := by
  classical
  have hIU : momentRoundIndicator d u = 0 := by simp only [momentRoundIndicator, if_neg (not_le.mpr hu)]
  have hIV : momentRoundIndicator d v = 1 := by simp only [momentRoundIndicator, if_pos hv]
  calc
    _ = f u * Finset.sum S a + (f v - f u) * thresholdSelectedMass d S a y := by
      unfold thresholdSelectedMass
      rw [Finset.mul_sum, Finset.mul_sum, <- Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro i hi
      by_cases hp : 0 < a i
      case pos =>
        rcases hCover i hi hp with hU | hV
        case inl => rw [hU, hIU]; ring
        case inr => rw [hV, hIV]; ring
      case neg =>
        have hz : a i = 0 := le_antisymm (le_of_not_gt hp) (ha i hi)
        simp [hz]
    _ = _ := by ring

theorem finiteWeighted_two_layer_moments {Iota : Type*} (S : Finset Iota)
    (a y : Iota -> Real) (d u v : Real)
    (ha : forall i, Membership.mem S i -> 0 <= a i) (hu : u < d) (hv : d <= v)
    (hCover : forall i, Membership.mem S i -> 0 < a i -> Or (y i = u) (y i = v)) :
    And (Finset.sum S (fun i => a i * y i) =
      (Finset.sum S a - thresholdSelectedMass d S a y) * u + thresholdSelectedMass d S a y * v)
      (Finset.sum S (fun i => a i * (y i) ^ 2) =
        (Finset.sum S a - thresholdSelectedMass d S a y) * u ^ 2 + thresholdSelectedMass d S a y * v ^ 2) := by
  exact And.intro (finiteWeighted_two_layer_function S a y d u v (fun q => q) ha hu hv hCover)
    (finiteWeighted_two_layer_function S a y d u v (fun q => q ^ 2) ha hu hv hCover)

end PrimeFactorOscillations

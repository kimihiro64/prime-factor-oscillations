/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.ThresholdSelectedVariance

/-! # Sharp radial separation rigidity and the resulting linear inverse -/

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 5000000

noncomputable section
namespace PrimeFactorOscillations

def thresholdSelectedSeparated {Iota : Type*} (d : Real) (S : Finset Iota)
    (a : Iota -> Nat) (y : Iota -> Real) (g : Real) : Prop :=
  forall i j, Membership.mem S i -> Membership.mem S j ->
    0 < a i -> 0 < a j -> d <= y i -> d <= y j ->
      Not (y i = y j) -> g <= abs (y i - y j)

theorem finiteEven_selected_separation_variance {Iota : Type*} (S : Finset Iota)
    (a : Iota -> Nat) (y : Iota -> Real) (d g : Real) (hg : 0 <= g)
    (hSeparated : thresholdSelectedSeparated d S a y g)
    (j i : Iota) (hj : Membership.mem S j) (hi : Membership.mem S i)
    (haj : 0 < a j) (hai : 0 < a i) (hcj : d <= y j) (hci : d <= y i)
    (hNe : Not (y i = y j)) :
    let w := fun r => 2 * (a r : Real)
    let K := thresholdSelectedMass d S w y
    2 * (K - 2) * g ^ 2 <= K * thresholdSelectedVariance d S w y := by
  classical
  dsimp only
  let w := fun r => 2 * (a r : Real)
  let b := fun r => w r * momentRoundIndicator d (y r)
  let c := fun r => if y r = y j then 0 else b r
  let K := thresholdSelectedMass d S w y
  let B := Finset.sum S c
  let T := Finset.sum S (fun r => c r * (y r - y j) ^ 2)
  let R := Finset.sum S (fun r => c r * (y r - y j))
  let mu := thresholdSelectedMean d S w y
  let V := thresholdSelectedVariance d S w y
  have hb : forall r, Membership.mem S r -> 0 <= b r := by
    intro r _
    dsimp only [b, w]
    apply mul_nonneg (mul_nonneg (by norm_num) (Nat.cast_nonneg _))
    unfold momentRoundIndicator
    split_ifs <;> norm_num
  have hc : forall r, Membership.mem S r -> 0 <= c r := by
    intro r hr
    dsimp only [c]
    split_ifs
    case pos => exact le_rfl
    case neg => exact hb r hr
  have hcBound : forall r, Membership.mem S r -> c r <= b r := by
    intro r hr
    dsimp only [c]
    split_ifs
    case pos => exact hb r hr
    case neg => exact le_rfl
  have hB : 2 <= B := by
    have hSingle := Finset.single_le_sum hc hi
    have hNat : 1 <= a i := hai
    have hReal : (1 : Real) <= (a i : Real) := by exact_mod_cast hNat
    simp only [c, ite_eq_right hNe, b, w, momentRoundIndicator, ite_eq_left hci, mul_one] at hSingle
    change _ <= B at hSingle
    linarith only [hReal, hSingle]
  have hA : 2 <= K - B := by
    have hNonneg : forall r, Membership.mem S r -> 0 <= b r - c r :=
      fun r hr => sub_nonneg.mpr (hcBound r hr)
    have hSingle := Finset.single_le_sum hNonneg hj
    have hNat : 1 <= a j := haj
    have hReal : (1 : Real) <= (a j : Real) := by exact_mod_cast hNat
    have hSum : Finset.sum S (fun r => b r - c r) = K - B := by
      rw [Finset.sum_sub_distrib]
      rfl
    rw [hSum] at hSingle
    simp only [c, ite_eq_left rfl, b, w, momentRoundIndicator, ite_eq_left hcj,
      mul_one, sub_zero] at hSingle
    linarith only [hReal, hSingle]
  have hK : 0 < K := by linarith only [hA, hB]
  have hT : B * g ^ 2 <= T := by
    calc
      _ = Finset.sum S (fun r => c r * g ^ 2) := by rw [Finset.sum_mul]
      _ <= _ := by
        apply Finset.sum_le_sum
        intro r hr
        by_cases hEq : y r = y j
        case pos => simp [c, hEq]
        case neg =>
          by_cases hp : 0 < a r
          case pos =>
            by_cases hCut : d <= y r
            case pos =>
              have hGap := hSeparated r j hr hj hp haj hCut hcj hEq
              have hSq : g ^ 2 <= (y r - y j) ^ 2 := by
                nlinarith only [sq_abs (y r - y j), sq_nonneg (abs (y r - y j) - g),
                  mul_nonneg hg (sub_nonneg.mpr hGap)]
              exact _root_.mul_le_mul_of_nonneg_left hSq (hc r hr)
            case neg => simp [c, b, momentRoundIndicator, hEq, hCut]
          case neg =>
            have hz : a r = 0 := Nat.eq_zero_of_not_pos hp
            simp [c, b, w, hz, hEq]
  have hCauchy := finiteWeightedSquareSum_le S c (fun r => y r - y j) hc
    (show 0 < Finset.sum S c by change 0 < B; linarith only [hB])
  change R ^ 2 <= B * T at hCauchy
  have hTFull : T = Finset.sum S (fun r => w r * thresholdTotalHighSquare d (y j) (y r)) := by
    apply Finset.sum_congr rfl
    intro r _
    dsimp only [c, b, thresholdTotalHighSquare]
    by_cases hEq : y r = y j
    case pos => simp [hEq]
    case neg => rw [ite_eq_right hEq]; ring
  have hRFull : R = K * (mu - y j) := by
    have hEach : forall r, c r * (y r - y j) = b r * y r - y j * b r := by
      intro r
      dsimp only [c]
      by_cases hEq : y r = y j
      case pos => simp [hEq]; ring
      case neg => rw [ite_eq_right hEq]; ring
    calc
      _ = Finset.sum S (fun r => b r * y r - y j * b r) :=
        Finset.sum_congr rfl (fun r _ => hEach r)
      _ = Finset.sum S (fun r => b r * y r) - y j * K := by
        rw [Finset.sum_sub_distrib, <- Finset.mul_sum]
        rfl
      _ = _ := by
        dsimp only [mu, thresholdSelectedMean]
        change Finset.sum S (fun r => b r * y r) - y j * K =
          K * (Finset.sum S (fun r => b r * y r) / K - y j)
        have hKn : Not (K = 0) := ne_of_gt hK
        field_simp [hKn]
  have hTVar : T = V + K * (mu - y j) ^ 2 := by
    rw [hTFull]
    exact finiteWeighted_selected_parallel_axis S w y d (y j) hK
  have hIdentity : K * T - R ^ 2 = K * V := by
    rw [hTVar, hRFull]
    ring
  have hTimes := _root_.mul_le_mul_of_nonneg_left hT (show 0 <= K - B by linarith only [hA])
  have hAB : 2 * (K - 2) <= (K - B) * B := by
    have hProduct := mul_nonneg (show 0 <= B - 2 by linarith only [hB])
      (show 0 <= K - B - 2 by linarith only [hA])
    nlinarith only [hProduct]
  have hABg := _root_.mul_le_mul_of_nonneg_right hAB (sq_nonneg g)
  change 2 * (K - 2) * g ^ 2 <= K * V
  nlinarith only [hCauchy, hIdentity, hTimes, hABg]

theorem finiteEven_selected_collision_rigidity {Iota : Type*} (S : Finset Iota)
    (a : Iota -> Nat) (y : Iota -> Real) (d g : Real)
    (hd : And (0 < d) (d < 1)) (hg : 0 <= g)
    (hMoment : Finset.sum S (fun i => 2 * (a i : Real) * (y i) ^ 2) =
      Finset.sum S (fun i => 2 * (a i : Real) * y i))
    (hK : 0 < thresholdSelectedMass d S (fun i => 2 * (a i : Real)) y)
    (hSeparated : thresholdSelectedSeparated d S a y g)
    (hSmall :
      let w := fun i => 2 * (a i : Real)
      let N := Finset.sum S w
      let K := thresholdSelectedMass d S w y
      let v := thresholdModelHigh (N - K) K d
      thresholdVarianceBudget d v K
        (thresholdTotalUpper d N K - Finset.sum S (fun i => w i * y i)) <
          2 * (K - 2) * g ^ 2 / K) :
    exists j, And (Membership.mem S j) (And (0 < a j) (And (d <= y j)
      (And (forall i, Membership.mem S i -> 0 < a i -> d <= y i -> y i = y j)
        (thresholdSelectedDirac d S (fun i => 2 * (a i : Real)) y (y j))))) := by
  classical
  let w := fun r => 2 * (a r : Real)
  let b := fun r => w r * momentRoundIndicator d (y r)
  let K := thresholdSelectedMass d S w y
  have ha : forall r, Membership.mem S r -> 0 <= w r :=
    fun r _ => mul_nonneg (by norm_num) (Nat.cast_nonneg _)
  have hb : forall r, Membership.mem S r -> 0 <= b r := by
    intro r hr
    apply mul_nonneg (ha r hr)
    unfold momentRoundIndicator
    split_ifs <;> norm_num
  choose j hj hp using (Finset.sum_pos_iff_of_nonneg hb).mp hK
  have hcj : d <= y j := by
    by_contra hn
    simp [b, momentRoundIndicator, hn] at hp
  have haj : 0 < a j := by
    by_contra hn
    have hz : a j = 0 := Nat.eq_zero_of_not_pos hn
    simp [b, w, hz] at hp
  have hSame : forall i, Membership.mem S i -> 0 < a i -> d <= y i -> y i = y j := by
    intro i hi hai hci
    by_contra hNe
    have hGap := finiteEven_selected_separation_variance S a y d g hg hSeparated
      j i hj hi haj hai hcj hci hNe
    have hUpper := finiteWeighted_selected_variance_budget S w y d hd ha hMoment hK
    have hScaled := _root_.mul_lt_mul_of_pos_left hSmall hK
    have hDen : K * (2 * (K - 2) * g ^ 2 / K) = 2 * (K - 2) * g ^ 2 := by
      have hKn : Not (K = 0) := ne_of_gt hK
      field_simp [hKn]
    have hUpperScaled := _root_.mul_le_mul_of_nonneg_left hUpper (le_of_lt hK)
    rw [hDen] at hScaled
    exact (not_lt_of_ge (le_trans hGap hUpperScaled)) hScaled
  refine Exists.intro j (And.intro hj (And.intro haj (And.intro hcj (And.intro hSame ?_))))
  intro phi
  calc
    _ = Finset.sum S (fun i => b i * phi (y j)) := by
      apply Finset.sum_congr rfl
      intro i hi
      change b i * phi (y i) = b i * phi (y j)
      by_cases hCut : d <= y i
      case pos =>
        by_cases hai : 0 < a i
        case pos => rw [hSame i hi hai hCut]
        case neg =>
          have hz : a i = 0 := Nat.eq_zero_of_not_pos hai
          simp [b, w, hz]
      case neg => simp [b, momentRoundIndicator, hCut]
    _ = _ := by rw [<- Finset.sum_mul]; rfl

theorem finiteEven_selected_collision_linear {Iota : Type*} (S : Finset Iota)
    (a : Iota -> Nat) (y : Iota -> Real) (d g : Real)
    (hd : And (0 < d) (d < 1)) (hg : 0 <= g)
    (hMoment : Finset.sum S (fun i => 2 * (a i : Real) * (y i) ^ 2) =
      Finset.sum S (fun i => 2 * (a i : Real) * y i))
    (hK : 0 < thresholdSelectedMass d S (fun i => 2 * (a i : Real)) y)
    (hSeparated : thresholdSelectedSeparated d S a y g)
    (hSmall :
      let w := fun i => 2 * (a i : Real)
      let N := Finset.sum S w
      let K := thresholdSelectedMass d S w y
      let v := thresholdModelHigh (N - K) K d
      thresholdVarianceBudget d v K
        (thresholdTotalUpper d N K - Finset.sum S (fun i => w i * y i)) <
          2 * (K - 2) * g ^ 2 / K) :
    let w := fun i => 2 * (a i : Real)
    let N := Finset.sum S w
    let K := thresholdSelectedMass d S w y
    let v := thresholdModelHigh (N - K) K d
    forall phi : Real -> Real,
      (forall u z : Real, abs (phi u - phi z) <= abs (u - z)) ->
      abs (Finset.sum S (fun i => w i * phi (y i)) -
        thresholdTotalStatistic d v N K phi) <=
          thresholdSingleCoefficient d v *
            (thresholdTotalUpper d N K - Finset.sum S (fun i => w i * y i)) := by
  choose j hj haj hcj hSame hDirac using finiteEven_selected_collision_rigidity
    S a y d g hd hg hMoment hK hSeparated hSmall
  exact (finiteWeighted_single_level_linear S (fun i => 2 * (a i : Real)) y d (y j)
    hd (fun i _ => mul_nonneg (by norm_num) (Nat.cast_nonneg _))
      hMoment hK hDirac).2.2.2

end PrimeFactorOscillations

/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.ThresholdFeasibilityEnvelope
import PrimeFactorOscillations.Mathlib.Algebra.Order.BigOperators.Ring.WeightedConcentration

/-! # Linear threshold-profile stability from integer feasibility slack -/

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 5000000

noncomputable section
namespace PrimeFactorOscillations

theorem finiteEven_atom_concentration {Iota : Type*} (S : Finset Iota)
    (a : Iota -> Nat) (x : Iota -> Real)
    (hx : forall i, Membership.mem S i -> 0 <= x i)
    (hX : 0 < Finset.sum S (fun i => 2 * (a i : Real) * x i))
    (hSmall : (Finset.sum S (fun i => 2 * (a i : Real) * x i)) ^ 2 -
        2 * Finset.sum S (fun i => 2 * (a i : Real) * (x i) ^ 2) <
      (Finset.sum S (fun i => 2 * (a i : Real) * x i)) ^ 2 / 2) :
    exists j, And (Membership.mem S j) (And (a j = 1) (And (0 < x j)
      (And (forall i, Membership.mem S i -> 0 < a i -> x i <= x j)
        (And (0 <= Finset.sum S (fun i => 2 * (a i : Real) * x i) - 2 * x j)
          ((Finset.sum S (fun i => 2 * (a i : Real) * x i)) *
              (Finset.sum S (fun i => 2 * (a i : Real) * x i) - 2 * x j) <=
            (Finset.sum S (fun i => 2 * (a i : Real) * x i)) ^ 2 -
              2 * Finset.sum S (fun i => 2 * (a i : Real) * (x i) ^ 2)))))) := by
  classical
  let T := Finset.sum S (fun i => (a i : Real) * x i)
  let V := Finset.sum S (fun i => (a i : Real) * (x i) ^ 2)
  have hFirst : Finset.sum S (fun i => 2 * (a i : Real) * x i) = 2 * T := by
    dsimp only [T]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    ring
  have hSecond : Finset.sum S (fun i => 2 * (a i : Real) * (x i) ^ 2) = 2 * V := by
    dsimp only [V]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    ring
  have hT : 0 < T := by rw [hFirst] at hX; linarith only [hX]
  have hTiny : T ^ 2 - V < T ^ 2 / 2 := by
    rw [hFirst, hSecond] at hSmall
    nlinarith only [hSmall]
  choose j hj hjOne hjX hMax hR hDef using
    Finset.exists_unit_weight_of_small_square_defect S a x hx hT hTiny
  rw [hFirst, hSecond]
  exact Exists.intro j (And.intro hj (And.intro hjOne (And.intro hjX
    (And.intro hMax (And.intro (by linarith only [hR]) (by nlinarith only [hDef]))))))

def thresholdFeasibilitySlack (d M K : Real) : Real :=
  (M - d * K) ^ 2 + (4 * d - 2) * M - 2 * d ^ 2 * K

def thresholdFeasibilityStatistic (d M K N : Real) (phi : Real -> Real) : Real :=
  (N - K) * phi 0 + (K - 2) * phi d + 2 * phi (d + (M - d * K) / 2)

theorem thresholdFeasibilityReference_moments (d M K N : Real) :
    And (thresholdFeasibilityStatistic d M K N (fun _ => 1) = N)
      (And (thresholdFeasibilityStatistic d M K N (fun x => x) = M)
        (thresholdFeasibilityStatistic d M K N (fun x => x ^ 2) =
          M + thresholdFeasibilitySlack d M K / 2)) := by
  dsimp [thresholdFeasibilityStatistic, thresholdFeasibilitySlack]
  refine And.intro ?_ (And.intro ?_ ?_) <;> ring

theorem finiteWeighted_threshold_slack_identity {Iota : Type*} (S : Finset Iota)
    (a y : Iota -> Real) (d : Real)
    (hMoment : Finset.sum S (fun i => a i * (y i) ^ 2) = Finset.sum S (fun i => a i * y i)) :
    let M := Finset.sum S (fun i => a i * y i)
    let K := thresholdSelectedMass d S a y
    let X := Finset.sum S (fun i => a i * thresholdExcess d (y i))
    let Y := Finset.sum S (fun i => a i * thresholdLow d (y i))
    let U := Finset.sum S (fun i => a i * (thresholdExcess d (y i)) ^ 2)
    let V := Finset.sum S (fun i => a i * ((y i) ^ 2 * (1 - momentRoundIndicator d (y i))))
    thresholdFeasibilitySlack d M K =
      (X ^ 2 - 2 * U) + 2 * X * Y + Y ^ 2 + 2 * d * Y + 2 * (d * Y - V) := by
  dsimp only
  have hLedger := finiteWeighted_threshold_ledger S a y d
  rw [hMoment] at hLedger
  have hA : Finset.sum S (fun i => a i * y i) - d * thresholdSelectedMass d S a y =
      Finset.sum S (fun i => a i * thresholdExcess d (y i)) +
        Finset.sum S (fun i => a i * thresholdLow d (y i)) := by
    linarith only [hLedger.1]
  have hScale := congrArg (fun q : Real => 4 * d * q) hLedger.1
  unfold thresholdFeasibilitySlack
  rw [hA]
  nlinarith only [hLedger.2, hScale]

theorem finiteEven_threshold_slack_control {Iota : Type*} (S : Finset Iota)
    (a : Iota -> Nat) (y : Iota -> Real) (d : Real) (hd : 0 <= d)
    (hy : forall i, Membership.mem S i -> 0 <= y i)
    (hMoment : Finset.sum S (fun i => 2 * (a i : Real) * (y i) ^ 2) =
      Finset.sum S (fun i => 2 * (a i : Real) * y i)) :
    let M := Finset.sum S (fun i => 2 * (a i : Real) * y i)
    let K := thresholdSelectedMass d S (fun i => 2 * (a i : Real)) y
    let X := Finset.sum S (fun i => 2 * (a i : Real) * thresholdExcess d (y i))
    let Y := Finset.sum S (fun i => 2 * (a i : Real) * thresholdLow d (y i))
    let U := Finset.sum S (fun i => 2 * (a i : Real) * (thresholdExcess d (y i)) ^ 2)
    And (M - d * K = X + Y) (And (0 <= X) (And (0 <= Y)
      (And (0 <= X ^ 2 - 2 * U)
        (And (X ^ 2 - 2 * U <= thresholdFeasibilitySlack d M K)
          (2 * d * Y <= thresholdFeasibilitySlack d M K))))) := by
  dsimp only
  let w := fun i => 2 * (a i : Real)
  let X := Finset.sum S (fun i => w i * thresholdExcess d (y i))
  let Y := Finset.sum S (fun i => w i * thresholdLow d (y i))
  let U := Finset.sum S (fun i => w i * (thresholdExcess d (y i)) ^ 2)
  let V := Finset.sum S (fun i => w i * ((y i) ^ 2 * (1 - momentRoundIndicator d (y i))))
  have hw : forall i, 0 <= w i := fun i =>
    mul_nonneg (show (0 : Real) <= 2 by norm_num) (Nat.cast_nonneg (a i))
  have hX : 0 <= X := Finset.sum_nonneg
    (fun i _ => mul_nonneg (hw i) (thresholdExcess_nonneg d (y i)))
  have hY : 0 <= Y := Finset.sum_nonneg
    (fun i hi => mul_nonneg (hw i) (thresholdLow_nonneg d (y i) (hy i hi)))
  have hAtom : forall i, Membership.mem S i -> Or (w i = 0) (2 <= w i) := by
    intro i _
    by_cases hz : a i = 0
    case pos => exact Or.inl (by simp [w, hz])
    case neg =>
      have hn : 1 <= a i := Nat.one_le_iff_ne_zero.mpr hz
      have hr : (1 : Real) <= (a i : Real) := by exact_mod_cast hn
      exact Or.inr (by dsimp [w]; linarith only [hr])
  have hSquare := finiteWeighted_atom_square S w (fun i => thresholdExcess d (y i))
    (fun i _ => hw i) (fun i _ => thresholdExcess_nonneg d (y i)) hAtom
  have hDefect : 0 <= X ^ 2 - 2 * U := by linarith only [hSquare]
  have hEachLow : forall i, Membership.mem S i ->
      w i * ((y i) ^ 2 * (1 - momentRoundIndicator d (y i))) <= d * (w i * thresholdLow d (y i)) := by
    intro i hi
    have hm := mul_le_mul_of_nonneg_left (thresholdLow_square d (y i) (hy i hi)) (hw i)
    nlinarith only [hm]
  have hLow : V <= d * Y := by
    have hs := Finset.sum_le_sum hEachLow
    simpa only [<- Finset.mul_sum, V, Y] using hs
  have hId := finiteWeighted_threshold_slack_identity S w y d hMoment
  have hXY := mul_nonneg hX hY
  have hDY := mul_nonneg hd hY
  have hF : X ^ 2 - 2 * U <=
      thresholdFeasibilitySlack d (Finset.sum S (fun i => w i * y i)) (thresholdSelectedMass d S w y) := by
    nlinarith only [hId, hXY, hDY, sq_nonneg Y, hLow]
  have hLF : 2 * d * Y <=
      thresholdFeasibilitySlack d (Finset.sum S (fun i => w i * y i)) (thresholdSelectedMass d S w y) := by
    nlinarith only [hId, hXY, hDefect, sq_nonneg Y, hLow]
  have hLedger := finiteWeighted_threshold_ledger S w y d
  exact And.intro (by linarith only [hLedger.1]) (And.intro hX (And.intro hY
    (And.intro hDefect (And.intro hF hLF))))


theorem finiteEven_threshold_lipschitz_reference {Iota : Type*} (S : Finset Iota)
    (a : Iota -> Nat) (y : Iota -> Real) (d : Real)
    (hy : forall i, Membership.mem S i -> 0 <= y i)
    (j : Iota) (hj : Membership.mem S j) (hjOne : a j = 1) (hjCut : d <= y j)
    (phi : Real -> Real)
    (hLip : forall u v : Real, abs (phi u - phi v) <= abs (u - v)) :
    let M := Finset.sum S (fun i => 2 * (a i : Real) * y i)
    let K := thresholdSelectedMass d S (fun i => 2 * (a i : Real)) y
    let N := Finset.sum S (fun i => 2 * (a i : Real))
    let X := Finset.sum S (fun i => 2 * (a i : Real) * thresholdExcess d (y i))
    let Y := Finset.sum S (fun i => 2 * (a i : Real) * thresholdLow d (y i))
    abs (Finset.sum S (fun i => 2 * (a i : Real) * phi (y i)) -
      thresholdFeasibilityStatistic d M K N phi) <=
        2 * (Y + (X - 2 * (y j - d))) := by
  classical
  dsimp only
  let w := fun i => 2 * (a i : Real)
  let M := Finset.sum S (fun i => w i * y i)
  let K := thresholdSelectedMass d S w y
  let N := Finset.sum S w
  let X := Finset.sum S (fun i => w i * thresholdExcess d (y i))
  let Y := Finset.sum S (fun i => w i * thresholdLow d (y i))
  let R := X - 2 * (y j - d)
  let c := d + (M - d * K) / 2
  let r := fun i => phi (y i) - phi 0 - momentRoundIndicator d (y i) * (phi d - phi 0)
  have hw : forall i, 0 <= w i := fun i =>
    mul_nonneg (show (0 : Real) <= 2 by norm_num) (Nat.cast_nonneg (a i))
  have hWj : w j = 2 := by simp only [w, hjOne, Nat.cast_one, mul_one]
  have hExj : thresholdExcess d (y j) = y j - d := by
    simp [thresholdExcess, momentRoundIndicator, hjCut]
  have hLowj : thresholdLow d (y j) = 0 := by
    simp [thresholdLow, momentRoundIndicator, hjCut]
  have hrj : r j = phi (y j) - phi d := by
    dsimp [r]
    rw [momentRoundIndicator, ite_eq_left hjCut]
    ring
  have hPoint : forall i, Membership.mem S i ->
      w i * phi (y i) = w i * phi 0 +
        (phi d - phi 0) * (w i * momentRoundIndicator d (y i)) + w i * r i := by
    intro i _
    dsimp [r]
    ring
  have hSum := Finset.sum_congr rfl hPoint
  simp only [Finset.sum_add_distrib, <- Finset.sum_mul, <- Finset.mul_sum] at hSum
  change Finset.sum S (fun i => w i * phi (y i)) =
    N * phi 0 + (phi d - phi 0) * K + Finset.sum S (fun i => w i * r i) at hSum
  have hErase := Finset.sum_erase_add S (fun i => w i * r i) hj
  rw [hWj, hrj] at hErase
  have hDiff : Finset.sum S (fun i => w i * phi (y i)) -
      thresholdFeasibilityStatistic d M K N phi =
        Finset.sum (S.erase j) (fun i => w i * r i) + 2 * (phi (y j) - phi c) := by
    dsimp only [thresholdFeasibilityStatistic, c]
    nlinarith only [hSum, hErase]
  have hrBound : forall i, Membership.mem S i ->
      abs (r i) <= thresholdExcess d (y i) + thresholdLow d (y i) := by
    intro i hi
    by_cases hCut : d <= y i
    case pos =>
      have hri : r i = phi (y i) - phi d := by
        dsimp [r]
        rw [momentRoundIndicator, ite_eq_left hCut]
        ring
      rw [hri]
      have hp := hLip (y i) d
      simpa only [thresholdExcess, thresholdLow, momentRoundIndicator, ite_eq_left hCut,
        mul_one, sub_self, mul_zero, add_zero, abs_of_nonneg (sub_nonneg.mpr hCut)] using hp
    case neg =>
      have hri : r i = phi (y i) - phi 0 := by
        simp [r, momentRoundIndicator, hCut]
      rw [hri]
      have hp := hLip (y i) 0
      simpa only [thresholdExcess, thresholdLow, momentRoundIndicator, ite_eq_right hCut,
        mul_zero, sub_zero, mul_one, zero_add, abs_of_nonneg (hy i hi)] using hp
  let f := fun i => w i * (thresholdExcess d (y i) + thresholdLow d (y i))
  have hf : forall i, Membership.mem S i -> 0 <= f i := by
    intro i hi
    exact mul_nonneg (hw i) (add_nonneg (thresholdExcess_nonneg d (y i))
      (thresholdLow_nonneg d (y i) (hy i hi)))
  have hFsum : Finset.sum S f = X + Y := by
    simp only [f, mul_add, Finset.sum_add_distrib, X, Y]
  have hFj : f j = 2 * (y j - d) := by
    simp only [f, hWj, hExj, hLowj, add_zero]
  have hFerase := Finset.sum_erase_add S f hj
  rw [hFsum, hFj] at hFerase
  have hRest : Finset.sum (S.erase j) f = R + Y := by
    dsimp only [R]
    linarith only [hFerase]
  have hRY : 0 <= R + Y := by
    rw [<- hRest]
    exact Finset.sum_nonneg (fun i hi => hf i (Finset.mem_of_mem_erase hi))
  have hRestBound : abs (Finset.sum (S.erase j) (fun i => w i * r i)) <= R + Y := by
    calc
      _ <= Finset.sum (S.erase j) (fun i => abs (w i * r i)) :=
        Finset.abs_sum_le_sum_abs _ _
      _ <= Finset.sum (S.erase j) f := by
        apply Finset.sum_le_sum
        intro i hi
        rw [abs_mul, abs_of_nonneg (hw i)]
        exact mul_le_mul_of_nonneg_left (hrBound i (Finset.mem_of_mem_erase hi)) (hw i)
      _ = _ := hRest
  have hLedger := (finiteWeighted_threshold_ledger S w y d).1
  have hc : 2 * (c - y j) = R + Y := by
    dsimp only [c, R]
    change M = d * K + X + Y at hLedger
    linarith only [hLedger]
  have hcNonneg : 0 <= c - y j := by linarith only [hc, hRY]
  have hDistance : 2 * abs (y j - c) = R + Y := by
    rw [abs_of_nonpos (by linarith only [hcNonneg])]
    linarith only [hc]
  have hPhi := hLip (y j) c
  have hPhiBound : abs (2 * (phi (y j) - phi c)) <= 2 * abs (y j - c) := by
    rw [abs_mul, abs_of_nonneg (show (0 : Real) <= 2 by norm_num)]
    exact mul_le_mul_of_nonneg_left hPhi (by norm_num)
  have hTriangle := abs_add_le (Finset.sum (S.erase j) (fun i => w i * r i))
    (2 * (phi (y j) - phi c))
  change abs (Finset.sum S (fun i => w i * phi (y i)) -
    thresholdFeasibilityStatistic d M K N phi) <= 2 * (Y + R)
  rw [hDiff]
  linarith only [hTriangle, hRestBound, hPhiBound, hDistance]


theorem thresholdEvenAdmissible_linear_stability {n : Nat} (d M K : Real)
    (a : Fin n -> Nat) (y : Fin n -> Real) (hd : And (0 < d) (d < 1))
    (hM : 0 < M) (hAd : thresholdEvenAdmissible d M K a y)
    (hLowSlack : thresholdFeasibilitySlack d M K <= d * (M - d * K))
    (hTinySlack : thresholdFeasibilitySlack d M K < (M - d * K) ^ 2 / 8) :
    let N := Finset.sum Finset.univ (fun i => 2 * (a i : Real))
    And (2 <= K) (And (K <= N)
      (And (exists j : Fin n, And (a j = 1) (d < y j))
        (forall phi : Real -> Real,
          (forall u v : Real, abs (phi u - phi v) <= abs (u - v)) ->
            abs (Finset.sum Finset.univ (fun i => 2 * (a i : Real) * phi (y i)) -
              thresholdFeasibilityStatistic d M K N phi) <=
                thresholdFeasibilitySlack d M K / d + 4 * thresholdFeasibilitySlack d M K / (M - d * K)))) := by
  classical
  dsimp only
  let w := fun i => 2 * (a i : Real)
  let N := Finset.sum Finset.univ w
  let A := M - d * K
  let P := thresholdFeasibilitySlack d M K
  let X := Finset.sum Finset.univ (fun i => w i * thresholdExcess d (y i))
  let Y := Finset.sum Finset.univ (fun i => w i * thresholdLow d (y i))
  let U := Finset.sum Finset.univ (fun i => w i * (thresholdExcess d (y i)) ^ 2)
  have hw : forall i, 0 <= w i := fun i =>
    mul_nonneg (show (0 : Real) <= 2 by norm_num) (Nat.cast_nonneg (a i))
  have hMv : Finset.sum Finset.univ (fun i => w i * y i) = M := hAd.2.1
  have hKv : thresholdSelectedMass d Finset.univ w y = K := hAd.2.2.2
  have hMoment : Finset.sum Finset.univ (fun i => w i * (y i) ^ 2) =
      Finset.sum Finset.univ (fun i => w i * y i) := hAd.2.2.1.trans hAd.2.1.symm
  have hDomain := finiteWeightedThreshold_domain Finset.univ w y d hd.2
    (fun i _ => hw i) (fun i _ => hAd.1 i) hMoment (by rw [hMv]; exact hM)
  rw [hMv, hKv] at hDomain
  have hA : 0 < A := sub_pos.mpr hDomain.2
  have hControl := finiteEven_threshold_slack_control Finset.univ a y d hd.1.le
    (fun i _ => hAd.1 i) hMoment
  dsimp only at hControl
  rw [hMv, hKv] at hControl
  have hXY : A = X + Y := hControl.1
  have hX0 : 0 <= X := hControl.2.1
  have hY0 : 0 <= Y := hControl.2.2.1
  have hDF : X ^ 2 - 2 * U <= P := hControl.2.2.2.2.1
  have hYF : 2 * d * Y <= P := hControl.2.2.2.2.2
  have hLow : P <= d * A := hLowSlack
  have hTiny : P < A ^ 2 / 8 := hTinySlack
  have h2Y : 2 * Y <= A := by
    by_contra hn
    have hm := mul_pos hd.1 (sub_pos.mpr (lt_of_not_ge hn))
    nlinarith only [hYF, hLow, hm]
  have h2X : A <= 2 * X := by linarith only [hXY, h2Y]
  have hX : 0 < X := by linarith only [hA, h2X]
  have hSquare := mul_nonneg (sub_nonneg.mpr h2X) (by linarith only [hX0, hA] : 0 <= 2 * X + A)
  have hSmall : X ^ 2 - 2 * U < X ^ 2 / 2 := by
    nlinarith only [hDF, hTiny, hSquare]
  choose j hj hjOne hjEx _hMax hR hDef using finiteEven_atom_concentration Finset.univ a
    (fun i => thresholdExcess d (y i)) (fun i _ => thresholdExcess_nonneg d (y i)) hX hSmall
  have hjCut : d < y j := by
    by_cases hc : d <= y j
    case pos => simpa only [thresholdExcess, momentRoundIndicator, ite_eq_left hc, mul_one, sub_pos] using hjEx
    case neg => simp [thresholdExcess, momentRoundIndicator, hc] at hjEx
  have hExj : thresholdExcess d (y j) = y j - d := by
    simp [thresholdExcess, momentRoundIndicator, hjCut.le]
  rw [hExj] at hR hDef
  let R := X - 2 * (y j - d)
  have hRD : X * R <= P := le_trans hDef hDF
  have hR0 : 0 <= R := hR
  have hAR : A * R <= 2 * P := by
    have hm := mul_nonneg (sub_nonneg.mpr h2X) hR0
    nlinarith only [hRD, hm]
  have hRBound : R <= 2 * P / A := by
    have hc : (2 * P / A) * A = 2 * P := by field_simp [hA.ne']
    by_contra hn
    have hm := mul_pos (sub_pos.mpr (lt_of_not_ge hn)) hA
    nlinarith only [hc, hAR, hm]
  have hYBound : Y <= P / (2 * d) := by
    have hc : (P / (2 * d)) * (2 * d) = P := by field_simp [hd.1.ne']
    by_contra hn
    have hm := mul_pos (sub_pos.mpr (lt_of_not_ge hn)) (by linarith only [hd.1] : 0 < 2 * d)
    nlinarith only [hc, hYF, hm]
  have hWj : w j = 2 := by simp only [w, hjOne, Nat.cast_one, mul_one]
  have hSelNonneg : forall i : Fin n, Membership.mem Finset.univ i ->
      0 <= w i * momentRoundIndicator d (y i) := by
    intro i _
    by_cases hc : d <= y i <;> simp [momentRoundIndicator, hc, hw i]
  have hKlow : 2 <= K := by
    have hs := Finset.single_le_sum hSelNonneg hj
    rw [hWj] at hs
    simpa only [momentRoundIndicator, ite_eq_left hjCut.le, mul_one, <- hKv, thresholdSelectedMass] using hs
  have hKtotal : K <= N := by
    have hEach : forall i : Fin n, Membership.mem Finset.univ i ->
        w i * momentRoundIndicator d (y i) <= w i := by
      intro i _
      by_cases hc : d <= y i <;> simp [momentRoundIndicator, hc, hw i]
    have hs := Finset.sum_le_sum hEach
    change thresholdSelectedMass d Finset.univ w y <= N at hs
    rw [hKv] at hs
    exact hs
  refine And.intro hKlow (And.intro hKtotal (And.intro (Exists.intro j (And.intro hjOne hjCut)) ?_))
  intro phi hLip
  have ht := finiteEven_threshold_lipschitz_reference Finset.univ a y d (fun i _ => hAd.1 i)
    j hj hjOne hjCut.le phi hLip
  dsimp only at ht
  rw [hMv, hKv] at ht
  change abs (Finset.sum Finset.univ (fun i => w i * phi (y i)) -
    thresholdFeasibilityStatistic d M K N phi) <= 2 * (Y + R) at ht
  have hCombine : 2 * (P / (2 * d) + 2 * P / A) = P / d + 4 * P / A := by
    field_simp [hd.1.ne', hA.ne']
    ring
  change abs (Finset.sum Finset.univ (fun i => w i * phi (y i)) -
    thresholdFeasibilityStatistic d M K N phi) <= P / d + 4 * P / A
  linarith only [ht, hYBound, hRBound, hCombine]


theorem thresholdEvenAdmissible_zero_slack_statistic {n : Nat} (d M K : Real)
    (a : Fin n -> Nat) (y : Fin n -> Real) (hd : And (0 < d) (d < 1))
    (hM : 0 < M) (hAd : thresholdEvenAdmissible d M K a y)
    (hZero : thresholdFeasibilitySlack d M K = 0) :
    let N := Finset.sum Finset.univ (fun i => 2 * (a i : Real))
    And (exists j : Fin n, And (a j = 1) (d < y j))
      (forall phi : Real -> Real,
        (forall u v : Real, abs (phi u - phi v) <= abs (u - v)) ->
          Finset.sum Finset.univ (fun i => 2 * (a i : Real) * phi (y i)) =
            thresholdFeasibilityStatistic d M K N phi) := by
  dsimp only
  have hw : forall i : Fin n, Membership.mem Finset.univ i -> 0 <= 2 * (a i : Real) :=
    fun i _ => mul_nonneg (by norm_num) (Nat.cast_nonneg (a i))
  have hm : Finset.sum Finset.univ (fun i => 2 * (a i : Real) * (y i) ^ 2) =
      Finset.sum Finset.univ (fun i => 2 * (a i : Real) * y i) := hAd.2.2.1.trans hAd.2.1.symm
  have hD := finiteWeightedThreshold_domain Finset.univ (fun i => 2 * (a i : Real)) y d hd.2
    hw (fun i _ => hAd.1 i) hm (by rw [hAd.2.1]; exact hM)
  rw [hAd.2.1, hAd.2.2.2] at hD
  have hA : 0 < M - d * K := sub_pos.mpr hD.2
  have hLow : thresholdFeasibilitySlack d M K <= d * (M - d * K) := by
    rw [hZero]
    exact mul_nonneg hd.1.le hA.le
  have hTiny : thresholdFeasibilitySlack d M K < (M - d * K) ^ 2 / 8 := by
    rw [hZero]
    exact div_pos (sq_pos_of_pos hA) (by norm_num)
  have h := thresholdEvenAdmissible_linear_stability d M K a y hd hM hAd hLow hTiny
  refine And.intro h.2.2.1 ?_
  intro phi hLip
  have hb := h.2.2.2 phi hLip
  rw [hZero, zero_div, mul_zero, zero_div, zero_add] at hb
  exact sub_eq_zero.mp (abs_eq_zero.mp (le_antisymm hb (abs_nonneg _)))

end PrimeFactorOscillations

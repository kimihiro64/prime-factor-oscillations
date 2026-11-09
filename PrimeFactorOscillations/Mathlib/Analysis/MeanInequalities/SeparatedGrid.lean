/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.FieldSimp
import PrimeFactorOscillations.Mathlib.Analysis.MeanInequalities.SeparatedVariance

/-! # Sharp weighted variance for separated real sites at every support size -/

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 5000000

noncomputable section
namespace Finset

def separatedGridCoord (r : Nat) (i : Fin r) : Real :=
  (i.val : Real) - ((r : Real) - 1) / 2

def separatedGridParity (r : Nat) : Real :=
  if r % 2 = 0 then 1 / 4 else 0

theorem sum_range_real_id (r : Nat) :
    Finset.sum (Finset.range r) (fun i => (i : Real)) =
      (r : Real) * ((r : Real) - 1) / 2 := by
  induction r with
  | zero => simp
  | succ r ih =>
    rw [Finset.sum_range_succ, ih]
    simp only [Nat.cast_succ]
    ring

theorem sum_range_real_sq (r : Nat) :
    Finset.sum (Finset.range r) (fun i => (i : Real) ^ 2) =
      (r : Real) * ((r : Real) - 1) * (2 * (r : Real) - 1) / 6 := by
  induction r with
  | zero => simp
  | succ r ih =>
    rw [Finset.sum_range_succ, ih]
    simp only [Nat.cast_succ]
    ring

theorem separatedGridCoord_sum (r : Nat) :
    Finset.sum Finset.univ (separatedGridCoord r) = 0 := by
  have hId : Finset.sum Finset.univ (fun i : Fin r => (i.val : Real)) =
      (r : Real) * ((r : Real) - 1) / 2 :=
    (Fin.sum_univ_eq_sum_range (fun i => (i : Real)) r).trans (sum_range_real_id r)
  unfold separatedGridCoord
  rw [Finset.sum_sub_distrib, hId]
  simp only [Finset.sum_const, nsmul_eq_mul, Finset.card_univ, Fintype.card_fin]
  ring

theorem separatedGridCoord_sum_sq (r : Nat) :
    Finset.sum Finset.univ (fun i => (separatedGridCoord r i) ^ 2) =
      (r : Real) * ((r : Real) ^ 2 - 1) / 12 := by
  let c := ((r : Real) - 1) / 2
  have hId : Finset.sum Finset.univ (fun i : Fin r => (i.val : Real)) =
      (r : Real) * ((r : Real) - 1) / 2 :=
    (Fin.sum_univ_eq_sum_range (fun i => (i : Real)) r).trans (sum_range_real_id r)
  have hSq : Finset.sum Finset.univ (fun i : Fin r => (i.val : Real) ^ 2) =
      (r : Real) * ((r : Real) - 1) * (2 * (r : Real) - 1) / 6 :=
    (Fin.sum_univ_eq_sum_range (fun i => (i : Real) ^ 2) r).trans (sum_range_real_sq r)
  calc
    _ = Finset.sum Finset.univ (fun i : Fin r =>
        (i.val : Real) ^ 2 - 2 * c * (i.val : Real) + c ^ 2) := by
      apply Finset.sum_congr rfl
      intro i _
      dsimp only [separatedGridCoord, c]
      ring
    _ = Finset.sum Finset.univ (fun i : Fin r => (i.val : Real) ^ 2) -
        2 * c * Finset.sum Finset.univ (fun i : Fin r => (i.val : Real)) +
          (r : Real) * c ^ 2 := by
      rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, <- Finset.mul_sum]
      simp only [Finset.sum_const, nsmul_eq_mul, Finset.card_univ, Fintype.card_fin]
    _ = _ := by
      rw [hId, hSq]
      dsimp only [c]
      ring

theorem separatedGridParity_le_sq (r : Nat) (i : Fin r) :
    separatedGridParity r <= (separatedGridCoord r i) ^ 2 := by
  by_cases hr : r % 2 = 0
  case pos =>
    rw [separatedGridParity, ite_eq_left hr]
    have hCount : r = 2 * (r / 2) := by omega
    have hCountR : (r : Real) = 2 * ((r / 2 : Nat) : Real) := by exact_mod_cast hCount
    by_cases hi : i.val < r / 2
    case pos =>
      have hIndex : i.val + 1 <= r / 2 := hi
      have hIndexR : (i.val : Real) + 1 <= ((r / 2 : Nat) : Real) := by exact_mod_cast hIndex
      have hZ : separatedGridCoord r i <= -1 / 2 := by
        dsimp only [separatedGridCoord]
        linarith only [hCountR, hIndexR]
      nlinarith only [hZ, sq_nonneg (separatedGridCoord r i + 1 / 2)]
    case neg =>
      have hIndex : r / 2 <= i.val := le_of_not_gt hi
      have hIndexR : ((r / 2 : Nat) : Real) <= (i.val : Real) := by exact_mod_cast hIndex
      have hZ : 1 / 2 <= separatedGridCoord r i := by
        dsimp only [separatedGridCoord]
        linarith only [hCountR, hIndexR]
      nlinarith only [hZ, sq_nonneg (separatedGridCoord r i - 1 / 2)]
  case neg =>
    rw [separatedGridParity, ite_eq_right hr]
    exact sq_nonneg _

theorem separatedGridParity_attained (r : Nat) (hr : 0 < r) :
    exists j : Fin r, (separatedGridCoord r j) ^ 2 = separatedGridParity r := by
  let j : Fin r := Fin.mk ((r - 1) / 2) (by omega)
  refine Exists.intro j ?_
  by_cases hEven : r % 2 = 0
  case pos =>
    have hCount : r = 2 * ((r - 1) / 2) + 2 := by omega
    have hCountR : (r : Real) = 2 * (((r - 1) / 2 : Nat) : Real) + 2 := by exact_mod_cast hCount
    rw [separatedGridParity, ite_eq_left hEven]
    dsimp only [separatedGridCoord, j]
    rw [hCountR]
    ring
  case neg =>
    have hCount : r = 2 * ((r - 1) / 2) + 1 := by omega
    have hCountR : (r : Real) = 2 * (((r - 1) / 2 : Nat) : Real) + 1 := by exact_mod_cast hCount
    rw [separatedGridParity, ite_eq_right hEven]
    dsimp only [separatedGridCoord, j]
    rw [hCountR]
    ring

theorem weighted_separatedGrid_lower (r : Nat) (w : Fin r -> Real) (q : Real)
    (hq : 0 <= q) (hw : forall i, q <= w i) :
    let K := Finset.sum Finset.univ w
    q * K * ((r : Real) * ((r : Real) ^ 2 - 1) / 12) +
      q * (r : Real) * (K - q * (r : Real)) * separatedGridParity r <=
        weightedVarianceNumerator Finset.univ w (separatedGridCoord r) := by
  have h := weighted_variance_baseline_lower Finset.univ w (separatedGridCoord r)
    q (separatedGridParity r) hq (fun i _ => hw i)
      (separatedGridCoord_sum r) (fun i _ => separatedGridParity_le_sq r i)
  dsimp only at h
  simpa only [separatedGridCoord_sum_sq, Finset.card_univ, Fintype.card_fin] using h

def separatedVarianceFloor (r : Nat) (q K : Real) : Real :=
  q * (r : Real) * ((r : Real) ^ 2 - 1) / 12 +
    q * (r : Real) * (K - q * (r : Real)) * separatedGridParity r / K

theorem separated_rank_distance_of_step (r : Nat) (y : Fin r -> Real) (g : Real)
    (hStep : forall i j : Fin r, j.val = i.val + 1 -> g <= y j - y i) :
    forall i j : Fin r, i.val <= j.val ->
      g * ((j.val : Real) - (i.val : Real)) <= y j - y i := by
  have hNat : forall b : Nat, forall hb : b < r, forall a : Nat, forall ha : a <= b,
      g * ((b : Real) - (a : Real)) <=
        y (Fin.mk b hb) - y (Fin.mk a (lt_of_le_of_lt ha hb)) := by
    intro b
    induction b with
    | zero =>
      intro hb a ha
      have hz : a = 0 := by omega
      subst a
      simp
    | succ b ih =>
      intro hb a ha
      by_cases hab : a = b + 1
      case pos =>
        subst a
        simp
      case neg =>
        have hAB : a <= b := by omega
        have hB : b < r := by omega
        have hPrev := ih hB a hAB
        have hNext := hStep (Fin.mk b hB) (Fin.mk (b + 1) hb) rfl
        simp only [Nat.cast_succ] at *
        linarith only [hPrev, hNext]
  intro i j hij
  exact hNat j.val j.isLt i.val hij

private theorem weighted_variance_scale {Iota : Type*} (S : Finset Iota)
    (w x : Iota -> Real) (g : Real) :
    weightedVarianceNumerator S w (fun i => g * x i) =
      g ^ 2 * weightedVarianceNumerator S w x := by
  have hFirst : Finset.sum S (fun i => w i * (g * x i)) =
      g * Finset.sum S (fun i => w i * x i) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    ring
  have hSecond : Finset.sum S (fun i => w i * (g * x i) ^ 2) =
      g ^ 2 * Finset.sum S (fun i => w i * (x i) ^ 2) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    ring
  dsimp only [weightedVarianceNumerator]
  rw [hFirst, hSecond]
  ring

theorem separated_weighted_variance_lower (r : Nat) (hr : 0 < r)
    (w y : Fin r -> Real) (q g : Real) (hq : 0 < q) (hg : 0 <= g)
    (hw : forall i, q <= w i)
    (hStep : forall i j : Fin r, j.val = i.val + 1 -> g <= y j - y i) :
    let K := Finset.sum Finset.univ w
    let mu := Finset.sum Finset.univ (fun i => w i * y i) / K
    And (0 < K)
      (g ^ 2 * separatedVarianceFloor r q K <=
        Finset.sum Finset.univ (fun i => w i * (y i - mu) ^ 2)) := by
  dsimp only
  let K := Finset.sum Finset.univ w
  let H := Finset.sum Finset.univ (fun i => w i * y i)
  let T := Finset.sum Finset.univ (fun i => w i * (y i) ^ 2)
  let mu := H / K
  have hw0 : forall i, Membership.mem Finset.univ i -> 0 <= w i :=
    fun i _ => le_trans hq.le (hw i)
  let j0 : Fin r := Fin.mk 0 hr
  have hK : 0 < K := lt_of_lt_of_le hq (le_trans (hw j0)
    (Finset.single_le_sum hw0 (Finset.mem_univ j0)))
  have hRank := separated_rank_distance_of_step r y g hStep
  have hPair : forall i j : Fin r, Membership.mem Finset.univ i ->
      Membership.mem Finset.univ j ->
      (g * separatedGridCoord r i - g * separatedGridCoord r j) ^ 2 <= (y i - y j) ^ 2 := by
    intro i j _ _
    by_cases hij : i.val <= j.val
    case pos =>
      have h := hRank i j hij
      have hDiff : 0 <= (j.val : Real) - (i.val : Real) := by
        have hCast : (i.val : Real) <= (j.val : Real) := by exact_mod_cast hij
        exact sub_nonneg.mpr hCast
      have hBase := mul_nonneg hg hDiff
      have hY : 0 <= y j - y i := le_trans hBase h
      have hProd := mul_nonneg (sub_nonneg.mpr h) (add_nonneg hY hBase)
      have hEq : (g * separatedGridCoord r i - g * separatedGridCoord r j) ^ 2 =
          (g * ((j.val : Real) - (i.val : Real))) ^ 2 := by
        dsimp only [separatedGridCoord]
        ring
      rw [hEq]
      nlinarith only [hProd]
    case neg =>
      have hji : j.val <= i.val := le_of_not_ge hij
      have h := hRank j i hji
      have hDiff : 0 <= (i.val : Real) - (j.val : Real) := by
        have hCast : (j.val : Real) <= (i.val : Real) := by exact_mod_cast hji
        exact sub_nonneg.mpr hCast
      have hBase := mul_nonneg hg hDiff
      have hY : 0 <= y i - y j := le_trans hBase h
      have hProd := mul_nonneg (sub_nonneg.mpr h) (add_nonneg hY hBase)
      have hEq : (g * separatedGridCoord r i - g * separatedGridCoord r j) ^ 2 =
          (g * ((i.val : Real) - (j.val : Real))) ^ 2 := by
        dsimp only [separatedGridCoord]
        ring
      rw [hEq]
      nlinarith only [hProd]
  have hComp := weightedVarianceNumerator_le_of_pairwise Finset.univ w
    (fun i => g * separatedGridCoord r i) y hw0 hPair
  rw [weighted_variance_scale] at hComp
  have hGrid := weighted_separatedGrid_lower r w q hq.le hw
  have hScaled := _root_.mul_le_mul_of_nonneg_left hGrid (sq_nonneg g)
  have hFloor : K * (g ^ 2 * separatedVarianceFloor r q K) =
      g ^ 2 * (q * K * ((r : Real) * ((r : Real) ^ 2 - 1) / 12) +
        q * (r : Real) * (K - q * (r : Real)) * separatedGridParity r) := by
    dsimp only [separatedVarianceFloor]
    field_simp [ne_of_gt hK]
  have hExpansion : Finset.sum Finset.univ (fun i => w i * (y i - mu) ^ 2) =
      T - 2 * mu * H + mu ^ 2 * K := by
    calc
      _ = Finset.sum Finset.univ (fun i =>
          w i * (y i) ^ 2 - (2 * mu) * (w i * y i) + mu ^ 2 * w i) := by
        apply Finset.sum_congr rfl
        intro i _
        ring
      _ = _ := by
        rw [Finset.sum_add_distrib, Finset.sum_sub_distrib,
          <- Finset.mul_sum, <- Finset.mul_sum]
  have hMoment : K * Finset.sum Finset.univ (fun i => w i * (y i - mu) ^ 2) =
      weightedVarianceNumerator Finset.univ w y := by
    rw [hExpansion]
    change K * (T - 2 * (H / K) * H + (H / K) ^ 2 * K) = K * T - H ^ 2
    field_simp [ne_of_gt hK]
    ring
  refine And.intro hK ?_
  have hBound : K * (g ^ 2 * separatedVarianceFloor r q K) <=
      K * Finset.sum Finset.univ (fun i => w i * (y i - mu) ^ 2) := by
    rw [hFloor, hMoment]
    exact le_trans hScaled hComp
  by_contra hn
  have hPos := mul_pos hK (sub_pos.mpr (lt_of_not_ge hn))
  nlinarith only [hPos, hBound]

def separatedGridWeights (r : Nat) (q K : Real) (j : Fin r) (i : Fin r) : Real :=
  q + if i = j then K - q * (r : Real) else 0

theorem separatedGridWeights_properties (r : Nat) (q K : Real) (j : Fin r)
    (hK : q * (r : Real) <= K) :
    And (forall i, q <= separatedGridWeights r q K j i)
      (Finset.sum Finset.univ (separatedGridWeights r q K j) = K) := by
  classical
  have hw : forall i, q <= separatedGridWeights r q K j i := by
    intro i
    dsimp only [separatedGridWeights]
    split_ifs <;> linarith only [hK]
  refine And.intro hw ?_
  calc
    _ = (r : Real) * q + (K - q * (r : Real)) := by
      change Finset.sum Finset.univ
        (fun i : Fin r => q + if i = j then K - q * (r : Real) else 0) = _
      rw [Finset.sum_add_distrib]
      simp
    _ = K := by ring

theorem separatedGridWeights_first (r : Nat) (q K : Real) (j : Fin r) :
    Finset.sum Finset.univ
      (fun i => separatedGridWeights r q K j i * separatedGridCoord r i) =
      (K - q * (r : Real)) * separatedGridCoord r j := by
  classical
  simp only [separatedGridWeights, add_mul, ite_mul, zero_mul,
    Finset.sum_add_distrib, <- Finset.mul_sum, separatedGridCoord_sum, mul_zero]
  simp

theorem separatedGridWeights_second (r : Nat) (q K : Real) (j : Fin r) :
    Finset.sum Finset.univ
      (fun i => separatedGridWeights r q K j i * (separatedGridCoord r i) ^ 2) =
      q * ((r : Real) * ((r : Real) ^ 2 - 1) / 12) +
        (K - q * (r : Real)) * (separatedGridCoord r j) ^ 2 := by
  classical
  simp only [separatedGridWeights, add_mul, ite_mul, zero_mul,
    Finset.sum_add_distrib, <- Finset.mul_sum, separatedGridCoord_sum_sq]
  simp

theorem separatedGridWeights_numerator (r : Nat) (q K : Real) (j : Fin r)
    (hK : q * (r : Real) <= K)
    (hj : (separatedGridCoord r j) ^ 2 = separatedGridParity r) :
    weightedVarianceNumerator Finset.univ (separatedGridWeights r q K j)
      (separatedGridCoord r) =
      q * K * ((r : Real) * ((r : Real) ^ 2 - 1) / 12) +
        q * (r : Real) * (K - q * (r : Real)) * separatedGridParity r := by
  unfold weightedVarianceNumerator
  rw [(separatedGridWeights_properties r q K j hK).2,
    separatedGridWeights_first, separatedGridWeights_second]
  calc
    _ = q * K * ((r : Real) * ((r : Real) ^ 2 - 1) / 12) +
        q * (r : Real) * (K - q * (r : Real)) * (separatedGridCoord r j) ^ 2 := by ring
    _ = _ := by rw [hj]

theorem weightedVarianceNumerator_centered {Iota : Type*} (S : Finset Iota)
    (w y : Iota -> Real) (hK : Not (Finset.sum S w = 0)) :
    let K := Finset.sum S w
    let H := Finset.sum S (fun i => w i * y i)
    K * Finset.sum S (fun i => w i * (y i - H / K) ^ 2) =
      weightedVarianceNumerator S w y := by
  dsimp only
  let K := Finset.sum S w
  let H := Finset.sum S (fun i => w i * y i)
  let T := Finset.sum S (fun i => w i * (y i) ^ 2)
  have hExpansion : Finset.sum S (fun i => w i * (y i - H / K) ^ 2) =
      T - 2 * (H / K) * H + (H / K) ^ 2 * K := by
    calc
      _ = Finset.sum S (fun i =>
          w i * (y i) ^ 2 - (2 * (H / K)) * (w i * y i) + (H / K) ^ 2 * w i) := by
        apply Finset.sum_congr rfl
        intro i _
        ring
      _ = _ := by
        rw [Finset.sum_add_distrib, Finset.sum_sub_distrib,
          <- Finset.mul_sum, <- Finset.mul_sum]
  rw [hExpansion]
  change K * (T - 2 * (H / K) * H + (H / K) ^ 2 * K) = K * T - H ^ 2
  have hK0 : Not (K = 0) := hK
  field_simp [hK0]
  ring

theorem separated_weighted_variance_sharp (r : Nat) (hr : 0 < r)
    (q K g : Real) (hq : 0 < q) (hK : q * (r : Real) <= K) (_hg : 0 <= g) :
    exists w y : Fin r -> Real,
      And (forall i, q <= w i)
        (And (Finset.sum Finset.univ w = K)
          (And (forall i j : Fin r, j.val = i.val + 1 -> y j - y i = g)
            (Finset.sum Finset.univ
              (fun i => w i * (y i -
                Finset.sum Finset.univ (fun j => w j * y j) / K) ^ 2) =
                  g ^ 2 * separatedVarianceFloor r q K))) := by
  classical
  choose j hj using separatedGridParity_attained r hr
  let w := separatedGridWeights r q K j
  let y := fun i => g * separatedGridCoord r i
  have hProps := separatedGridWeights_properties r q K j hK
  have hrR : 0 < (r : Real) := by exact_mod_cast hr
  have hKpos : 0 < K := lt_of_lt_of_le (mul_pos hq hrR) hK
  refine Exists.intro w (Exists.intro y (And.intro hProps.1 (And.intro hProps.2
    (And.intro ?_ ?_))))
  case refine_1 =>
    intro i j hij
    have hCast : (j.val : Real) = (i.val : Real) + 1 := by exact_mod_cast hij
    dsimp only [y, separatedGridCoord]
    rw [hCast]
    ring
  case refine_2 =>
    have hCenter := weightedVarianceNumerator_centered Finset.univ w y
      (by rw [hProps.2]; exact ne_of_gt hKpos)
    rw [hProps.2] at hCenter
    have hNum := separatedGridWeights_numerator r q K j hK hj
    have hScale := weighted_variance_scale Finset.univ w (separatedGridCoord r) g
    change weightedVarianceNumerator Finset.univ w y =
      g ^ 2 * weightedVarianceNumerator Finset.univ w (separatedGridCoord r) at hScale
    rw [hScale, hNum] at hCenter
    have hFloor : K * (g ^ 2 * separatedVarianceFloor r q K) =
        g ^ 2 * (q * K * ((r : Real) * ((r : Real) ^ 2 - 1) / 12) +
          q * (r : Real) * (K - q * (r : Real)) * separatedGridParity r) := by
      dsimp only [separatedVarianceFloor]
      field_simp [ne_of_gt hKpos]
    have hEq := hCenter.trans hFloor.symm
    have hInv : (1 / K) * K = 1 := by field_simp [ne_of_gt hKpos]
    have hCancel := congrArg (fun z : Real => (1 / K) * z) hEq
    simpa only [<- mul_assoc, hInv, one_mul] using hCancel

end Finset

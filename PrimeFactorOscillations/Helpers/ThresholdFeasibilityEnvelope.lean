/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import PrimeFactorOscillations.Helpers.ThresholdEvenSharpness

/-! # Exact threshold feasibility envelope with all cross terms retained -/

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 5000000

noncomputable section
namespace PrimeFactorOscillations

def thresholdExcess (d y : Real) : Real :=
  (y - d) * momentRoundIndicator d y

def thresholdLow (d y : Real) : Real :=
  y * (1 - momentRoundIndicator d y)

theorem thresholdExcess_nonneg (d y : Real) : 0 <= thresholdExcess d y := by
  classical
  by_cases h : d <= y
  case pos => simpa [thresholdExcess, momentRoundIndicator, h] using sub_nonneg.mpr h
  case neg => simp [thresholdExcess, momentRoundIndicator, h]

theorem thresholdLow_nonneg (d y : Real) (hy : 0 <= y) : 0 <= thresholdLow d y := by
  classical
  by_cases h : d <= y
  case pos => simp [thresholdLow, momentRoundIndicator, h]
  case neg => simpa [thresholdLow, momentRoundIndicator, h] using hy

theorem thresholdFeasibility_point (d y : Real) :
    And (y = d * momentRoundIndicator d y + thresholdExcess d y + thresholdLow d y)
      (y ^ 2 = d ^ 2 * momentRoundIndicator d y + 2 * d * thresholdExcess d y +
        (thresholdExcess d y) ^ 2 + y ^ 2 * (1 - momentRoundIndicator d y)) := by
  classical
  by_cases h : d <= y <;>
    simp [thresholdExcess, thresholdLow, momentRoundIndicator, h] <;> ring

theorem thresholdLow_square (d y : Real) (hy : 0 <= y) :
    y ^ 2 * (1 - momentRoundIndicator d y) <= d * thresholdLow d y := by
  classical
  by_cases h : d <= y
  case pos => simp [thresholdLow, momentRoundIndicator, h]
  case neg =>
    have hm := mul_nonneg hy (sub_nonneg.mpr (le_of_not_ge h))
    simp only [thresholdLow, momentRoundIndicator, if_neg h, sub_zero, mul_one]
    nlinarith only [hm]

theorem finiteWeighted_atom_square {Iota : Type*} (S : Finset Iota)
    (a x : Iota -> Real)
    (ha : forall i, Membership.mem S i -> 0 <= a i)
    (hx : forall i, Membership.mem S i -> 0 <= x i)
    (hAtom : forall i, Membership.mem S i -> Or (a i = 0) (2 <= a i)) :
    2 * Finset.sum S (fun i => a i * (x i) ^ 2) <=
      (Finset.sum S (fun i => a i * x i)) ^ 2 := by
  classical
  calc
    _ = Finset.sum S (fun i => 2 * (a i * (x i) ^ 2)) := Finset.mul_sum ..
    _ <= Finset.sum S (fun i => (a i * x i) ^ 2) := by
      apply Finset.sum_le_sum
      intro i hi
      rcases hAtom i hi with hZero | hTwo
      case inl => simp [hZero]
      case inr =>
        have hp := mul_nonneg (mul_nonneg (ha i hi) (sub_nonneg.mpr hTwo))
          (sq_nonneg (x i))
        nlinarith only [hp]
    _ <= _ := Finset.sum_sq_le_sq_sum_of_nonneg
      (fun i hi => mul_nonneg (ha i hi) (hx i hi))

theorem finiteWeighted_paired_square {Iota : Type*} (S : Finset Iota)
    (a x : Iota -> Real)
    (ha : forall i, Membership.mem S i -> 0 <= a i)
    (hx : forall i, Membership.mem S i -> 0 <= x i)
    (hUnit : forall i, Membership.mem S i -> 0 < a i -> 1 <= a i)
    (hPair : forall i, Membership.mem S i -> 0 < a i -> 0 < x i ->
      exists j, And (Membership.mem S j) (And (Not (i = j))
        (And (1 <= a j) (x j = x i)))) :
    2 * Finset.sum S (fun i => a i * (x i) ^ 2) <=
      (Finset.sum S (fun i => a i * x i)) ^ 2 := by
  classical
  let T := Finset.sum S (fun i => a i * x i)
  have hT : 0 <= T := Finset.sum_nonneg (fun i hi => mul_nonneg (ha i hi) (hx i hi))
  have hEach : forall i, Membership.mem S i -> 2 * (a i * (x i) ^ 2) <= T * (a i * x i) := by
    intro i hi
    by_cases hp : 0 < a i
    case neg =>
      have hz : a i = 0 := le_antisymm (le_of_not_gt hp) (ha i hi)
      simp [hz]
    case pos =>
      by_cases hxp : 0 < x i
      case neg =>
        have hz : x i = 0 := le_antisymm (le_of_not_gt hxp) (hx i hi)
        simp [hz]
      case pos =>
        choose j hj using hPair i hi hp hxp
        have hSub : forall q, Membership.mem ({i, j} : Finset Iota) q -> Membership.mem S q := by
          intro q hq
          simp only [Finset.mem_insert, Finset.mem_singleton] at hq
          rcases hq with hqi | hqj
          case inl => simpa only [hqi] using hi
          case inr => simpa only [hqj] using hj.1
        have hTwo := Finset.sum_le_sum_of_subset_of_nonneg hSub
          (fun q hq _ => mul_nonneg (ha q hq) (hx q hq))
        have hSum : a i * x i + a j * x j <= T := by
          simpa only [Finset.sum_pair hj.2.1] using hTwo
        rw [hj.2.2.2] at hSum
        have hAi := mul_nonneg (sub_nonneg.mpr (hUnit i hi hp)) (hx i hi)
        have hAj := mul_nonneg (sub_nonneg.mpr hj.2.2.1) (hx i hi)
        have hTX : 2 * x i <= T := by linarith only [hSum, hAi, hAj]
        have hh := mul_nonneg (sub_nonneg.mpr hTX) (mul_nonneg (ha i hi) (hx i hi))
        nlinarith only [hh]
  have hSum := Finset.sum_le_sum hEach
  simpa only [<- Finset.mul_sum, T, sq] using hSum

theorem finiteWeighted_threshold_ledger {Iota : Type*} (S : Finset Iota)
    (a y : Iota -> Real) (d : Real) :
    And (Finset.sum S (fun i => a i * y i) =
      d * thresholdSelectedMass d S a y +
      Finset.sum S (fun i => a i * thresholdExcess d (y i)) +
      Finset.sum S (fun i => a i * thresholdLow d (y i)))
    (Finset.sum S (fun i => a i * (y i) ^ 2) =
      d ^ 2 * thresholdSelectedMass d S a y +
      2 * d * Finset.sum S (fun i => a i * thresholdExcess d (y i)) +
      Finset.sum S (fun i => a i * (thresholdExcess d (y i)) ^ 2) +
      Finset.sum S (fun i => a i * ((y i) ^ 2 * (1 - momentRoundIndicator d (y i))))) := by
  constructor
  all_goals
    unfold thresholdSelectedMass
    simp only [Finset.mul_sum, <- Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
  case left =>
    have hh := congrArg (fun q : Real => a i * q) (thresholdFeasibility_point d (y i)).1
    nlinarith only [hh]
  case right =>
    have hh := congrArg (fun q : Real => a i * q) (thresholdFeasibility_point d (y i)).2
    nlinarith only [hh]

theorem finiteWeighted_threshold_quadratic {Iota : Type*} (S : Finset Iota)
    (a y : Iota -> Real) (d : Real) (hd : 0 <= d)
    (ha : forall i, Membership.mem S i -> 0 <= a i)
    (hy : forall i, Membership.mem S i -> 0 <= y i)
    (hMoment : Finset.sum S (fun i => a i * (y i) ^ 2) = Finset.sum S (fun i => a i * y i))
    (hSquare : 2 * Finset.sum S (fun i => a i * (thresholdExcess d (y i)) ^ 2) <=
      (Finset.sum S (fun i => a i * thresholdExcess d (y i))) ^ 2) :
    (Finset.sum S (fun i => a i * y i) - d * thresholdSelectedMass d S a y) ^ 2 +
      (4 * d - 2) * Finset.sum S (fun i => a i * y i) -
      2 * d ^ 2 * thresholdSelectedMass d S a y >= 0 := by
  let M := Finset.sum S (fun i => a i * y i)
  let K := thresholdSelectedMass d S a y
  let X := Finset.sum S (fun i => a i * thresholdExcess d (y i))
  let Y := Finset.sum S (fun i => a i * thresholdLow d (y i))
  have hX : 0 <= X := Finset.sum_nonneg
    (fun i hi => mul_nonneg (ha i hi) (thresholdExcess_nonneg d (y i)))
  have hY : 0 <= Y := Finset.sum_nonneg
    (fun i hi => mul_nonneg (ha i hi) (thresholdLow_nonneg d (y i) (hy i hi)))
  have hLedger := finiteWeighted_threshold_ledger S a y d
  have hT : M - d * K = X + Y := by linarith only [hLedger.1]
  have hEachLow : forall i, Membership.mem S i ->
      a i * ((y i) ^ 2 * (1 - momentRoundIndicator d (y i))) <=
        d * (a i * thresholdLow d (y i)) := by
    intro i hi
    calc
      _ <= a i * (d * thresholdLow d (y i)) :=
        mul_le_mul_of_nonneg_left (thresholdLow_square d (y i) (hy i hi)) (ha i hi)
      _ = _ := by ring
  have hLow := Finset.sum_le_sum hEachLow
  rw [<- Finset.mul_sum] at hLow
  have hEnvelope : 2 * M <= 2 * d ^ 2 * K + 4 * d * X + X ^ 2 + 2 * d * Y := by
    linarith only [hLedger.2, hMoment, hLow, hSquare]
  have hExpanded : 2 * M <= 2 * d ^ 2 * K + 4 * d * (X + Y) + (X + Y) ^ 2 := by
    nlinarith only [hEnvelope, mul_nonneg hd hY, mul_nonneg hX hY, sq_nonneg Y]
  rw [<- hT] at hExpanded
  change (M - d * K) ^ 2 + (4 * d - 2) * M - 2 * d ^ 2 * K >= 0
  nlinarith only [hExpanded]

theorem thresholdEvenAdmissible_quadratic {n : Nat} (d M K : Real)
    (a : Fin n -> Nat) (y : Fin n -> Real) (hd : 0 <= d)
    (hAd : thresholdEvenAdmissible d M K a y) :
    (M - d * K) ^ 2 + (4 * d - 2) * M - 2 * d ^ 2 * K >= 0 := by
  have hAtom : forall i : Fin n, Membership.mem Finset.univ i ->
      Or (2 * (a i : Real) = 0) (2 <= 2 * (a i : Real)) := by
    intro i _
    by_cases hz : a i = 0
    case pos => exact Or.inl (by simp [hz])
    case neg =>
      have hn : 1 <= a i := Nat.one_le_iff_ne_zero.mpr hz
      have hr : (1 : Real) <= (a i : Real) := by exact_mod_cast hn
      exact Or.inr (by linarith only [hr])
  have ha := fun (i : Fin n) (_ : Membership.mem Finset.univ i) =>
    mul_nonneg (show (0 : Real) <= 2 by norm_num) (Nat.cast_nonneg (a i))
  have hSquare := finiteWeighted_atom_square Finset.univ (fun i => 2 * (a i : Real))
    (fun i => thresholdExcess d (y i)) ha (fun i _ => thresholdExcess_nonneg d (y i)) hAtom
  have h := finiteWeighted_threshold_quadratic Finset.univ (fun i => 2 * (a i : Real)) y d hd
    ha (fun i _ => hAd.1 i) (by rw [hAd.2.2.1, hAd.2.1]) hSquare
  simpa only [hAd.2.1, hAd.2.2.2] using h

end PrimeFactorOscillations

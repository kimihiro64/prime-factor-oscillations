/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Tactic.FieldSimp
import PrimeFactorOscillations.Proof.PrimeClassDeletion.CapacitySelection
import PrimeFactorOscillations.Proof.PrimeClassDeletion.GreedyRegulator

/-!
# Exact termination criterion for a positive-weight greedy clock

The original rejection test is retained. Uniformly positive rejection
weights turn bounded excess into eventual termination, without a norm
estimate, a phase assumption, or an arithmetic distribution hypothesis.
-/

set_option autoImplicit false
set_option Elab.async false

namespace PrimeFactorOscillations.PrimeClassDeletion

noncomputable def clockRejected (e w : Nat -> Real) (n : Nat) : Prop :=
  Not (e n <= clockDeletedMass e w n)

theorem clockDeletedMass_eq_rejectedCost (e w : Nat -> Real) (n : Nat) :
    clockDeletedMass e w n = selectionCost (clockRejected e w) w n := by
  classical
  induction n with
  | zero => rfl
  | succ n ih =>
      by_cases h : e n <= clockDeletedMass e w n
      all_goals
        simp only [clockDeletedMass, deletionStep, selectionCost]
        simp only [clockRejected, h, not_true_eq_false, not_false_eq_true,
          ite_true, ite_false]
        linarith only [ih]

theorem selectionCount_monotone (a : Nat -> Prop) : Monotone (selectionCount a) := by
  classical
  apply monotone_nat_of_le_succ
  intro n
  simp only [selectionCount]
  split <;> omega

theorem selectionCost_ge_minWeight_count (a : Nat -> Prop) (w : Nat -> Real)
    (c : Real) (hw : forall n, c <= w n) (n : Nat) :
    (selectionCount a n : Real) * c <= selectionCost a w n := by
  classical
  induction n with
  | zero => simp only [selectionCount, selectionCost, Nat.cast_zero, zero_mul, le_refl]
  | succ n ih =>
      by_cases h : a n
      case pos =>
        simp only [selectionCount, selectionCost, ite_eq_left h, Nat.cast_add, Nat.cast_one]
        nlinarith only [ih, hw n]
      case neg =>
        simpa only [selectionCount, selectionCost, ite_eq_right h,
          Nat.add_zero, add_zero] using ih

theorem clockRejected_count_le_prefix_bound
    (e w : Nat -> Real) (c C : Real) (hc : 0 <= c) (hC : 0 <= C)
    (hw : forall n, c <= w n) (n : Nat)
    (he : forall i, i < n -> e i <= C) :
    (selectionCount (clockRejected e w) n : Real) * c <= C + c := by
  classical
  revert he
  induction n with
  | zero =>
      intro _
      simpa only [selectionCount, Nat.cast_zero, zero_mul] using add_nonneg hC hc
  | succ n ih =>
      intro he
      have hBefore := ih (fun i hi => he i (hi.trans (Nat.lt_succ_self n)))
      by_cases hReject : clockRejected e w n
      case pos =>
        have hLower := selectionCost_ge_minWeight_count (clockRejected e w) w c hw n
        rw [<- clockDeletedMass_eq_rejectedCost] at hLower
        have hTest : clockDeletedMass e w n < e n := lt_of_not_ge hReject
        have hUpper := he n (Nat.lt_succ_self n)
        simp only [selectionCount, ite_eq_left hReject, Nat.cast_add, Nat.cast_one]
        nlinarith only [hLower, hTest, hUpper]
      case neg =>
        simpa only [selectionCount, ite_eq_right hReject, Nat.add_zero] using hBefore

theorem selection_eventually_none_of_bounded_count
    (a : Nat -> Prop) (K : Nat) (hBound : forall n, selectionCount a n <= K) :
    Exists fun N : Nat => forall n, N <= n -> Not (a n) := by
  classical
  induction K with
  | zero =>
      refine Exists.intro 0 ?_
      intro n _ ha
      have h := hBound (n + 1)
      simp only [selectionCount, ite_eq_left ha] at h
      omega
  | succ K ih =>
      by_cases hHit : Exists fun N : Nat => selectionCount a N = K + 1
      case pos =>
        choose N hN using hHit
        refine Exists.intro N ?_
        intro n hn ha
        have hMono := selectionCount_monotone a hn
        have hNow := hBound n
        have hEqual : selectionCount a n = K + 1 := by omega
        have hNext := hBound (n + 1)
        simp only [selectionCount, ite_eq_left ha, hEqual] at hNext
        omega
      case neg =>
        apply ih
        intro n
        have hNow := hBound n
        have hUnequal : Not (selectionCount a n = K + 1) := by
          intro h
          exact hHit (Exists.intro n h)
        omega

theorem clockRecord_monotone (e : Nat -> Real) : Monotone (clockRecord e) := by
  apply monotone_nat_of_le_succ
  intro n
  exact le_max_left _ _

theorem clockDeletedMass_constant_after_no_rejections
    (e w : Nat -> Real) (N : Nat)
    (hNo : forall n, N <= n -> Not (clockRejected e w n))
    (n : Nat) (hn : N <= n) :
    clockDeletedMass e w n = clockDeletedMass e w N := by
  classical
  have hOffset : forall k : Nat,
      clockDeletedMass e w (N + k) = clockDeletedMass e w N := by
    intro k
    induction k with
    | zero => simp only [Nat.add_zero]
    | succ k ih =>
        have hAllowed : e (N + k) <= clockDeletedMass e w (N + k) := by
          by_contra h
          exact hNo (N + k) (Nat.le_add_right N k) h
        rw [Nat.add_succ, clockDeletedMass, deletionStep, ite_eq_left hAllowed]
        exact ih
  have hSplit : N + (n - N) = n := Nat.add_sub_of_le hn
  rw [<- hSplit]
  exact hOffset (n - N)

theorem greedyClock_eventually_no_rejections_iff_bounded_excess
    (e w : Nat -> Real) (c : Real) (hc : 0 < c)
    (hw : forall n, c <= w n) :
    (Exists fun N : Nat => forall n, N <= n -> Not (clockRejected e w n)) <->
      (Exists fun C : Real => And (0 <= C) (forall n, e n <= C)) := by
  classical
  constructor
  case mp =>
    intro hFinite
    choose N hNo using hFinite
    let C := max (clockRecord e N) (clockDeletedMass e w N)
    refine Exists.intro C (And.intro
      ((clockRecord_nonneg e N).trans (le_max_left _ _)) ?_)
    intro n
    by_cases hn : n < N
    case pos =>
      have hLocal := (clockRecord_contains e n).trans
        (clockRecord_monotone e (Nat.succ_le_of_lt hn))
      exact hLocal.trans (le_max_left _ _)
    case neg =>
      have hNn : N <= n := le_of_not_gt hn
      have hAllowed : e n <= clockDeletedMass e w n := by
        by_contra h
        exact hNo n hNn h
      rw [clockDeletedMass_constant_after_no_rejections e w N hNo n hNn] at hAllowed
      exact hAllowed.trans (le_max_right _ _)
  case mpr =>
    intro hBound
    choose C hC he using hBound
    choose K hK using exists_nat_gt ((C + c) / c)
    have hKScaled := mul_lt_mul_of_pos_right hK hc
    have hCancel : ((C + c) / c) * c = C + c := by field_simp [hc.ne']
    rw [hCancel] at hKScaled
    have hCount : forall n, selectionCount (clockRejected e w) n <= K := by
      intro n
      have hReal := clockRejected_count_le_prefix_bound e w c C hc.le hC hw n
        (fun i _ => he i)
      by_contra hFail
      have hNat : K <= selectionCount (clockRejected e w) n :=
        (lt_of_not_ge hFail).le
      have hCast : (K : Real) <= (selectionCount (clockRejected e w) n : Real) := by
        exact_mod_cast hNat
      have hScaled := mul_le_mul_of_nonneg_right hCast hc.le
      linarith only [hReal, hScaled, hKScaled]
    exact selection_eventually_none_of_bounded_count (clockRejected e w) K hCount

end PrimeFactorOscillations.PrimeClassDeletion

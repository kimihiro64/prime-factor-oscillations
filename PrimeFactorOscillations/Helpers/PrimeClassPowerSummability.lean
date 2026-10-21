/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.PrimeClassDecoderComplete

/-!
# Convergence from exact finite prime-class shell budgets

Every finite subsum is partitioned by the actual integer logarithm of
its prime labels. A summable shell budget therefore bounds all finite
subseries. No density or infinitude assumption on the class is used.
-/

set_option autoImplicit false
set_option Elab.async false

namespace PrimeFactorOscillations.PrimeClassSampling

theorem classPowerWeight_summable_mono
    (P : Set Nat) (s t : Real) (hst : s <= t)
    (hsum : Summable (classPowerWeight P s)) :
    Summable (classPowerWeight P t) := by
  apply Summable.of_nonneg_of_le (classPowerWeight_nonneg P t) _ hsum
  intro p
  classical
  unfold classPowerWeight
  split_ifs with hp
  case pos =>
    exact Real.rpow_le_rpow_of_exponent_le
      (by exact_mod_cast (show 1 <= p from hp.1.one_lt.le)) (by linarith)
  case neg => exact le_refl 0

theorem classPowerWeight_summable_of_shell_budget
    (P : Set Nat) (B : Nat) (hB : 1 < B) (s : Real) (hs : 0 <= s)
    (g : Nat -> Real) (hg0 : forall j, 0 <= g j) (hg : Summable g)
    (hbudget : forall j : Nat,
      ((primeClassPrefix P (B ^ (j + 1))).card : Real) *
        ((B ^ j : Nat) : Real) ^ (-s) <= g j) :
    Summable (classPowerWeight P s) := by
  classical
  apply summable_of_sum_le (classPowerWeight_nonneg P s)
    (c := tsum g)
  intro u
  let v := u.filter (fun p => And (Nat.Prime p) (Membership.mem P p))
  let J := v.image (Nat.log B)
  have heq : u.sum (classPowerWeight P s) =
      v.sum (fun p => (p : Real) ^ (-s)) := by
    simp only [v, Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro p _
    rfl
  rw [heq]
  rw [<- Finset.sum_fiberwise_of_maps_to
    (s := v) (t := J) (g := Nat.log B)
    (fun p hp => Finset.mem_image.mpr (Exists.intro p (And.intro hp rfl)))
    (fun p => (p : Real) ^ (-s))]
  apply le_trans (Finset.sum_le_sum (fun j _ => ?_))
    (Summable.sum_le_tsum J (fun j _ => hg0 j) hg)
  let w := v.filter (fun p => Nat.log B p = j)
  have hsub : forall p, Membership.mem w p ->
      Membership.mem (primeClassPrefix P (B ^ (j + 1))) p := by
    intro p hp
    have hpw := Finset.mem_filter.mp hp
    have hpv := Finset.mem_filter.mp hpw.1
    apply Finset.mem_filter.mpr
    apply And.intro _ hpv.2
    apply Finset.mem_Icc.mpr
    apply And.intro hpv.2.1.two_le
    have hpbound := Nat.lt_pow_succ_log_self hB p
    rw [hpw.2] at hpbound
    exact Nat.le_of_lt hpbound
  have hterm : forall p, Membership.mem w p ->
      (p : Real) ^ (-s) <= ((B ^ j : Nat) : Real) ^ (-s) := by
    intro p hp
    have hpw := Finset.mem_filter.mp hp
    have hpv := Finset.mem_filter.mp hpw.1
    have hpbound := Nat.pow_log_le_self B hpv.2.1.ne_zero
    rw [hpw.2] at hpbound
    exact Real.rpow_le_rpow_of_nonpos
      (by exact_mod_cast (Nat.pow_pos (n := j) (by omega : 0 < B)))
      (by exact_mod_cast hpbound) (by linarith)
  calc
    w.sum (fun p => (p : Real) ^ (-s)) <=
        (w.card : Real) * ((B ^ j : Nat) : Real) ^ (-s) := by
      simpa only [Finset.sum_const, nsmul_eq_mul] using
        Finset.sum_le_sum (fun p hp => hterm p hp)
    _ <= ((primeClassPrefix P (B ^ (j + 1))).card : Real) *
        ((B ^ j : Nat) : Real) ^ (-s) := by
      exact mul_le_mul_of_nonneg_right (by exact_mod_cast Finset.card_le_card hsub)
        (Real.rpow_nonneg (Nat.cast_nonneg _) _)
    _ <= g j := hbudget j

theorem primeClassPrefix_card_mono
    (P : Set Nat) (X Y : Nat) (hXY : X <= Y) :
    (primeClassPrefix P X).card <= (primeClassPrefix P Y).card := by
  classical
  apply Finset.card_le_card
  intro p hp
  have hd := Finset.mem_filter.mp hp
  have hi := Finset.mem_Icc.mp hd.1
  exact Finset.mem_filter.mpr (And.intro
    (Finset.mem_Icc.mpr (And.intro hi.1 (hi.2.trans hXY))) hd.2)

theorem classPowerWeight_summable_of_geometric_prefix_bound
    (P : Set Nat) (B : Nat) (hB : 1 < B) (s A C : Real)
    (hs : 0 <= s) (hA : 0 <= A) (hC : 0 <= C)
    (hratio : A * (B : Real) ^ (-s) < 1)
    (hcount : forall j : Nat,
      ((primeClassPrefix P (B ^ (j + 1))).card : Real) <= C * A ^ j) :
    Summable (classPowerWeight P s) := by
  let r : Real := A * (B : Real) ^ (-s)
  have hr0 : 0 <= r := mul_nonneg hA (Real.rpow_nonneg (Nat.cast_nonneg B) _)
  have hr1 : norm r < 1 := by simpa only [Real.norm_eq_abs, abs_of_nonneg hr0] using hratio
  have hg : Summable (fun j : Nat => C * r ^ j) :=
    (summable_geometric_iff_norm_lt_one.mpr hr1).mul_left C
  apply classPowerWeight_summable_of_shell_budget P B hB s hs
    (fun j => C * r ^ j) (fun j => mul_nonneg hC (pow_nonneg hr0 j)) hg
  intro j
  calc
    ((primeClassPrefix P (B ^ (j + 1))).card : Real) *
        ((B ^ j : Nat) : Real) ^ (-s) <=
        (C * A ^ j) * ((B ^ j : Nat) : Real) ^ (-s) :=
      mul_le_mul_of_nonneg_right (hcount j) (Real.rpow_nonneg (Nat.cast_nonneg _) _)
    _ = C * r ^ j := by
      rw [Nat.cast_pow, <- Real.rpow_pow_comm (Nat.cast_nonneg B)]
      dsimp [r]
      rw [mul_pow]
      ring

theorem classPowerWeight_summable_of_eventual_geometric_prefix_bound
    (P : Set Nat) (B : Nat) (hB : 1 < B) (s A C : Real)
    (hs : 0 <= s) (hA : 1 <= A) (hC : 0 <= C)
    (hratio : A * (B : Real) ^ (-s) < 1)
    (hcount : Filter.Eventually (fun j : Nat =>
      ((primeClassPrefix P (B ^ (j + 1))).card : Real) <= C * A ^ j) Filter.atTop) :
    Summable (classPowerWeight P s) := by
  choose j0 hj0 using Filter.eventually_atTop.mp hcount
  let K : Real := max C ((primeClassPrefix P (B ^ (j0 + 1))).card : Real)
  have hK : 0 <= K := hC.trans (le_max_left _ _)
  apply classPowerWeight_summable_of_geometric_prefix_bound P B hB s A K hs
    (by linarith) hK hratio
  intro j
  by_cases hj : j0 <= j
  case pos =>
    exact (hj0 j hj).trans
      (mul_le_mul_of_nonneg_right (le_max_left _ _) (pow_nonneg (by linarith) j))
  case neg =>
    have hjle : j + 1 <= j0 + 1 := by omega
    have hpow : B ^ (j + 1) <= B ^ (j0 + 1) := Nat.pow_le_pow_right (by omega) hjle
    have hmono : ((primeClassPrefix P (B ^ (j + 1))).card : Real) <=
        ((primeClassPrefix P (B ^ (j0 + 1))).card : Real) := by
      exact_mod_cast primeClassPrefix_card_mono P _ _ hpow
    have hcard : ((primeClassPrefix P (B ^ (j + 1))).card : Real) <= K :=
      hmono.trans (le_max_right _ _)
    have hAall : forall k : Nat, 1 <= A ^ k := by
      intro k
      induction k with
      | zero => simp
      | succ k ih =>
        rw [pow_succ]
        exact one_le_mul_of_one_le_of_one_le ih hA
    exact hcard.trans (le_mul_of_one_le_right hK (hAall j))

end PrimeFactorOscillations.PrimeClassSampling

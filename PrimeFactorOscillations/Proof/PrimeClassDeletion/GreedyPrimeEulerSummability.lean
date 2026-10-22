/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import Mathlib.Analysis.PSeries
import PrimeFactorOscillations.Helpers.PrimeClassPowerSummability
import PrimeFactorOscillations.Proof.PrimeClassDeletion.CappedPrimeMissingCost
import PrimeFactorOscillations.Proof.PrimeClassDeletion.GreedyPrimePolylogMass
import PrimeFactorOscillations.Proof.PrimeClassDeletion.GreedyPrimeRHUpper

/-!
# Unconditional convergence of the actual greedy missing Euler cost

Use all dyadic shells of the proved unconditional deleted logarithmic mass.
The reciprocal-prime shell budget is a sum of an inverse square and two
geometrically decaying terms. No competitor summability is assumed.
-/

set_option autoImplicit false
set_option Elab.async false

open Filter
open PrimeFactorOscillations.PrimeClassSampling

namespace PrimeFactorOscillations.PrimeClassDeletion

theorem greedyDeletedPrimeClass_reciprocal_summable :
    Summable (classPowerWeight greedyDeletedPrimeClass 1) := by
  choose A hA C hC hmass using
    greedyDeletedPrimeClass_eventually_theta_polylog_bound
  choose N hN using Filter.eventually_atTop.mp hmass
  let L : Real := Real.log 2
  let r : Real := 1 / 2
  let b : Nat -> Real := fun j =>
    ((primeClassPrefix greedyDeletedPrimeClass (2 ^ (j + 1))).card : Real) /
      (2 : Real) ^ j
  let g : Nat -> Real := fun j =>
    A / L * r ^ j + (2 * C / L ^ 3) * (1 / ((j + 1 : Nat) : Real) ^ 2) +
      ((j + 1 : Nat) : Real) * r ^ j
  have hL : 0 < L := Real.log_pos (by norm_num)
  have hr : norm r < 1 := by norm_num [r]
  have hgeo : Summable (fun j : Nat => r ^ j) :=
    summable_geometric_iff_norm_lt_one.mpr hr
  have hlin : Summable (fun j : Nat => (j : Real) * r ^ j) := by
    simpa only [pow_one] using summable_pow_mul_geometric_of_norm_lt_one 1 hr
  have hlinNext : Summable (fun j : Nat => ((j + 1 : Nat) : Real) * r ^ j) := by
    convert hlin.add hgeo using 1
    funext j
    simp only [Nat.cast_add, Nat.cast_one]
    ring
  have hInvSq : Summable (fun j : Nat => 1 / (j : Real) ^ 2) :=
    Real.summable_one_div_nat_pow.mpr (by norm_num)
  have hInvSqNext : Summable (fun j : Nat => 1 / ((j + 1 : Nat) : Real) ^ 2) :=
    (summable_nat_add_iff 1).mpr hInvSq
  have hg : Summable g :=
    ((hgeo.mul_left (A / L)).add (hInvSqNext.mul_left (2 * C / L ^ 3))).add hlinNext
  have hb0 (j : Nat) : 0 <= b j := by dsimp only [b]; positivity
  have hb : Summable b := by
    apply Summable.of_norm_bounded_eventually_nat hg
    filter_upwards [eventually_ge_atTop N] with j hj
    rw [Real.norm_eq_abs, abs_of_nonneg (hb0 j)]
    let X : Nat := 2 ^ (j + 1)
    let q : Real := (2 : Real) ^ j
    let k : Real := ((j + 1 : Nat) : Real)
    have hq : 0 < q := by dsimp only [q]; positivity
    have hk : 0 < k := by dsimp only [k]; positivity
    have hNX : N <= X := by
      have hpow := Nat.lt_two_pow_self (n := j + 1)
      dsimp only [X]
      omega
    have hcast : (X : Real) = 2 * q := by
      simp only [X, q, pow_succ, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat]
      ring
    have hlog : Real.log (X : Real) = k * L := by
      simp only [X, Nat.cast_pow, Nat.cast_ofNat, Real.log_pow, k, L]
    have hMass := (primeClassPrefix_count_mul_log_two_le_theta
      greedyDeletedPrimeClass X).trans (hN X hNX)
    rw [hlog, hcast] at hMass
    change ((primeClassPrefix greedyDeletedPrimeClass X).card : Real) * L <=
      A + C * (2 * q / (k * L) ^ 2) + k * L at hMass
    have hInv : r ^ j = 1 / q := by simp only [r, div_pow, one_pow, q]
    calc
      b j = (((primeClassPrefix greedyDeletedPrimeClass X).card : Real) * L) *
          (1 / (L * q)) := by
        dsimp only [b, X, q]
        field_simp [hL.ne']
      _ <= (A + C * (2 * q / (k * L) ^ 2) + k * L) *
          (1 / (L * q)) :=
        mul_le_mul_of_nonneg_right hMass (by positivity)
      _ = g j := by
        dsimp only [g]
        rw [hInv]
        change (A + C * (2 * q / (k * L) ^ 2) + k * L) *
          (1 / (L * q)) =
            A / L * (1 / q) + (2 * C / L ^ 3) * (1 / k ^ 2) + k * (1 / q)
        field_simp [hL.ne', hq.ne', hk.ne']
  apply classPowerWeight_summable_of_shell_budget greedyDeletedPrimeClass 2
    (by norm_num) 1 (by norm_num) b hb0 hb
  intro j
  simp only [b, Nat.cast_pow, Nat.cast_ofNat, Real.rpow_neg_one, div_eq_mul_inv]
  exact le_refl _

theorem primeEulerLogWeight_le_two_div (p : Nat) (hp : Nat.Prime p) :
    primeEulerLogWeight p <= 2 / (p : Real) := by
  have hpTwo : (2 : Real) <= p := Nat.cast_le.mpr hp.two_le
  have hpPos : (0 : Real) < p := by linarith only [hpTwo]
  have hpOne : 0 < (p : Real) - 1 := by linarith only [hpTwo]
  have hsmall : (1 : Real) / p < 1 := (div_lt_one hpPos).mpr (by linarith only [hpTwo])
  have hbase : 0 < 1 - 1 / (p : Real) := sub_pos.mpr hsmall
  have hlog := Real.log_le_sub_one_of_pos (inv_pos.mpr hbase)
  rw [Real.log_inv] at hlog
  calc
    primeEulerLogWeight p <= 1 / (1 - 1 / (p : Real)) - 1 := by
      simpa only [primeEulerLogWeight, one_div] using hlog
    _ = 1 / ((p : Real) - 1) := by
      field_simp [hpPos.ne', hpOne.ne', hbase.ne']
      <;> ring
    _ <= 1 / ((p : Real) / 2) :=
      one_div_le_one_div_of_le (by positivity) (by linarith only [hpTwo])
    _ = 2 / (p : Real) := by field_simp

theorem greedyPrimeClass_missing_logEulerCost_summable :
    Summable (primeClassMissingWeight greedyPrimeClass primeEulerLogWeight) := by
  classical
  apply Summable.of_nonneg_of_le
    (primeClassMissingWeight_nonneg greedyPrimeClass primeEulerLogWeight
      primeEulerLogWeight_nonneg) _
    (greedyDeletedPrimeClass_reciprocal_summable.mul_left 2)
  intro p
  by_cases hp : Nat.Prime p
  case neg =>
    simp only [primeClassMissingWeight, classPowerWeight, hp, false_and, ite_false,
      mul_zero, le_refl]
  case pos =>
    by_cases hsel : Membership.mem greedyPrimeClass p
    case pos =>
      have hzero : primeClassMissingWeight greedyPrimeClass primeEulerLogWeight p = 0 := by
        simp only [primeClassMissingWeight, hsel, not_true_eq_false, and_false, ite_false]
      rw [hzero]
      exact mul_nonneg (by norm_num) (classPowerWeight_nonneg greedyDeletedPrimeClass 1 p)
    case neg =>
      have hdel : Membership.mem greedyDeletedPrimeClass p := by
        refine And.intro hp ?_
        intro hi
        exact hsel (And.intro hp hi)
      simp only [primeClassMissingWeight, ite_eq_left (And.intro hp hsel),
        classPowerWeight, ite_eq_left (And.intro hp hdel), Real.rpow_neg_one]
      simpa only [div_eq_mul_inv] using primeEulerLogWeight_le_two_div p hp

end PrimeFactorOscillations.PrimeClassDeletion

/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/

import PrimeFactorOscillations.Helpers.PowerPolynomialLaw

/-!
# AffineSumClock

Maintained extraction of completed detector/packet proof components.
All original theorem hypotheses and retained proof bodies are preserved.
This module alone asserts no improved zero-free boundary.
-/

set_option autoImplicit false
set_option Elab.async false

/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/

/-!
# Affine prime-sum clock factors

The recurrence below is the normalized unit-sum recurrence over a prime
field. This probe checks its algebra and the complete finite signed clock
consumer. It does not assert a growing-cutoff prime-input sampling theorem
or the missing infinite-range one-sided estimate.
-/


noncomputable section
namespace PrimeFactorOscillations.AffineClock

def sumFactor (q : Real) : Nat -> Real
  | 0 => 1
  | n + 1 => 1 - sumFactor q n / q

theorem sumFactor_bounds (q : Real) (hq : 2 <= q) (n : Nat) :
    And (1 - 1 / q <= sumFactor q n) (sumFactor q n <= 1) := by
  have hq0 : 0 < q := by linarith
  have hi : 0 <= (1 : Real) / q := div_nonneg (by norm_num) (le_of_lt hq0)
  have hi1 : (1 : Real) / q <= 1 := by
    have h1q : (1 : Real) <= q := by linarith
    have hd : (1 : Real) / q <= q / q :=
      div_le_div_of_nonneg_right h1q (le_of_lt hq0)
    simpa [div_self (ne_of_gt hq0)] using hd
  induction n with
  | zero =>
      dsimp [sumFactor]
      exact And.intro (by linarith) le_rfl
  | succ n ih =>
      have ha0 : 0 <= sumFactor q n := by linarith [ih.1]
      have hd : sumFactor q n / q <= 1 / q :=
        div_le_div_of_nonneg_right ih.2 (le_of_lt hq0)
      have hd0 : 0 <= sumFactor q n / q :=
        div_nonneg ha0 (le_of_lt hq0)
      dsimp [sumFactor]
      exact And.intro (by linarith) (by linarith)

theorem sumFactor_closed (q : Real) (hq : Not (q = 0))
    (hq1 : Not (q + 1 = 0)) (n : Nat) :
    sumFactor q n = q / (q + 1) + (-1 / q) ^ n / (q + 1) := by
  induction n with
  | zero =>
      dsimp [sumFactor]
      simp only [pow_zero]
      field_simp [hq, hq1]
  | succ n ih =>
      dsimp [sumFactor]
      rw [ih, pow_succ]
      field_simp [hq, hq1]
      ring

theorem signed_clock_comparison {I : Type*} (S : Finset I)
    (q mass : I -> Real) (hq : forall p, Membership.mem S p -> 2 <= q p)
    (hm : forall p, Membership.mem S p -> 0 <= mass p)
    (nu feedback : Real) (n : Nat) :
    And
      (0 <= (nu * feedback - S.sum (fun p => mass p * sumFactor (q p) n)) -
        (nu * feedback - S.sum mass))
      ((nu * feedback - S.sum (fun p => mass p * sumFactor (q p) n)) -
        (nu * feedback - S.sum mass) <= S.sum (fun p => mass p / q p)) := by
  have heq :
      (nu * feedback - S.sum (fun p => mass p * sumFactor (q p) n)) -
          (nu * feedback - S.sum mass) =
        S.sum (fun p => mass p * (1 - sumFactor (q p) n)) := by
    simp only [mul_sub, mul_one, Finset.sum_sub_distrib]
    ring
  rw [heq]
  constructor
  . apply Finset.sum_nonneg
    intro p hp
    have hb := sumFactor_bounds (q p) (hq p hp) n
    exact mul_nonneg (hm p hp) (by linarith [hb.2])
  . calc
      _ <= S.sum (fun p => mass p * (1 / q p)) := by
        apply Finset.sum_le_sum
        intro p hp
        have hb := sumFactor_bounds (q p) (hq p hp) n
        apply mul_le_mul_of_nonneg_left _ (hm p hp)
        linarith [hb.1]
      _ = S.sum (fun p => mass p / q p) := by
        apply Finset.sum_congr rfl
        intro p hp
        ring

end PrimeFactorOscillations.AffineClock

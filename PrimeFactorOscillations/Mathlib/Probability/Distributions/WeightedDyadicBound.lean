/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import Mathlib.Tactic.Linarith
import PrimeFactorOscillations.Mathlib.Probability.Distributions.WeightedDyadic

/-!
# Cumulative bounds for arithmetic dyadic weights

The uniform input (j+1)*w_j <= 2^j retains the logarithmic improvement
after accumulating all blocks. The bounds apply at every cutoff and
feed the complete weighted geometric probability tail.
-/

set_option autoImplicit false
set_option Elab.async false

namespace Nat

theorem dyadicPrefixWeight_succ_last (w : Nat -> Nat) (t : Nat) :
    dyadicPrefixWeight w (t + 1) = dyadicPrefixWeight w t + w t := by
  exact Finset.sum_range_succ w t

theorem dyadicPrefixWeight_add_one_le_pow (w : Nat -> Nat)
    (hw : forall j, (j + 1) * w j <= 2 ^ j) (t : Nat) :
    dyadicPrefixWeight w t + 1 <= 2 ^ t := by
  induction t with
  | zero => simp [dyadicPrefixWeight]
  | succ t ih =>
    have hu : w t <= (t + 1) * w t := by
      nlinarith [Nat.zero_le (t * w t)]
    have ht : w t <= 2 ^ t := hu.trans (hw t)
    rw [dyadicPrefixWeight_succ_last, pow_succ]
    nlinarith

/-- Accumulation preserves a reciprocal-linear factor in the block index. -/
theorem dyadicPrefixWeight_mul_le_three_pow (w : Nat -> Nat)
    (hw : forall j, (j + 1) * w j <= 2 ^ j) (t : Nat) :
    (t + 1) * dyadicPrefixWeight w t <= 3 * 2 ^ t := by
  induction t with
  | zero => simp [dyadicPrefixWeight]
  | succ t ih =>
    cases t with
    | zero =>
      have h0 := hw 0
      simp only [zero_add, one_mul, pow_zero] at h0
      simpa [dyadicPrefixWeight] using (show 2 * w 0 <= 6 by nlinarith)
    | succ s =>
      let W := dyadicPrefixWeight w (s + 1)
      let c := 2 ^ (s + 1)
      have hsum : (s + 2) * (W + w (s + 1)) <= 4 * c := by
        dsimp only [W, c]
        nlinarith [hw (s + 1)]
      have hstep : (s + 2) * ((s + 3) * (W + w (s + 1))) <=
          (s + 2) * (3 * (2 * c)) := by
        calc
          (s + 2) * ((s + 3) * (W + w (s + 1))) =
              (s + 3) * ((s + 2) * (W + w (s + 1))) := by ring
          _ <= (s + 3) * (4 * c) := Nat.mul_le_mul_left _ hsum
          _ <= (s + 2) * (3 * (2 * c)) := by nlinarith [Nat.zero_le (s * c)]
      have h := Nat.le_of_mul_le_mul_left hstep (Nat.succ_pos (s + 1))
      rw [dyadicPrefixWeight_succ_last, pow_succ']
      exact h

end Nat

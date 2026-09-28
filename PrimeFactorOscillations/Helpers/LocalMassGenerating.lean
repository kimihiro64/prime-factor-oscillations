import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import PrimeFactorOscillations.Definitions.Reversals

/-! # Exact local-mass generating functions and finite tail bounds -/

set_option autoImplicit false

namespace PrimeFactorOscillations

theorem finiteLocalMass_eq_zero_of_length_lt (eta : Nat -> Rat) (xs : List Nat)
    (r : Nat) (hr : xs.length < r) : finiteLocalMass eta xs r = 0 := by
  induction xs generalizing r with
  | nil =>
      cases r with
      | zero => simp at hr
      | succ r => rfl
  | cons p xs ih =>
      cases r with
      | zero => simp at hr
      | succ r =>
          have hlen : xs.length < r := by simpa using hr
          rw [finiteLocalMass, ih (r + 1) (by omega), ih r hlen]
          ring

theorem finiteLocalMass_nonneg (eta : Nat -> Rat) (xs : List Nat)
    (heta : forall p, List.Mem p xs -> 0 <= eta p /\ eta p <= 1) (r : Nat) :
    0 <= finiteLocalMass eta xs r := by
  induction xs generalizing r with
  | nil => cases r <;> simp [finiteLocalMass]
  | cons p xs ih =>
      have hp := heta p (List.Mem.head _)
      have ht : forall q, List.Mem q xs -> 0 <= eta q /\ eta q <= 1 :=
        fun q hq => heta q (List.Mem.tail _ hq)
      cases r with
      | zero => exact mul_nonneg (sub_nonneg.mpr hp.2) (ih ht 0)
      | succ r =>
          exact add_nonneg
            (mul_nonneg (sub_nonneg.mpr hp.2) (ih ht (r + 1)))
            (mul_nonneg hp.1 (ih ht r))

/-- Exact finite generating function; no asymptotic or independence assumption
is hidden in this algebraic identity for the Bernoulli recurrence. -/
theorem finiteLocalMass_generating (eta : Nat -> Rat) (xs : List Nat) (z : Rat) :
    (Finset.range (xs.length + 1)).sum (fun r => finiteLocalMass eta xs r * z ^ r) =
      (xs.map (fun p => 1 - eta p + eta p * z)).prod := by
  induction xs with
  | nil => simp [finiteLocalMass]
  | cons p xs ih =>
      simp only [List.length_cons, List.map_cons, List.prod_cons]
      rw [Finset.sum_range_succ']
      simp only [finiteLocalMass, pow_zero, mul_one, pow_succ]
      simp_rw [add_mul, mul_assoc]
      rw [Finset.sum_add_distrib, <- Finset.mul_sum, <- Finset.mul_sum]
      have hshift :
          (Finset.range (xs.length + 1)).sum
              (fun r => finiteLocalMass eta xs (r + 1) * (z ^ r * z)) +
            finiteLocalMass eta xs 0 =
          (Finset.range (xs.length + 1)).sum
              (fun r => finiteLocalMass eta xs r * z ^ r) := by
        have h := Finset.sum_range_succ'
          (fun r => finiteLocalMass eta xs r * z ^ r) (xs.length + 1)
        rw [Finset.sum_range_succ, finiteLocalMass_eq_zero_of_length_lt eta xs
          (xs.length + 1) (by omega)] at h
        simp only [zero_mul, add_zero, pow_succ, pow_zero, mul_one] at h
        exact h.symm
      have hlast :
          (Finset.range (xs.length + 1)).sum
              (fun r => finiteLocalMass eta xs r * (z ^ r * z)) =
            z * (Finset.range (xs.length + 1)).sum
              (fun r => finiteLocalMass eta xs r * z ^ r) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro r hr
        ring
      rw [hlast]
      rw [<- ih]
      have hs := congrArg (fun t : Rat => (1 - eta p) * t) hshift
      nlinarith only [hs]

private theorem rat_power_mono_index (z : Rat) (hz : 1 <= z)
    (k r : Nat) (hkr : k <= r) : z ^ k <= z ^ r := by
  choose d hd using Nat.exists_eq_add_of_le hkr
  subst r
  clear hkr
  have hz0 : 0 <= z := le_trans (by norm_num) hz
  have hpow : 1 <= z ^ d := by
    induction d with
    | zero => simp
    | succ d ih =>
        rw [pow_succ]
        have hm := mul_le_mul_of_nonneg_left hz (pow_nonneg hz0 d)
        nlinarith
  have hm := mul_le_mul_of_nonneg_left hpow (pow_nonneg hz0 k)
  simpa only [mul_one, <- pow_add] using hm

/-- Finite exponential-moment tail bound, including zero and forced local laws. -/
theorem finiteLocalMass_tail_mul_pow_le (eta : Nat -> Rat) (xs : List Nat)
    (heta : forall p, List.Mem p xs -> 0 <= eta p /\ eta p <= 1)
    (k : Nat) (z : Rat) (hz : 1 <= z) :
    z ^ k * ((Finset.range (xs.length + 1)).filter (fun r => k <= r)).sum
      (finiteLocalMass eta xs) <=
        (xs.map (fun p => 1 - eta p + eta p * z)).prod := by
  calc
    _ = ((Finset.range (xs.length + 1)).filter (fun r => k <= r)).sum
        (fun r => finiteLocalMass eta xs r * z ^ k) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro r hr
      ring
    _ <= ((Finset.range (xs.length + 1)).filter (fun r => k <= r)).sum
        (fun r => finiteLocalMass eta xs r * z ^ r) := by
      apply Finset.sum_le_sum
      intro r hr
      exact mul_le_mul_of_nonneg_left
        (rat_power_mono_index z hz k r (Finset.mem_filter.mp hr).2)
        (finiteLocalMass_nonneg eta xs heta r)
    _ <= (Finset.range (xs.length + 1)).sum
        (fun r => finiteLocalMass eta xs r * z ^ r) := by
      apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
      intro r hr hn
      exact mul_nonneg (finiteLocalMass_nonneg eta xs heta r)
        (pow_nonneg (le_trans (by norm_num) hz) r)
    _ = _ := finiteLocalMass_generating eta xs z

end PrimeFactorOscillations

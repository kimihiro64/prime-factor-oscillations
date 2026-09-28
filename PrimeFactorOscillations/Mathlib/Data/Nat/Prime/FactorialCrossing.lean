/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import Mathlib.Data.Finset.Max
import Mathlib.Order.Interval.Finset.Nat
import PrimeFactorOscillations.Mathlib.Data.Nat.Prime.FactorialCells

/-! # Adjacent prime indices crossing a factorial barrier -/

namespace Nat

/-- A finite sequence crossing a threshold has an adjacent crossing step. -/
theorem exists_adjacent_threshold_crossing (f : Nat -> Nat) {u v b : Nat}
    (huv : u <= v) (hu : f u <= b) (hv : b < f v) :
    exists d, u <= d /\ d < v /\ f d <= b /\ b < f (d + 1) := by
  let s := (Finset.Icc u v).filter (fun i => f i <= b)
  have hs : s.Nonempty := by
    exact Exists.intro u (Finset.mem_filter.mpr
      (And.intro (Finset.mem_Icc.mpr (And.intro (Nat.le_refl u) huv)) hu))
  let d := s.max' hs
  have hd := Finset.mem_filter.mp (s.max'_mem hs)
  have hdu : u <= d := (Finset.mem_Icc.mp hd.1).1
  have hdv : d <= v := (Finset.mem_Icc.mp hd.1).2
  have hdf : f d <= b := hd.2
  have hstrict : d < v := by
    by_contra hn
    have heq : d = v := by omega
    rw [heq] at hdf
    omega
  have hnext : b < f (d + 1) := by
    by_contra hn
    have hm : Membership.mem s (d + 1) := Finset.mem_filter.mpr
      (And.intro (Finset.mem_Icc.mpr (And.intro (by omega) (by omega)))
        (by omega))
    have hmax : d + 1 <= d := s.le_max' (d + 1) hm
    omega
  exact Exists.intro d (And.intro hdu (And.intro hstrict (And.intro hdf hnext)))

/-- Crossing a factorial barrier in a prime sequence creates a long gap. -/
theorem exists_prime_step_across_factorial_block (f : Nat -> Nat)
    (hprime : forall i, Nat.Prime (f i)) {L c u v : Nat}
    (hc : 0 < c) (huv : u <= v)
    (hu : f u <= c * Nat.factorial L + 1)
    (hv : c * Nat.factorial L + 1 < f v) :
    exists d, u <= d /\ d < v /\ f d + L <= f (d + 1) := by
  choose d hd using exists_adjacent_threshold_crossing f huv hu hv
  have hnext : c * Nat.factorial L + L + 1 <= f (d + 1) := by
    by_contra hn
    have hj : 2 <= f (d + 1) - c * Nat.factorial L := by omega
    have hjL : f (d + 1) - c * Nat.factorial L <= L := by omega
    have hnot := Nat.not_prime_mul_factorial_add hc hj hjL
    have heq : c * Nat.factorial L +
        (f (d + 1) - c * Nat.factorial L) = f (d + 1) := by omega
    rw [heq] at hnot
    exact hnot (hprime (d + 1))
  exact Exists.intro d (And.intro hd.1 (And.intro hd.2.1 (by omega)))

end Nat

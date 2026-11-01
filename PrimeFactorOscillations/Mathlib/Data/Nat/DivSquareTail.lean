/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import Mathlib.Algebra.BigOperators.Intervals

/-!
# An integer tail bound for square-divisor counts

A one-step comparison of natural quotients telescopes without a rounding
error. The finite upper endpoint is arbitrary; all denominators are positive
under the lower-cutoff hypothesis. These are classical counting estimates.
-/

set_option autoImplicit false
set_option Elab.async false

namespace Nat

/-- A square-divisor quotient is absorbed by two consecutive divisor quotients. -/
theorem div_sq_add_div_le_div_pred (Y u : Nat) (hu : 2 <= u) :
    Y / (u * u) + Y / u <= Y / (u - 1) := by
  let q := Y / u
  let r := Y / (u * u)
  have hr : r = q / u := by
    dsimp [q, r]
    rw [Nat.div_div_eq_div_mul]
  have hur : u * r <= q := by
    rw [hr]
    exact Nat.mul_div_le q u
  have hpred : (u - 1) * r <= q :=
    (Nat.mul_le_mul_right r (Nat.sub_le u 1)).trans hur
  have huq : u * q <= Y := Nat.mul_div_le Y u
  have hproduct : (u - 1) * (q + r) <= Y := by
    calc
      (u - 1) * (q + r) = (u - 1) * q + (u - 1) * r := by rw [Nat.mul_add]
      _ <= (u - 1) * q + q := Nat.add_le_add_left hpred _
      _ = ((u - 1) + 1) * q := by rw [Nat.add_mul, Nat.one_mul]
      _ = u * q := by rw [Nat.sub_add_cancel (by omega : 1 <= u)]
      _ <= Y := huq
  change r + q <= Y / (u - 1)
  apply (Nat.le_div_iff_mul_le (by omega : 0 < u - 1)).mpr
  simpa only [Nat.mul_comm, Nat.add_comm] using hproduct

/-- Every finite square-divisor tail is bounded by one natural quotient. -/
theorem sum_Ico_div_sq_le (Y T N : Nat) (hT : 2 <= T) :
    Finset.sum (Finset.Ico T N) (fun u => Y / (u * u)) <= Y / (T - 1) := by
  have haux : forall K : Nat, T <= K ->
      Finset.sum (Finset.Ico T K) (fun u => Y / (u * u)) + Y / (K - 1) <=
        Y / (T - 1) := by
    intro K hTK
    induction K, hTK using Nat.le_induction with
    | base => simp
    | succ n hn ih =>
      rw [Finset.sum_Ico_succ_top hn]
      have hstep := div_sq_add_div_le_div_pred Y n (hT.trans hn)
      have hpred : n + 1 - 1 = n := by omega
      rw [hpred]
      omega
  by_cases hTN : T <= N
  . exact (Nat.le_add_right _ _).trans (haux N hTN)
  . rw [Finset.Ico_eq_empty_of_le (by omega : N <= T), Finset.sum_empty]
    exact Nat.zero_le _

end Nat

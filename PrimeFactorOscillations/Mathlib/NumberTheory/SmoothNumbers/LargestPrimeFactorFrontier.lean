/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Mathlib.NumberTheory.SmoothNumbers.LargestPrimeFactorSum

/-!
# The exact odd largest-factor frontier below four times the cutoff

Every retained odd integer with largest prime factor above M has cofactor
one or three. The identity retains arbitrary additive weights, hence actual
prime-pair multiplicities. It is not a distribution assertion about those weights.
-/

set_option autoImplicit false
set_option Elab.async false

namespace Nat

theorem sum_largestPrimeFactor_frontier_eq_two_rows {A : Type*} [AddCommMonoid A]
    (f : Nat -> A) (hEven : forall n, f (2 * n) = 0) (M : Nat) (hM : 3 <= M) :
    Finset.sum ((Finset.Icc 1 (4 * M - 1)).filter
        (fun n => M < largestPrimeFactor n)) f =
      Finset.sum ((Finset.Icc (M + 1) (4 * M - 1)).filter Nat.Prime) f +
      Finset.sum ((Finset.Icc (M + 1) ((4 * M - 1) / 3)).filter Nat.Prime)
        (fun r => f (3 * r)) := by
  have hDiv : (4 * M - 1) / M = 3 :=
    Nat.div_eq_of_lt_le (by omega) (by omega)
  have hOne : largestPrimeFactorRow (4 * M - 1) M 1 =
      (Finset.Icc (M + 1) (4 * M - 1)).filter Nat.Prime := by
    simp [largestPrimeFactorRow, largestPrimeFactor, max_eq_left (by omega : 1 <= M + 1)]
  have hThree : largestPrimeFactorRow (4 * M - 1) M 3 =
      (Finset.Icc (M + 1) ((4 * M - 1) / 3)).filter Nat.Prime := by
    unfold largestPrimeFactorRow
    rw [largestPrimeFactor_of_prime (by decide : Nat.Prime 3),
      max_eq_left (by omega : 3 <= M + 1)]
  rw [sum_largePrimeFactor_eq f (4 * M - 1) M (by omega), hDiv]
  rw [Finset.sum_Icc_succ_top (a := 1) (b := 2) (by omega)]
  rw [Finset.sum_Icc_succ_top (a := 1) (b := 1) (by omega)]
  simp only [Finset.Icc_self, Finset.sum_singleton, hOne, hThree,
    one_mul, hEven, Finset.sum_const_zero, add_zero]

end Nat

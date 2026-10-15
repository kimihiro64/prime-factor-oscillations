/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import Mathlib.Analysis.Complex.Basic
import PrimeFactorOscillations.Mathlib.NumberTheory.SmoothNumbers.LargestPrimeFactorSum

/-!
# Finite transfer from prime rows to smooth and largest-factor sums

These inequalities keep the actual prime-row norms. They do not assume that
Dirichlet nonvanishing has already been turned into a quantitative prime bound.
-/

set_option autoImplicit false
set_option Elab.async false

namespace Nat

theorem sum_smoothNumbersUpTo_eq_sub_prime_rows (f : Nat -> Complex)
    (hmul : forall m p, f (m * p) = f m * f p) (X y : Nat) (hy : 1 <= y) :
    Finset.sum (smoothNumbersUpTo X (y + 1)) f =
      Finset.sum (Finset.Icc 1 X) f -
        Finset.sum (Finset.Icc 1 (X / y)) (fun m =>
          f m * Finset.sum (largestPrimeFactorRow X y m) f) := by
  apply eq_sub_of_add_eq
  simpa only [hmul, Finset.mul_sum] using
    sum_smoothNumbersUpTo_add_largestPrimeFactor_rows f X y hy

theorem norm_sum_smoothNumbersUpTo_le_prime_rows (f : Nat -> Complex)
    (hmul : forall m p, f (m * p) = f m * f p) (X y : Nat) (hy : 1 <= y)
    (hunit : forall m, Membership.mem (Finset.Icc 1 (X / y)) m -> norm (f m) <= 1) :
    norm (Finset.sum (smoothNumbersUpTo X (y + 1)) f) <=
      norm (Finset.sum (Finset.Icc 1 X) f) +
        Finset.sum (Finset.Icc 1 (X / y)) (fun m =>
          norm (Finset.sum (largestPrimeFactorRow X y m) f)) := by
  rw [sum_smoothNumbersUpTo_eq_sub_prime_rows f hmul X y hy]
  apply (norm_sub_le _ _).trans
  apply _root_.add_le_add le_rfl
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro m hm
  rw [norm_mul]
  exact mul_le_of_le_one_left (norm_nonneg _) (hunit m hm)

theorem norm_sum_largePrimeFactor_twist_le_prime_rows (f : Nat -> Complex)
    (X y : Nat) (hy : 1 <= y) :
    norm (Finset.sum ((Finset.Icc 1 X).filter (fun n => y < largestPrimeFactor n))
      (fun n => f (largestPrimeFactor n))) <=
      Finset.sum (Finset.Icc 1 (X / y)) (fun m =>
        norm (Finset.sum (largestPrimeFactorRow X y m) f)) := by
  rw [sum_largePrimeFactor_twist_eq f X y hy]
  exact norm_sum_le _ _

end Nat

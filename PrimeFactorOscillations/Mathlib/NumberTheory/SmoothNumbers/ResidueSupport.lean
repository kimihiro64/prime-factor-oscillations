/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import Mathlib.Data.ZMod.Units
import PrimeFactorOscillations.Mathlib.NumberTheory.SmoothNumbers.LargestPrimeFactorSum

/-!
# Largest-factor residue support

A largest factor above y is a unit modulo every positive y-smooth modulus.
The smooth and nonsmooth cardinalities partition the positive integer interval.
-/

set_option autoImplicit false
set_option Elab.async false

namespace Nat

theorem largestPrimeFactor_le_self {n : Nat} (hn : 0 < n) :
    largestPrimeFactor n <= n := by
  apply (largestPrimeFactor_le_iff _ _).mpr
  exact And.intro hn (fun _ hp => le_of_mem_primeFactors hp)

theorem isUnit_largestPrimeFactor_of_le_cutoff {N n y : Nat} [NeZero N]
    (hn : 0 < n) (hN : largestPrimeFactor N <= y)
    (hyn : y < largestPrimeFactor n) : IsUnit (largestPrimeFactor n : ZMod N) := by
  have hy : 1 <= y := (one_le_largestPrimeFactor N).trans hN
  have hn2 : 1 < n := (lt_of_le_of_lt hy hyn).trans_le (largestPrimeFactor_le_self hn)
  have hp := largestPrimeFactor_prime hn2
  rw [ZMod.isUnit_iff_coprime]
  by_contra h
  have hd : Dvd.dvd (largestPrimeFactor n) N := (hp.dvd_iff_not_coprime).mpr h
  have hle := largestPrimeFactor_mono_dvd hd (NeZero.ne N)
  rw [largestPrimeFactor_of_prime hp] at hle
  exact (not_lt_of_ge (hle.trans hN)) hyn

theorem card_smoothNumbersUpTo_add_largePrimeFactor (X y : Nat) (hy : 1 <= y) :
    (smoothNumbersUpTo X (y + 1)).card +
      ((Finset.Icc 1 X).filter (fun n => y < largestPrimeFactor n)).card = X := by
  have h := sum_smoothNumbersUpTo_add_largestPrimeFactor_rows (fun _ => (1 : Nat)) X y hy
  rw [<- sum_largePrimeFactor_eq (fun _ => (1 : Nat)) X y hy] at h
  simpa using h

end Nat

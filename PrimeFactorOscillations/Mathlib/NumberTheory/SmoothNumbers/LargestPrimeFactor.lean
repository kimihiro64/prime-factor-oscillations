/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.NumberTheory.SmoothNumbers

/-!
# Largest prime factors and inclusive smoothness

The largest prime factor is defined from the finite set of prime divisors.
Its value is one at zero and one; every arithmetic interpretation excludes zero.
The product law retains repeated prime factors, and smoothness uses the inclusive
cutoff by matching Mathlib's strict-cutoff set at y + 1.

All proofs use Mathlib directly. No historical LPF project source is imported.
-/

set_option autoImplicit false
set_option Elab.async false

namespace Nat

/-- Largest prime factor, with value one at zero and one. Analytic domains exclude zero. -/
def largestPrimeFactor (n : Nat) : Nat := max 1 (n.primeFactors.sup id)

theorem largestPrimeFactor_le_iff (n y : Nat) :
    largestPrimeFactor n <= y <-> 1 <= y /\ forall p, Membership.mem n.primeFactors p -> p <= y := by
  simp [largestPrimeFactor, Finset.sup_le_iff]

theorem one_le_largestPrimeFactor (n : Nat) : 1 <= largestPrimeFactor n :=
  le_max_left _ _

theorem primeFactor_le_largestPrimeFactor {n p : Nat}
    (hp : Membership.mem n.primeFactors p) : p <= largestPrimeFactor n := by
  exact (Finset.le_sup (f := id) hp).trans (le_max_right _ _)

theorem largestPrimeFactor_eq_max' (n : Nat) (hn : 1 < n) :
    largestPrimeFactor n = n.primeFactors.max' (nonempty_primeFactors.mpr hn) := by
  let hne := nonempty_primeFactors.mpr hn
  have hmem := Finset.max'_mem n.primeFactors hne
  apply le_antisymm
  next =>
    apply (largestPrimeFactor_le_iff _ _).mpr
    refine And.intro (Nat.prime_of_mem_primeFactors hmem).one_lt.le ?_
    intro p hp
    exact Finset.le_max' n.primeFactors p hp
  next =>
    exact primeFactor_le_largestPrimeFactor hmem

theorem largestPrimeFactor_prime {n : Nat} (hn : 1 < n) :
    Nat.Prime (largestPrimeFactor n) := by
  rw [largestPrimeFactor_eq_max' n hn]
  exact prime_of_mem_primeFactors (Finset.max'_mem _ _)

theorem largestPrimeFactor_dvd {n : Nat} (hn : 1 < n) :
    Dvd.dvd (largestPrimeFactor n) n := by
  rw [largestPrimeFactor_eq_max' n hn]
  exact dvd_of_mem_primeFactors (Finset.max'_mem _ _)

theorem largestPrimeFactor_mono_dvd {m n : Nat} (hd : Dvd.dvd m n)
    (hn : Not (n = 0)) : largestPrimeFactor m <= largestPrimeFactor n := by
  apply (largestPrimeFactor_le_iff _ _).mpr
  refine And.intro (one_le_largestPrimeFactor _) ?_
  intro p hp
  exact primeFactor_le_largestPrimeFactor (primeFactors_mono hd hn hp)

theorem largestPrimeFactor_mul {m n : Nat} (hm : Not (m = 0)) (hn : Not (n = 0)) :
    largestPrimeFactor (m * n) = max (largestPrimeFactor m) (largestPrimeFactor n) := by
  simp [largestPrimeFactor, primeFactors_mul hm hn, Finset.sup_union,
    max_assoc, max_left_comm, max_comm]

theorem largestPrimeFactor_of_prime {p : Nat} (hp : Nat.Prime p) :
    largestPrimeFactor p = p := by
  simp [largestPrimeFactor, Nat.Prime.primeFactors hp, max_eq_right hp.one_lt.le]

theorem largestPrimeFactor_mul_prime {m p : Nat} (hm : Not (m = 0))
    (hp : Nat.Prime p) (hmp : largestPrimeFactor m <= p) :
    largestPrimeFactor (m * p) = p := by
  rw [largestPrimeFactor_mul hm hp.ne_zero, largestPrimeFactor_of_prime hp,
    max_eq_right hmp]

theorem mem_smoothNumbers_iff_largestPrimeFactor_le {n y : Nat}
    (hn : Not (n = 0)) (hy : 1 <= y) :
    Membership.mem (smoothNumbers (y + 1)) n <-> largestPrimeFactor n <= y := by
  rw [mem_smoothNumbers, largestPrimeFactor_le_iff]
  constructor
  next =>
    intro h
    refine And.intro hy ?_
    intro p hp
    exact Nat.lt_succ_iff.mp (h.2 p (mem_primeFactors_iff_mem_primeFactorsList.mp hp))
  next =>
    intro h
    refine And.intro hn ?_
    intro p hp
    exact Nat.lt_succ_iff.mpr (h.2 p (mem_primeFactors_iff_mem_primeFactorsList.mpr hp))

end Nat

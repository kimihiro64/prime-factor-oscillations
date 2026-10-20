/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/

import PrimeFactorOscillations.Helpers.PrimeProfileJointProbeLocality
import PrimeFactorOscillations.Mathlib.Analysis.SpecialFunctions.Log.FiniteLogDeficitEndpoint

/-!
# The exact endpoint envelope of all positive probability-profile probes

The supremum of every escape-multiplicity threshold is the maximum of two
rational prime sums. This gives an exact locality criterion for simultaneous
budgets at all positive probes, with one common permutation throughout.
-/

set_option autoImplicit false
set_option Elab.async false

noncomputable section

namespace PrimeFactorOscillations.PrimeProfileRigidity

/-- The quadratic endpoint of the last k coordinates of the observed prime prefix. -/
def primeEscapeQuadraticEndpoint (n k : Nat) : Real :=
  Real.logDeficitQuadraticEndpoint (Finset.range k)
    (fun i => (PrimeFactorUnimodality.primeAt (n + 1 - k + i) : Real))
    (PrimeFactorUnimodality.primeAt n : Real)

/-- The reciprocal endpoint of the last k coordinates of the observed prime prefix. -/
def primeEscapeReciprocalEndpoint (n k : Nat) : Real :=
  Real.logDeficitReciprocalEndpoint (Finset.range k)
    (fun i => (PrimeFactorUnimodality.primeAt (n + 1 - k + i) : Real))
    (PrimeFactorUnimodality.primeAt n : Real)

/-- The complete signed threshold is a positive sum over its exact terminal block. -/
theorem primePrefixEscapeThreshold_eq_finiteLogDeficit (t : Real) (n k : Nat)
    (hk : k <= n + 1) :
    primePrefixEscapeThreshold t n k =
      Real.finiteLogDeficit (Finset.range k)
        (fun i => (PrimeFactorUnimodality.primeAt (n + 1 - k + i) : Real))
        t (PrimeFactorUnimodality.primeAt n : Real) := by
  have hindex : n + 1 - k + k = n + 1 := by omega
  have hsum := Finset.sum_range_add (primeLogWeight t) (n + 1 - k) k
  rw [hindex] at hsum
  unfold primePrefixEscapeThreshold Real.finiteLogDeficit Real.normalizedLogDeficit
  rw [<- Finset.mul_sum, Finset.sum_neg_distrib]
  unfold primeLogWeight at hsum
  unfold primeLogWeight
  rw [hsum]
  ring

/-- Every positive probe lies below the explicit rational endpoint envelope. -/
theorem primePrefixEscapeThreshold_le_endpoints (t : Real) (n k : Nat)
    (ht : 0 < t) (hk : k <= n + 1) :
    primePrefixEscapeThreshold t n k <=
      max (primeEscapeQuadraticEndpoint n k) (primeEscapeReciprocalEndpoint n k) := by
  have hr : (0 : Real) < PrimeFactorUnimodality.primeAt n := by
    exact_mod_cast (PrimeFactorUnimodality.prime_primeAt n).pos
  have hp : forall i : Nat, Membership.mem (Finset.range k) i ->
      (0 : Real) < PrimeFactorUnimodality.primeAt (n + 1 - k + i) := by
    intro i _
    exact_mod_cast (PrimeFactorUnimodality.prime_primeAt (n + 1 - k + i)).pos
  rw [primePrefixEscapeThreshold_eq_finiteLogDeficit t n k hk]
  exact Real.finiteLogDeficit_le_max_endpoints _ _ t _ ht hr hp

/-- Every strict sublevel of the rational envelope has an actual positive-probe witness. -/
theorem prime_prefix_exists_probe_iff (n k : Nat) (hkpos : 0 < k)
    (hk : k <= n + 1) (C : Real) :
    (exists t : Real, 0 < t /\ C < primePrefixEscapeThreshold t n k) <->
      C < max (primeEscapeQuadraticEndpoint n k) (primeEscapeReciprocalEndpoint n k) := by
  have hr : (0 : Real) < PrimeFactorUnimodality.primeAt n := by
    exact_mod_cast (PrimeFactorUnimodality.prime_primeAt n).pos
  have hs : (Finset.range k).Nonempty := by
    exact Exists.intro 0 (Finset.mem_range.mpr hkpos)
  have hp : forall i : Nat, Membership.mem (Finset.range k) i ->
      (0 : Real) < PrimeFactorUnimodality.primeAt (n + 1 - k + i) := by
    intro i _
    exact_mod_cast (PrimeFactorUnimodality.prime_primeAt (n + 1 - k + i)).pos
  have h := Real.finiteLogDeficit_exists_probe_iff (Finset.range k)
    (fun i => (PrimeFactorUnimodality.primeAt (n + 1 - k + i) : Real))
    (PrimeFactorUnimodality.primeAt n : Real) C hr hs hp
  simpa only [<- primePrefixEscapeThreshold_eq_finiteLogDeficit _ _ _ hk,
    primeEscapeQuadraticEndpoint, primeEscapeReciprocalEndpoint] using h

/-- The all-probe escape envelope is the least upper bound, including the prime 2 and n=0. -/
theorem primePrefixEscapeThreshold_isLUB (n k : Nat) (hkpos : 0 < k)
    (hk : k <= n + 1) :
    IsLUB {x : Real | exists t : Real, 0 < t /\ x = primePrefixEscapeThreshold t n k}
      (max (primeEscapeQuadraticEndpoint n k) (primeEscapeReciprocalEndpoint n k)) := by
  constructor
  . intro x hx
    let t := Classical.choose hx
    have ht := Classical.choose_spec hx
    rw [ht.2]
    exact primePrefixEscapeThreshold_le_endpoints t n k ht.1 hk
  . intro y hy
    by_contra hn
    have hex := (prime_prefix_exists_probe_iff n k hkpos hk y).mpr (lt_of_not_ge hn)
    let t := Classical.choose hex
    have ht := Classical.choose_spec hex
    have hle := hy (Exists.intro t (And.intro ht.1 rfl))
    exact (not_lt_of_ge hle) ht.2

/-- Joint budgets at every positive probe localize exactly below the rational endpoint envelope. -/
theorem prime_prefix_all_positive_probes_locality_iff (n k : Nat) (hkpos : 0 < k)
    (hk : k <= n + 1) (C : Real) :
    (exists M : Nat, forall e : Equiv.Perm Nat,
      (forall t : Real, 0 < t -> normalizedPrimePrefixDefect e (fun _ => t) n <= C) ->
      (((Finset.range (n + 1)).image e) \ Finset.range M).card < k) <->
      C < max (primeEscapeQuadraticEndpoint n k) (primeEscapeReciprocalEndpoint n k) := by
  let J := {t : Real // 0 < t}
  have hbudget (e : Equiv.Perm Nat) :
      (forall j : J, normalizedPrimePrefixDefect e (fun _ => j.val) n <= C) <->
      (forall t : Real, 0 < t -> normalizedPrimePrefixDefect e (fun _ => t) n <= C) := by
    constructor
    . intro h t ht
      exact h (Subtype.mk t ht)
    . intro h j
      exact h j.val j.property
  have hwitness :
      (exists j : J, C < primePrefixEscapeThreshold j.val n k) <->
      (exists t : Real, 0 < t /\ C < primePrefixEscapeThreshold t n k) := by
    constructor
    . intro h
      let j := Classical.choose h
      exact Exists.intro j.val (And.intro j.property (Classical.choose_spec h))
    . intro h
      let t := Classical.choose h
      have ht := Classical.choose_spec h
      exact Exists.intro (Subtype.mk t ht.1) ht.2
  have h := prime_prefix_joint_probe_locality_iff
    (fun j : J => j.val) (fun _ : J => C) (fun j : J => j.property) n k hkpos hk
  simp only [hbudget] at h
  exact h.trans (hwitness.trans (prime_prefix_exists_probe_iff n k hkpos hk C))

/-- For one escaping coordinate the all-positive-probe endpoint is exactly the boundary prime. -/
theorem prime_escape_one_endpoint (n : Nat) :
    max (primeEscapeQuadraticEndpoint n 1) (primeEscapeReciprocalEndpoint n 1) =
      (PrimeFactorUnimodality.primeAt n : Real) := by
  have hr : (0 : Real) < PrimeFactorUnimodality.primeAt n := by
    exact_mod_cast (PrimeFactorUnimodality.prime_primeAt n).pos
  have hquad : primeEscapeQuadraticEndpoint n 1 =
      (PrimeFactorUnimodality.primeAt n : Real) / 2 := by
    unfold primeEscapeQuadraticEndpoint Real.logDeficitQuadraticEndpoint
    simp only [Nat.add_sub_cancel, Finset.sum_range_one, Nat.add_zero]
    field_simp
  have hrecip : primeEscapeReciprocalEndpoint n 1 =
      (PrimeFactorUnimodality.primeAt n : Real) := by
    unfold primeEscapeReciprocalEndpoint Real.logDeficitReciprocalEndpoint
    simp only [Nat.add_sub_cancel, Finset.sum_range_one, Nat.add_zero]
    field_simp
  rw [hquad, hrecip, max_eq_right]
  linarith only [hr]

/-- A common budget across all positive probes has the sharp single-coordinate cutoff C < p_n. -/
theorem prime_prefix_all_positive_probes_one_locality_iff (n : Nat) (C : Real) :
    (exists M : Nat, forall e : Equiv.Perm Nat,
      (forall t : Real, 0 < t -> normalizedPrimePrefixDefect e (fun _ => t) n <= C) ->
      (((Finset.range (n + 1)).image e) \ Finset.range M).card < 1) <->
      C < (PrimeFactorUnimodality.primeAt n : Real) := by
  have h := prime_prefix_all_positive_probes_locality_iff n 1 (by omega) (by omega) C
  simpa only [prime_escape_one_endpoint] using h

end PrimeFactorOscillations.PrimeProfileRigidity

/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/

import PrimeFactorOscillations.Helpers.PrimeProfileEscapeSpectrum

/-!
# Exact localization from arbitrarily many simultaneous probe budgets

All probes constrain the same permutation and finite prefix. A common finite
block exchange witnesses every supercritical budget simultaneously, even for
an infinite or empty index type. Thus one strict individual threshold is
necessary and sufficient for localization of the prescribed multiplicity.
-/

set_option autoImplicit false
set_option Elab.async false

noncomputable section

namespace PrimeFactorOscillations.PrimeProfileRigidity

/-- One finite permutation escapes under every saturation budget in an arbitrary positive probe family. -/
theorem prime_prefix_joint_escape_at_threshold
    {J : Type*} (t : J -> Real) (ht : forall j : J, 0 < t j)
    (n k M : Nat) (hk : k <= n + 1) :
    exists e : Equiv.Perm Nat, exists L : Nat,
      (forall i : Nat, L <= i -> e i = i) /\
      k <= (((Finset.range (n + 1)).image e) \ Finset.range M).card /\
      (forall j : J, normalizedPrimePrefixDefect e (fun _ => t j) n <=
        primePrefixEscapeThreshold (t j) n k) := by
  have h := Finset.exists_common_prefixTail_escape_at_saturation
    (fun j : J => normalizedPrimePrefixWeight (t j) n) (fun _ : J => (0 : Real))
    (fun j => (normalizedPrimePrefixWeight_properties (t j) n (ht j)).2.1)
    (n + 1) k M hk
  simpa only [<- normalizedPrimePrefixDefect_eq_scaled_prefix,
    <- primePrefixEscapeThreshold_eq_saturation] using h

/-- Even infinitely many joint one-sided budgets localize precisely when one member is subcritical. -/
theorem prime_prefix_joint_probe_locality_iff
    {J : Type*} (t C : J -> Real) (ht : forall j : J, 0 < t j)
    (n k : Nat) (hkpos : 0 < k) (hk : k <= n + 1) :
    (exists M : Nat, forall e : Equiv.Perm Nat,
      (forall j : J, normalizedPrimePrefixDefect e (fun _ => t j) n <= C j) ->
      (((Finset.range (n + 1)).image e) \ Finset.range M).card < k) <->
    (exists j : J, C j < primePrefixEscapeThreshold (t j) n k) := by
  have hdata := fun j : J => normalizedPrimePrefixWeight_properties (t j) n (ht j)
  have h := Finset.prefixTail_joint_locality_iff
    (fun j : J => normalizedPrimePrefixWeight (t j) n) (fun _ : J => (0 : Real)) C
    (fun j => (hdata j).1) (fun j => (hdata j).2.1) (fun j => (hdata j).2.2)
    (n + 1) k hkpos hk
  simpa only [<- normalizedPrimePrefixDefect_eq_scaled_prefix,
    <- primePrefixEscapeThreshold_eq_saturation] using h

end PrimeFactorOscillations.PrimeProfileRigidity

/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/

import PrimeFactorOscillations.Helpers.PrimeProfileTransportParity
import PrimeFactorOscillations.Mathlib.Order.BoundedNatSequence

/-!
# A bounded prime-profile probe has a uniform discrete transport tail

The cutoff bounds use only prime enumeration tending to infinity.
They do not require the prime number theorem or a prime-pattern supply.
-/

set_option autoImplicit false
set_option Elab.async false

noncomputable section

namespace PrimeFactorOscillations.PrimeProfileRigidity

theorem eventually_prime_transport_lattice
    (e : Equiv.Perm Nat) (t : Nat -> Real) (ht : forall n, 0 < t n)
    (C : Real) (hC0 : 0 <= C)
    (hupper : exists M : Nat, forall n : Nat, M <= n ->
      normalizedPrimePrefixDefect e t n <= C) :
    exists M : Nat, forall n : Nat, M <= n ->
      (exists K : Nat,
        Finset.prefixDefect (fun j => (PrimeFactorUnimodality.primeAt j : Real))
          e (n + 1) = 2 * (K : Real)) /\
      Finset.prefixDefect (fun j => (PrimeFactorUnimodality.primeAt j : Real))
        e (n + 1) <= 4 * C := by
  let M0 := Classical.choose hupper
  have hM0 : forall n : Nat, M0 <= n -> normalizedPrimePrefixDefect e t n <= C :=
    Classical.choose_spec hupper
  have hlarge : exists M : Nat, max (4 * C) (2 + C) < (M : Real) :=
    exists_nat_gt _
  let M := Classical.choose hlarge
  have hM : max (4 * C) (2 + C) < (M : Real) := Classical.choose_spec hlarge
  refine Exists.intro (max M0 M) ?_
  intro n hn
  have hR : (M : Real) <= PrimeFactorUnimodality.primeAt n := by
    have hidx : M <= n := (le_max_right M0 M).trans hn
    have hcast : (M : Real) <= n := by exact_mod_cast hidx
    have hp : (n : Real) <= PrimeFactorUnimodality.primeAt n := by
      exact_mod_cast PrimeFactorUnimodality.primeAt_strictMono.id_le n
    exact hcast.trans hp
  have hC : C < (PrimeFactorUnimodality.primeAt n : Real) / 4 := by
    have hh := le_max_left (4 * C) (2 + C)
    linarith only [hh, hM, hR]
  have hsmall : 2 < (PrimeFactorUnimodality.primeAt n : Real) - C := by
    have hh := le_max_right (4 * C) (2 + C)
    linarith only [hh, hM, hR]
  have hcost := hM0 n ((le_max_left M0 M).trans hn)
  exact And.intro
    (prime_prefix_transport_even_of_cost_le e t n C (ht n) hC0 hC hcost hsmall)
    (prime_prefix_transport_le_four_mul_cost e t n C (ht n) hC0 hC hcost)

theorem eventually_uniform_prime_transport_error
    (e : Equiv.Perm Nat) (t : Nat -> Real) (ht : forall n, 0 < t n)
    (C : Real) (hC0 : 0 <= C)
    (hupper : exists M : Nat, forall n : Nat, M <= n ->
      normalizedPrimePrefixDefect e t n <= C)
    (eps : Real) (heps : 0 < eps) :
    exists M : Nat, forall n : Nat, M <= n -> forall v : Nat -> Real,
      0 < v n ->
      abs (normalizedPrimePrefixDefect e v n -
        Finset.prefixDefect (fun j => (PrimeFactorUnimodality.primeAt j : Real))
          e (n + 1)) < eps := by
  let M0 := Classical.choose hupper
  have hM0 : forall n : Nat, M0 <= n -> normalizedPrimePrefixDefect e t n <= C :=
    Classical.choose_spec hupper
  have hlarge : exists M : Nat, max (4 * C) (32 * C ^ 2 / eps) < (M : Real) :=
    exists_nat_gt _
  let M := Classical.choose hlarge
  have hM : max (4 * C) (32 * C ^ 2 / eps) < (M : Real) :=
    Classical.choose_spec hlarge
  refine Exists.intro (max M0 M) ?_
  intro n hn v hv
  have hR : (M : Real) <= PrimeFactorUnimodality.primeAt n := by
    have hidx : M <= n := (le_max_right M0 M).trans hn
    have hcast : (M : Real) <= n := by exact_mod_cast hidx
    have hp : (n : Real) <= PrimeFactorUnimodality.primeAt n := by
      exact_mod_cast PrimeFactorUnimodality.primeAt_strictMono.id_le n
    exact hcast.trans hp
  have hC : C < (PrimeFactorUnimodality.primeAt n : Real) / 4 := by
    have hh := le_max_left (4 * C) (32 * C ^ 2 / eps)
    linarith only [hh, hM, hR]
  have herrorM : 32 * C ^ 2 / eps < (M : Real) :=
    lt_of_le_of_lt (le_max_right (4 * C) (32 * C ^ 2 / eps)) hM
  have hp : (0 : Real) < PrimeFactorUnimodality.primeAt n := by
    exact_mod_cast (PrimeFactorUnimodality.prime_primeAt n).pos
  have hfrac : 32 * C ^ 2 / (PrimeFactorUnimodality.primeAt n : Real) < eps := by
    have hmul : (32 * C ^ 2 / (PrimeFactorUnimodality.primeAt n : Real)) *
        (PrimeFactorUnimodality.primeAt n : Real) <
          eps * (PrimeFactorUnimodality.primeAt n : Real) := by
      calc
        (32 * C ^ 2 / (PrimeFactorUnimodality.primeAt n : Real)) *
            (PrimeFactorUnimodality.primeAt n : Real) = 32 * C ^ 2 := by field_simp [hp.ne']
        _ = (32 * C ^ 2 / eps) * eps := by field_simp [heps.ne']
        _ < (M : Real) * eps := mul_lt_mul_of_pos_right herrorM heps
        _ <= (PrimeFactorUnimodality.primeAt n : Real) * eps :=
          mul_le_mul_of_nonneg_right hR heps.le
        _ = eps * (PrimeFactorUnimodality.primeAt n : Real) := mul_comm _ _
    by_contra hn
    have hle : eps <= 32 * C ^ 2 / (PrimeFactorUnimodality.primeAt n : Real) :=
      le_of_not_gt hn
    have hbad := mul_le_mul_of_nonneg_right hle hp.le
    exact (not_lt_of_ge hbad) hmul
  exact (prime_prefix_transport_uniform_error e t n C (ht n) hC0 hC
    (hM0 n ((le_max_left M0 M).trans hn)) v hv).trans_lt hfrac

end PrimeFactorOscillations.PrimeProfileRigidity

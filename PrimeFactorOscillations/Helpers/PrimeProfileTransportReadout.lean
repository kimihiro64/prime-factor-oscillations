/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/

import PrimeFactorOscillations.Helpers.PrimeProfileTransportParity

/-!
# Exact finite-accuracy readout of the even transport

A single probe budget with 32*C^2 below the boundary prime makes the
uniform transport error less than one. Every positive probe then has
the same unique nearest even integer, equal to the exact signed transport.
The boundary prime is at least three; the exceptional prime two remains
present in the original finite sums and is excluded only by localization.
-/

set_option autoImplicit false
set_option Elab.async false

noncomputable section

namespace PrimeFactorOscillations.PrimeProfileRigidity

/-- Every positive probe recovers one exact even transport under the same
finite accuracy threshold, without assuming a bounded sequence of costs. -/
theorem prime_prefix_exact_even_transport_readout
    (e : Equiv.Perm Nat) (t : Nat -> Real) (n : Nat) (C : Real)
    (ht : 0 < t n) (hC0 : 0 <= C)
    (hp3 : (3 : Real) <= PrimeFactorUnimodality.primeAt n)
    (hprecision : 32 * C ^ 2 < (PrimeFactorUnimodality.primeAt n : Real))
    (hcost : normalizedPrimePrefixDefect e t n <= C) :
    exists K : Nat,
      Finset.prefixDefect (fun j => (PrimeFactorUnimodality.primeAt j : Real))
        e (n + 1) = 2 * (K : Real) /\
      (forall v : Nat -> Real, 0 < v n ->
        abs (normalizedPrimePrefixDefect e v n - 2 * (K : Real)) < 1) /\
      (forall v : Nat -> Real, 0 < v n -> forall j : Nat,
        abs (normalizedPrimePrefixDefect e v n - 2 * (j : Real)) < 1 -> j = K) := by
  let r : Real := PrimeFactorUnimodality.primeAt n
  have hr3 : 3 <= r := hp3
  have hr : 0 < r := by linarith only [hr3]
  have hprec : 32 * C ^ 2 < r := hprecision
  have hbudget : C < r / 4 := by
    by_contra h
    have hCp : 0 <= 4 * C - r := by linarith only [le_of_not_gt h]
    have hm : 0 <= (4 * C - r) * (4 * C + r) :=
      mul_nonneg hCp (by positivity)
    have hrSq : 0 <= r * (r - 3) :=
      mul_nonneg hr.le (sub_nonneg.mpr hr3)
    nlinarith only [hm, hrSq, hprec, hr3]
  have hsmall : 2 < r - C := by linarith only [hbudget, hr3]
  have heven := prime_prefix_transport_even_of_cost_le e t n C ht hC0
    hbudget hcost hsmall
  let K := Classical.choose heven
  have hK : Finset.prefixDefect (fun j => (PrimeFactorUnimodality.primeAt j : Real))
      e (n + 1) = 2 * (K : Real) := Classical.choose_spec heven
  have hcancel : 32 * C ^ 2 / r * r = 32 * C ^ 2 := by field_simp [hr.ne']
  have herr : 32 * C ^ 2 / r < 1 := by
    by_contra h
    have hm := mul_le_mul_of_nonneg_right (le_of_not_gt h) hr.le
    rw [hcancel, one_mul] at hm
    exact (not_le_of_gt hprec) hm
  have hread : forall v : Nat -> Real, 0 < v n ->
      abs (normalizedPrimePrefixDefect e v n - 2 * (K : Real)) < 1 := by
    intro v hv
    have he := prime_prefix_transport_uniform_error e t n C ht hC0 hbudget hcost v hv
    rw [hK] at he
    exact he.trans_lt herr
  refine Exists.intro K (And.intro hK (And.intro hread ?_))
  intro v hv j hj
  have hKr := abs_lt.mp (hread v hv)
  have hjr := abs_lt.mp hj
  have hjK : (j : Real) < (K : Real) + 1 := by linarith only [hjr.1, hKr.2]
  have hKj : (K : Real) < (j : Real) + 1 := by linarith only [hKr.1, hjr.2]
  have hjKn : j < K + 1 := by exact_mod_cast hjK
  have hKjn : K < j + 1 := by exact_mod_cast hKj
  omega

end PrimeFactorOscillations.PrimeProfileRigidity

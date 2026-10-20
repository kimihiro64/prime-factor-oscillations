/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/

import PrimeFactorOscillations.Helpers.PrimeCountingLocation
import PrimeFactorOscillations.Helpers.PrimePrefixCutoffBracket

/-!
# Fixed-shift ratios of enumerated primes

The existing unconditional theta PNT and exact consecutive-prime prefix
identity give adjacent prime ratios tending to one. Finite products give
every fixed index shift. The consumer is prime-labelled profile rigidity:
matching reciprocal tails must have the same leading scale.
-/

set_option autoImplicit false
set_option Elab.async false

noncomputable section

namespace PrimeFactorOscillations

open Filter

/-- The inclusive old prime prefix ends just before its successor prime. -/
theorem primeProfilePrefixSet_before_next_eq (i : Nat) :
    primeProfilePrefixSet (PrimeFactorUnimodality.primeAt (i + 1) - 1) =
      primeProfilePrefixSet (PrimeFactorUnimodality.primeAt i) := by
  classical
  rw [primeProfilePrefixSet_next_prime]
  apply Finset.ext
  intro a
  have hmem : Membership.mem
      (@insert Nat.Primes (Finset Nat.Primes) inferInstance
        (Subtype.mk (PrimeFactorUnimodality.primeAt i)
          (PrimeFactorUnimodality.prime_primeAt i))
        (primeProfilePrefixSet (PrimeFactorUnimodality.primeAt i - 1))) a <->
      a = (Subtype.mk (PrimeFactorUnimodality.primeAt i)
        (PrimeFactorUnimodality.prime_primeAt i) : Nat.Primes) \/
      Membership.mem (primeProfilePrefixSet (PrimeFactorUnimodality.primeAt i - 1)) a :=
    Finset.mem_insert
  apply hmem.trans
  simp only [mem_primeProfilePrefixSet]
  constructor
  . intro h
    cases h with
    | inl h =>
      have hv := congrArg Subtype.val h
      change (a : Nat) = PrimeFactorUnimodality.primeAt i at hv
      omega
    | inr h => omega
  . intro h
    by_cases heq : (a : Nat) = PrimeFactorUnimodality.primeAt i
    . exact Or.inl (Subtype.ext heq)
    . exact Or.inr (by omega)

/-- No prime lies between an enumerated prime and the predecessor of the next. -/
theorem theta_before_next_prime_eq (i : Nat) :
    Chebyshev.theta ((PrimeFactorUnimodality.primeAt (i + 1) - 1 : Nat) : Real) =
      Chebyshev.theta (PrimeFactorUnimodality.primeAt i : Real) := by
  classical
  unfold Chebyshev.theta
  simp only [Nat.floor_natCast]
  apply Finset.sum_congr
  . apply Finset.ext
    intro r
    simp only [Finset.mem_filter, Finset.mem_Ioc]
    constructor
    . intro h
      let a : Nat.Primes := Subtype.mk r h.2
      have hm : Membership.mem
          (primeProfilePrefixSet (PrimeFactorUnimodality.primeAt (i + 1) - 1)) a :=
        (mem_primeProfilePrefixSet a _).mpr h.1.2
      rw [primeProfilePrefixSet_before_next_eq] at hm
      exact And.intro
        (And.intro h.1.1 ((mem_primeProfilePrefixSet a _).mp hm)) h.2
    . intro h
      have hpq : PrimeFactorUnimodality.primeAt i <
          PrimeFactorUnimodality.primeAt (i + 1) :=
        PrimeFactorUnimodality.primeAt_strictMono (Nat.lt_succ_self i)
      exact And.intro (And.intro h.1.1 (by omega)) h.2
  . intro r hr
    rfl

/-- Unconditionally, adjacent enumerated primes have ratio tending to one. -/
theorem tendsto_primeAt_succ_div :
    Tendsto (fun i : Nat =>
      (PrimeFactorUnimodality.primeAt (i + 1) : Real) /
        (PrimeFactorUnimodality.primeAt i : Real)) atTop (nhds 1) := by
  have hp : Tendsto PrimeFactorUnimodality.primeAt atTop atTop :=
    PrimeFactorUnimodality.primeAt_strictMono.tendsto_atTop
  have hq : Tendsto (fun i : Nat => PrimeFactorUnimodality.primeAt (i + 1))
      atTop atTop := by
    apply StrictMono.tendsto_atTop
    intro i j hij
    exact PrimeFactorUnimodality.primeAt_strictMono (Nat.add_lt_add_right hij 1)
  have hP := tendsto_primeProfile_theta_ratio.comp hp
  have hQ : Tendsto (fun i : Nat =>
      Chebyshev.theta (PrimeFactorUnimodality.primeAt i : Real) /
        (PrimeFactorUnimodality.primeAt (i + 1) : Real)) atTop (nhds 1) := by
    apply (tendsto_thetaPrefix_div_endpoint.comp hq).congr'
    exact Eventually.of_forall (fun i => by
      simp only [Function.comp_def, theta_before_next_prime_eq])
  have hquot := hP.div hQ (by norm_num : Not ((1 : Real) = 0))
  apply (show Tendsto (fun i : Nat =>
      (Chebyshev.theta (PrimeFactorUnimodality.primeAt i : Real) /
        (PrimeFactorUnimodality.primeAt i : Real)) /
      (Chebyshev.theta (PrimeFactorUnimodality.primeAt i : Real) /
        (PrimeFactorUnimodality.primeAt (i + 1) : Real))) atTop (nhds 1) by
      simpa only [Function.comp_def, Pi.div_def, div_one] using hquot).congr'
  filter_upwards [hP.eventually (lt_mem_nhds (by norm_num : (0 : Real) < 1))] with i hi
  have hp0 : Not ((PrimeFactorUnimodality.primeAt i : Real) = 0) := by
    exact_mod_cast (PrimeFactorUnimodality.prime_primeAt i).ne_zero
  have hq0 : Not ((PrimeFactorUnimodality.primeAt (i + 1) : Real) = 0) := by
    exact_mod_cast (PrimeFactorUnimodality.prime_primeAt (i + 1)).ne_zero
  have ht0 : Not (Chebyshev.theta (PrimeFactorUnimodality.primeAt i : Real) = 0) := by
    intro hz
    simp only [Function.comp_def, hz, zero_div, lt_self_iff_false] at hi
  field_simp

/-- Every fixed forward prime-index shift has asymptotic ratio one. -/
theorem tendsto_primeAt_add_div (k : Nat) :
    Tendsto (fun n : Nat =>
      (PrimeFactorUnimodality.primeAt (n + k) : Real) /
        (PrimeFactorUnimodality.primeAt n : Real)) atTop (nhds 1) := by
  induction k with
  | zero =>
    apply tendsto_const_nhds.congr'
    exact Eventually.of_forall (fun n => by
      have hp0 : Not ((PrimeFactorUnimodality.primeAt n : Real) = 0) := by
        exact_mod_cast (PrimeFactorUnimodality.prime_primeAt n).ne_zero
      simp only [Nat.add_zero, div_self hp0])
  | succ k ih =>
    have hshift : Tendsto (fun n : Nat => n + k) atTop atTop := by
      apply StrictMono.tendsto_atTop
      intro i j hij
      exact Nat.add_lt_add_right hij k
    have hprod := (tendsto_primeAt_succ_div.comp hshift).mul ih
    apply (show Tendsto (fun n : Nat =>
        ((PrimeFactorUnimodality.primeAt ((n + k) + 1) : Real) /
          (PrimeFactorUnimodality.primeAt (n + k) : Real)) *
        ((PrimeFactorUnimodality.primeAt (n + k) : Real) /
          (PrimeFactorUnimodality.primeAt n : Real))) atTop (nhds 1) by
        simpa only [Function.comp_def, mul_one] using hprod).congr'
    exact Eventually.of_forall (fun n => by
      have hp0 : Not ((PrimeFactorUnimodality.primeAt n : Real) = 0) := by
        exact_mod_cast (PrimeFactorUnimodality.prime_primeAt n).ne_zero
      have hk0 : Not ((PrimeFactorUnimodality.primeAt (n + k) : Real) = 0) := by
        exact_mod_cast (PrimeFactorUnimodality.prime_primeAt (n + k)).ne_zero
      simp only [Nat.add_succ]
      field_simp)

/-- Two independently shifted prime enumerations have the same leading scale. -/
theorem tendsto_primeAt_shift_div_shift (a b : Nat) :
    Tendsto (fun n : Nat =>
      (PrimeFactorUnimodality.primeAt (n + b) : Real) /
        (PrimeFactorUnimodality.primeAt (n + a) : Real)) atTop (nhds 1) := by
  have hquot := (tendsto_primeAt_add_div b).div (tendsto_primeAt_add_div a)
    (by norm_num : Not ((1 : Real) = 0))
  apply (show Tendsto (fun n : Nat =>
      ((PrimeFactorUnimodality.primeAt (n + b) : Real) /
        (PrimeFactorUnimodality.primeAt n : Real)) /
      ((PrimeFactorUnimodality.primeAt (n + a) : Real) /
        (PrimeFactorUnimodality.primeAt n : Real))) atTop (nhds 1) by
      simpa only [Pi.div_def, div_one] using hquot).congr'
  exact Eventually.of_forall (fun n => by
    have hp0 : Not ((PrimeFactorUnimodality.primeAt n : Real) = 0) := by
      exact_mod_cast (PrimeFactorUnimodality.prime_primeAt n).ne_zero
    have ha0 : Not ((PrimeFactorUnimodality.primeAt (n + a) : Real) = 0) := by
      exact_mod_cast (PrimeFactorUnimodality.prime_primeAt (n + a)).ne_zero
    have hb0 : Not ((PrimeFactorUnimodality.primeAt (n + b) : Real) = 0) := by
      exact_mod_cast (PrimeFactorUnimodality.prime_primeAt (n + b)).ne_zero
    field_simp)

end PrimeFactorOscillations

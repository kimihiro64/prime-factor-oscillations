/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/

import PrimeFactorOscillations.Helpers.PrimeProfileQuantization

/-!
# Uniform finite-or-infinite distortion dichotomy

A bounded probe at one cutoff bounds every other positive probe by twelve
times its budget once the boundary prime exceeds four times that budget.
Consequently unbounded unit-probe cost has witnesses shared by all probes.
Together with quantization this classifies every fixed prime permutation.
-/

set_option autoImplicit false
set_option Elab.async false

noncomputable section

namespace PrimeFactorOscillations.PrimeProfileRigidity

theorem prime_prefix_all_probes_le_twelve_mul_cost
    (e : Equiv.Perm Nat) (t : Nat -> Real) (n : Nat) (C : Real)
    (ht : 0 < t n) (hC0 : 0 <= C)
    (hC : C < (PrimeFactorUnimodality.primeAt n : Real) / 4)
    (hcost : normalizedPrimePrefixDefect e t n <= C)
    (v : Nat -> Real) (hv : 0 < v n) :
    normalizedPrimePrefixDefect e v n <= 12 * C := by
  let r : Real := PrimeFactorUnimodality.primeAt n
  let S : Real := Finset.prefixDefect
    (fun j => (PrimeFactorUnimodality.primeAt j : Real)) e (n + 1)
  have hr : 0 < r := by
    dsimp only [r]
    exact_mod_cast (PrimeFactorUnimodality.prime_primeAt n).pos
  have hbudget : 4 * C < r := by linarith only [hC]
  have hs : S <= 4 * C :=
    prime_prefix_transport_le_four_mul_cost e t n C ht hC0 hC hcost
  have he : normalizedPrimePrefixDefect e v n - S <= 32 * C ^ 2 / r :=
    (abs_le.mp (prime_prefix_transport_uniform_error e t n C ht hC0 hC hcost v hv)).2
  have hproduct : 0 <= C * (r - 4 * C) :=
    mul_nonneg hC0 (sub_nonneg.mpr hbudget.le)
  have herr : 32 * C ^ 2 / r <= 8 * C := by
    have hm : 32 * C ^ 2 <= (8 * C) * r := by nlinarith only [hproduct]
    have hd := div_le_div_of_nonneg_right hm hr.le
    have heq : (8 * C) * r / r = 8 * C := by field_simp [hr.ne']
    rw [heq] at hd
    exact hd
  linarith only [hs, he, herr]

/-- One unbounded fixed probe forces arbitrarily late lower witnesses
that hold simultaneously for every positive probe. -/
theorem uniformly_unbounded_of_unit_probe_unbounded
    (e : Equiv.Perm Nat)
    (hunbounded : Not (exists C : Real, 0 <= C /\
      exists M : Nat, forall n : Nat, M <= n ->
        normalizedPrimePrefixDefect e (fun _ => 1) n <= C)) :
    forall C : Real, forall N : Nat, exists n : Nat, N <= n /\
      forall v : Nat -> Real, 0 < v n ->
        C < normalizedPrimePrefixDefect e v n := by
  intro C N
  let A : Real := max C 0
  have hA : 0 <= A := le_max_right C 0
  have hCA : C <= A := le_max_left C 0
  have hP : exists P : Nat, 4 * A < (P : Real) := exists_nat_gt _
  let P := Classical.choose hP
  have hPgt : 4 * A < (P : Real) := Classical.choose_spec hP
  have hw : exists n : Nat, max N P <= n /\
      12 * A < normalizedPrimePrefixDefect e (fun _ => 1) n := by
    by_contra h
    apply hunbounded
    refine Exists.intro (12 * A) (And.intro (by positivity) ?_)
    refine Exists.intro (max N P) ?_
    intro n hn
    apply le_of_not_gt
    intro hd
    exact h (Exists.intro n (And.intro hn hd))
  let n := Classical.choose hw
  have hn : max N P <= n /\
      12 * A < normalizedPrimePrefixDefect e (fun _ => 1) n :=
    Classical.choose_spec hw
  have hPn : P <= n := (le_max_right N P).trans hn.1
  have hpr : (P : Real) <= (PrimeFactorUnimodality.primeAt n : Real) := by
    exact_mod_cast hPn.trans (PrimeFactorUnimodality.primeAt_strictMono.id_le n)
  have hbudget : A < (PrimeFactorUnimodality.primeAt n : Real) / 4 := by
    linarith only [hPgt, hpr]
  refine Exists.intro n (And.intro ((le_max_left N P).trans hn.1) ?_)
  intro v hv
  apply lt_of_not_ge
  intro hsmall
  have hb := prime_prefix_all_probes_le_twelve_mul_cost e v n A hv hA hbudget
    (hsmall.trans hCA) (fun _ => 1) (by norm_num)
  exact (not_le_of_gt hn.2) hb

/-- Either every positive probe has one common even envelope, or arbitrarily
late cutoffs exceed every prescribed level for all positive probes at once. -/
theorem prime_profile_uniform_distortion_dichotomy (e : Equiv.Perm Nat) :
    (exists K : Nat,
      (forall eps : Real, 0 < eps -> exists M : Nat,
        forall n : Nat, M <= n -> forall v : Nat -> Real, 0 < v n ->
          normalizedPrimePrefixDefect e v n <= 2 * (K : Real) + eps) /\
      (forall eps : Real, 0 < eps -> forall N : Nat,
        exists n : Nat, N <= n /\
          forall v : Nat -> Real, 0 < v n ->
            2 * (K : Real) - eps <= normalizedPrimePrefixDefect e v n)) \/
    (forall C : Real, forall N : Nat, exists n : Nat, N <= n /\
      forall v : Nat -> Real, 0 < v n ->
        C < normalizedPrimePrefixDefect e v n) := by
  classical
  by_cases hb : exists C : Real, 0 <= C /\
      exists M : Nat, forall n : Nat, M <= n ->
        normalizedPrimePrefixDefect e (fun _ => 1) n <= C
  . let C := Classical.choose hb
    have hC : 0 <= C /\ exists M : Nat, forall n : Nat, M <= n ->
        normalizedPrimePrefixDefect e (fun _ => 1) n <= C := Classical.choose_spec hb
    exact Or.inl (bounded_probe_quantized_uniform_envelope e (fun _ => 1)
      (fun _ => by norm_num) C hC.1 hC.2)
  . exact Or.inr (uniformly_unbounded_of_unit_probe_unbounded e hb)

end PrimeFactorOscillations.PrimeProfileRigidity

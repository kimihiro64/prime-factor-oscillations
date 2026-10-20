/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/

import PrimeFactorOscillations.Helpers.PrimeProfileCutoffRigidity

/-!
# Bounded profile cost localizes every transported prime

The complete signed finite prefix is split at its boundary reference.
Every retained reference cost is nonnegative. A bounded total therefore
confines every entering and leaving prime, independently of the probe.
-/

set_option autoImplicit false
set_option Elab.async false

noncomputable section

namespace PrimeFactorOscillations.PrimeProfileRigidity

theorem normalized_reference_costs_le_prefixDefect
    (e : Equiv.Perm Nat) (t : Nat -> Real) (n : Nat) (ht : 0 < t n) :
    (forall j, Membership.mem
      ((Finset.range (n + 1)).image e \ Finset.range (n + 1)) j ->
      (PrimeFactorUnimodality.primeAt n : Real) ^ 2 *
        ((PrimeFactorUnimodality.primeAt n : Real) + t n) / (t n) ^ 2 *
        Real.pairLogDefect (t n) (PrimeFactorUnimodality.primeAt n : Real)
          (PrimeFactorUnimodality.primeAt j : Real) <= normalizedPrimePrefixDefect e t n) /\
    (forall j, Membership.mem
      (Finset.range (n + 1) \ (Finset.range (n + 1)).image e) j ->
      (PrimeFactorUnimodality.primeAt n : Real) ^ 2 *
        ((PrimeFactorUnimodality.primeAt n : Real) + t n) / (t n) ^ 2 *
        Real.pairLogDefect (t n) (PrimeFactorUnimodality.primeAt j : Real)
          (PrimeFactorUnimodality.primeAt n : Real) <= normalizedPrimePrefixDefect e t n) := by
  let s := (Finset.range (n + 1)).image e
  let u := Finset.range (n + 1)
  have hc : s.card = u.card := Finset.card_image_iff.mpr
    (fun _ _ _ _ h => e.injective h)
  have hs : forall j, Membership.mem (s \ u) j ->
      primeLogWeight (t n) n <= primeLogWeight (t n) j := by
    intro j hj
    have hn := (Finset.mem_sdiff.mp hj).2
    change Not (Membership.mem (Finset.range (n + 1)) j) at hn
    rw [Finset.mem_range] at hn
    exact (primeLogWeight_strictMono _ ht).monotone (by omega)
  have hu : forall j, Membership.mem (u \ s) j ->
      primeLogWeight (t n) j <= primeLogWeight (t n) n := by
    intro j hj
    have hn := (Finset.mem_sdiff.mp hj).1
    change Membership.mem (Finset.range (n + 1)) j at hn
    rw [Finset.mem_range] at hn
    exact (primeLogWeight_strictMono _ ht).monotone (by omega)
  have hp : (0 : Real) < PrimeFactorUnimodality.primeAt n := by
    exact_mod_cast (PrimeFactorUnimodality.prime_primeAt n).pos
  have hnorm : 0 <= (PrimeFactorUnimodality.primeAt n : Real) ^ 2 *
      ((PrimeFactorUnimodality.primeAt n : Real) + t n) / (t n) ^ 2 := by positivity
  constructor
  . intro j hj
    have hb := Finset.incoming_reference_le_sum_sub_sum s u
      (primeLogWeight (t n)) (primeLogWeight (t n) n) hc hs hu j hj
    change _ <= ((Finset.range (n + 1)).image e).sum (primeLogWeight (t n)) -
      (Finset.range (n + 1)).sum (primeLogWeight (t n)) at hb
    rw [Finset.sum_image (fun _ _ _ _ h => e.injective h)] at hb
    have hm := mul_le_mul_of_nonneg_left hb hnorm
    simpa only [Real.pairLogDefect, primeLogWeight,
      normalizedPrimePrefixDefect, Finset.prefixDefect] using hm
  . intro j hj
    have hb := Finset.outgoing_reference_le_sum_sub_sum s u
      (primeLogWeight (t n)) (primeLogWeight (t n) n) hc hs hu j hj
    change _ <= ((Finset.range (n + 1)).image e).sum (primeLogWeight (t n)) -
      (Finset.range (n + 1)).sum (primeLogWeight (t n)) at hb
    rw [Finset.sum_image (fun _ _ _ _ h => e.injective h)] at hb
    have hm := mul_le_mul_of_nonneg_left hb hnorm
    simpa only [Real.pairLogDefect, primeLogWeight,
      normalizedPrimePrefixDefect, Finset.prefixDefect] using hm

/-- No far coordinate can hide in a bounded full signed prefix cost. -/
theorem prime_prefix_coordinates_localized_of_cost_le
    (e : Equiv.Perm Nat) (t : Nat -> Real) (n : Nat) (C : Real)
    (ht : 0 < t n) (hC : C < (PrimeFactorUnimodality.primeAt n : Real) / 4)
    (hcost : normalizedPrimePrefixDefect e t n <= C) :
    (forall j, Membership.mem
      ((Finset.range (n + 1)).image e \ Finset.range (n + 1)) j ->
      (PrimeFactorUnimodality.primeAt j : Real) -
        PrimeFactorUnimodality.primeAt n <= 4 * C) /\
    (forall j, Membership.mem
      (Finset.range (n + 1) \ (Finset.range (n + 1)).image e) j ->
      (PrimeFactorUnimodality.primeAt n : Real) -
        PrimeFactorUnimodality.primeAt j <= C) := by
  have hb := normalized_reference_costs_le_prefixDefect e t n ht
  have hp : (0 : Real) < PrimeFactorUnimodality.primeAt n := by
    exact_mod_cast (PrimeFactorUnimodality.prime_primeAt n).pos
  constructor
  . intro j hj
    have hn := (Finset.mem_sdiff.mp hj).2
    rw [Finset.mem_range] at hn
    have hidx : n <= j := by omega
    have hpq : (PrimeFactorUnimodality.primeAt n : Real) <=
        PrimeFactorUnimodality.primeAt j := by
      exact_mod_cast PrimeFactorUnimodality.primeAt_strictMono.monotone hidx
    exact (Real.incoming_gap_localization_of_normalized_pairLogDefect_le
      (t n) (PrimeFactorUnimodality.primeAt n : Real)
      (PrimeFactorUnimodality.primeAt j : Real) C ht hp hpq hC
      ((hb.1 j hj).trans hcost)).2
  . intro j hj
    have hn := Finset.mem_range.mp (Finset.mem_sdiff.mp hj).1
    have hidx : j <= n := by omega
    have hpj : (0 : Real) < PrimeFactorUnimodality.primeAt j := by
      exact_mod_cast (PrimeFactorUnimodality.prime_primeAt j).pos
    have hpq : (PrimeFactorUnimodality.primeAt j : Real) <=
        PrimeFactorUnimodality.primeAt n := by
      exact_mod_cast PrimeFactorUnimodality.primeAt_strictMono.monotone hidx
    exact (Real.reference_gap_le_normalized_pairLogDefect (t n)
      (PrimeFactorUnimodality.primeAt j : Real)
      (PrimeFactorUnimodality.primeAt n : Real) ht hpj hpq).trans
      ((hb.2 j hj).trans hcost)

end PrimeFactorOscillations.PrimeProfileRigidity

/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/

import PrimeFactorOscillations.Helpers.PrimeProfilePrimeRatio
import PrimeFactorOscillations.Mathlib.Analysis.SpecialFunctions.Log.CompensatedReciprocalNormalization
import PrimeFactorOscillations.Mathlib.Combinatorics.FinitePrefixDisplacement

/-!
# Adaptive finite-cutoff rigidity of prime-coordinate permutations

The complete compensated logarithmic defect has a positive cost at each
displaced prefix. Vanishing normalized defect forces finite support, for
every independently chosen sequence of positive probes.
-/

set_option autoImplicit false
set_option Elab.async false

noncomputable section

open Filter
open scoped Topology

namespace PrimeFactorOscillations.PrimeProfileRigidity

def primeLogWeight (t : Real) (n : Nat) : Real :=
  Real.bernoulliLogProfile t (PrimeFactorUnimodality.primeAt n : Real)

def normalizedPrimePrefixDefect (e : Equiv.Perm Nat) (t : Nat -> Real)
    (n : Nat) : Real :=
  (PrimeFactorUnimodality.primeAt n : Real) ^ 2 *
      ((PrimeFactorUnimodality.primeAt n : Real) + t n) / (t n) ^ 2 *
    Finset.prefixDefect (primeLogWeight (t n)) e (n + 1)

theorem primeLogWeight_strictMono (t : Real) (ht : 0 < t) :
    StrictMono (primeLogWeight t) := by
  intro i j hij
  apply Real.bernoulliLogProfile_strictMonoOn_pos t ht
  . change (0 : Real) < PrimeFactorUnimodality.primeAt i
    exact_mod_cast (PrimeFactorUnimodality.prime_primeAt i).pos
  . change (0 : Real) < PrimeFactorUnimodality.primeAt j
    exact_mod_cast (PrimeFactorUnimodality.prime_primeAt j).pos
  . exact_mod_cast PrimeFactorUnimodality.primeAt_strictMono hij

/-- A normalized cutoff cost below a quarter recovers the whole prime prefix. -/
theorem prime_prefix_eq_of_normalized_defect_lt (e : Equiv.Perm Nat)
    (t : Nat -> Real) (n : Nat) (ht : 0 < t n)
    (hr : (PrimeFactorUnimodality.primeAt (n + 1) : Real) <=
      2 * (PrimeFactorUnimodality.primeAt n : Real))
    (hd : normalizedPrimePrefixDefect e t n < 1 / 4) :
    (Finset.range (n + 1)).image e = Finset.range (n + 1) := by
  have hp : (0 : Real) < PrimeFactorUnimodality.primeAt n := by
    exact_mod_cast (PrimeFactorUnimodality.prime_primeAt n).pos
  have hgNat : PrimeFactorUnimodality.primeAt n + 1 <=
      PrimeFactorUnimodality.primeAt (n + 1) :=
    PrimeFactorUnimodality.primeAt_strictMono (Nat.lt_succ_self n)
  have hg : (1 : Real) <= (PrimeFactorUnimodality.primeAt (n + 1) : Real) -
      (PrimeFactorUnimodality.primeAt n : Real) := by
    have hc : (PrimeFactorUnimodality.primeAt n : Real) + 1 <=
        (PrimeFactorUnimodality.primeAt (n + 1) : Real) := by exact_mod_cast hgNat
    linarith only [hc]
  have hb := Real.quarter_le_normalized_pairLogDefect (t n)
    (PrimeFactorUnimodality.primeAt n : Real)
    (PrimeFactorUnimodality.primeAt (n + 1) : Real) ht hp hg hr
  have hnorm : 0 < (PrimeFactorUnimodality.primeAt n : Real) ^ 2 *
      ((PrimeFactorUnimodality.primeAt n : Real) + t n) / (t n) ^ 2 := by positivity
  apply Finset.image_range_eq_of_prefixDefect_lt_gap
    (primeLogWeight (t n)) (primeLogWeight_strictMono _ ht) e n
  unfold normalizedPrimePrefixDefect at hd
  unfold Real.pairLogDefect at hb
  change 1 / 4 <= _ * (primeLogWeight (t n) (n + 1) - primeLogWeight (t n) n) at hb
  nlinarith only [hd, hb, hnorm]

/-- Vanishing adaptive cutoff cost is exactly a finite coordinate permutation. -/
theorem normalizedPrimePrefixDefect_tendsto_zero_iff (e : Equiv.Perm Nat)
    (t : Nat -> Real) (ht : forall n, 0 < t n) :
    Tendsto (normalizedPrimePrefixDefect e t) atTop (nhds 0) <->
      exists N : Nat, forall n, N <= n -> e n = n := by
  constructor
  . intro h
    have hsmall := h.eventually (gt_mem_nhds (by norm_num : (0 : Real) < 1 / 4))
    have hratio := tendsto_primeAt_succ_div.eventually
      (gt_mem_nhds (by norm_num : (1 : Real) < 2))
    have heq : Filter.Eventually (fun n : Nat =>
        (Finset.range (n + 1)).image e = Finset.range (n + 1)) atTop := by
      filter_upwards [hsmall, hratio] with n hn hr
      have hp : (0 : Real) < PrimeFactorUnimodality.primeAt n := by
        exact_mod_cast (PrimeFactorUnimodality.prime_primeAt n).pos
      have hmul := mul_lt_mul_of_pos_right hr hp
      have hid : (PrimeFactorUnimodality.primeAt (n + 1) : Real) /
          (PrimeFactorUnimodality.primeAt n : Real) *
          (PrimeFactorUnimodality.primeAt n : Real) =
          (PrimeFactorUnimodality.primeAt (n + 1) : Real) := by field_simp
      rw [hid] at hmul
      exact prime_prefix_eq_of_normalized_defect_lt e t n (ht n) hmul.le hn
    let N := Classical.choose (eventually_atTop.mp heq)
    have hN : forall n : Nat, N <= n ->
        (Finset.range (n + 1)).image e = Finset.range (n + 1) :=
      Classical.choose_spec (eventually_atTop.mp heq)
    refine Exists.intro (N + 1) ?_
    intro n hn
    have hm : N <= n - 1 := by omega
    have h0 : (Finset.range n).image e = Finset.range n := by
      have hpref := hN (n - 1) hm
      have he : n - 1 + 1 = n := by omega
      rw [he] at hpref
      exact hpref
    exact Finset.perm_apply_eq_of_image_range_eq e n h0 (hN n (by omega))
  . intro h
    let N := Classical.choose h
    have hN : forall n, N <= n -> e n = n := Classical.choose_spec h
    apply tendsto_const_nhds.congr'
    filter_upwards [eventually_ge_atTop N] with n hn
    have hpref := Finset.image_range_eq_of_fixed_tail e N (n + 1) hN (by omega)
    have hz := Finset.prefixDefect_eq_zero_of_image_range_eq (primeLogWeight (t n))
      e (n + 1) hpref
    simp only [normalizedPrimePrefixDefect, hz, mul_zero]

end PrimeFactorOscillations.PrimeProfileRigidity

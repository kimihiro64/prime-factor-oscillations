/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/

import PrimeFactorOscillations.Helpers.PrimeProfileCostLocalization
import PrimeFactorOscillations.Mathlib.Analysis.SpecialFunctions.Log.CompensatedReciprocalWindow

/-!
# The integrated reciprocal window on both retained prime supports

Common coordinates are excluded. Every retained ratio belongs to the same
rational interval at any positive probe with cost below the quarter-reference.
-/

set_option autoImplicit false
set_option Elab.async false

noncomputable section

namespace PrimeFactorOscillations.PrimeProfileRigidity

/-- Both retained supports lie in the window with characteristic root seven. -/
theorem prime_prefix_integrated_reciprocal_window
    (e : Equiv.Perm Nat) (t : Nat -> Real) (n : Nat) (C : Real)
    (ht : 0 < t n) (hC : C < (PrimeFactorUnimodality.primeAt n : Real) / 4)
    (hcost : normalizedPrimePrefixDefect e t n <= C) :
    (forall j, Membership.mem
      ((Finset.range (n + 1)).image e \ Finset.range (n + 1)) j ->
      (45 / 64 : Real) <= (PrimeFactorUnimodality.primeAt n : Real) /
        PrimeFactorUnimodality.primeAt j /\
      (PrimeFactorUnimodality.primeAt n : Real) /
        PrimeFactorUnimodality.primeAt j <= (5 / 4 : Real)) /\
    (forall j, Membership.mem
      (Finset.range (n + 1) \ (Finset.range (n + 1)).image e) j ->
      (45 / 64 : Real) <= (PrimeFactorUnimodality.primeAt n : Real) /
        PrimeFactorUnimodality.primeAt j /\
      (PrimeFactorUnimodality.primeAt n : Real) /
        PrimeFactorUnimodality.primeAt j <= (5 / 4 : Real)) := by
  have h := normalized_reference_costs_le_prefixDefect e t n ht
  have hr : (0 : Real) < PrimeFactorUnimodality.primeAt n := by
    exact_mod_cast (PrimeFactorUnimodality.prime_primeAt n).pos
  constructor
  . intro j hj
    have hn := (Finset.mem_sdiff.mp hj).2
    rw [Finset.mem_range] at hn
    have hidx : n <= j := by omega
    have hpr : (PrimeFactorUnimodality.primeAt n : Real) <=
        PrimeFactorUnimodality.primeAt j := by
      exact_mod_cast PrimeFactorUnimodality.primeAt_strictMono.monotone hidx
    have hp := hr.trans_le hpr
    have hlo := (Real.incoming_quarter_cost_reciprocal_window (t n)
      (PrimeFactorUnimodality.primeAt n : Real)
      (PrimeFactorUnimodality.primeAt j : Real) C ht hr hpr hC
      ((h.1 j hj).trans hcost)).2
    have hup : (PrimeFactorUnimodality.primeAt n : Real) /
        PrimeFactorUnimodality.primeAt j <= 1 := (div_le_one hp).mpr hpr
    exact And.intro hlo (hup.trans (by norm_num))
  . intro j hj
    have hn := Finset.mem_range.mp (Finset.mem_sdiff.mp hj).1
    have hidx : j <= n := by omega
    have hpr : (PrimeFactorUnimodality.primeAt j : Real) <=
        PrimeFactorUnimodality.primeAt n := by
      exact_mod_cast PrimeFactorUnimodality.primeAt_strictMono.monotone hidx
    have hp : (0 : Real) < PrimeFactorUnimodality.primeAt j := by
      exact_mod_cast (PrimeFactorUnimodality.prime_primeAt j).pos
    have hup := Real.outgoing_quarter_cost_reciprocal_window (t n)
      (PrimeFactorUnimodality.primeAt j : Real)
      (PrimeFactorUnimodality.primeAt n : Real) C ht hp hpr hC
      ((h.2 j hj).trans hcost)
    refine And.intro ?_ hup.le
    by_contra hnlo
    have hm := mul_lt_mul_of_pos_right (lt_of_not_ge hnlo) hp
    have hid : (PrimeFactorUnimodality.primeAt n : Real) /
        PrimeFactorUnimodality.primeAt j * PrimeFactorUnimodality.primeAt j =
        PrimeFactorUnimodality.primeAt n := by field_simp
    rw [hid] at hm
    nlinarith only [hm, hp, hpr]

end PrimeFactorOscillations.PrimeProfileRigidity

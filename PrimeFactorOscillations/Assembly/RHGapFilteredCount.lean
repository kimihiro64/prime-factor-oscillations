/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Assembly.AscentClockWindow
import PrimeFactorOscillations.Assembly.RHLogAscentCapacity
import PrimeFactorOscillations.Helpers.ReferenceEligibleCounts

/-!
# RH comparison with the count of actual reference-eligible gaps

The exact early/late split preserves the actual lower prime endpoints, the
real lower cutoff, the natural strict upper cutoff, and every actual gap.
The established unconditional reversal supply then forces a positive count
of reference-eligible endpoints under RH. This is a necessary comparison;
it supplies no independently improved prime-gap bound.
-/

set_option autoImplicit false
set_option Elab.async false

namespace PrimeFactorOscillations

theorem ordinary_reversal_count_reference_bound_of_RH
    (hRH : RiemannHypothesis) (a : Real) (ha : 0 < a) :
    exists K : Nat, 2 <= K /\ forall k : Nat, K <= k ->
      forall m : Nat, HasAtLeastReversals (ordinaryDensity k) m ->
      m <= Nat.primeCounting (Nat.floor (Real.exp (Real.exp (a * (k : Real))))) +
        ordinaryReferenceEligibleCount k (Real.exp (Real.exp (a * (k : Real))))
          (Nat.ceil (Real.exp (Real.exp ((k : Real) / 2))) + 1) := by
  choose Q hQ hgap using ordinary_ascent_reference_gap_bound_of_RH hRH
    (1 : Real) (max 1 (4 / a)) (by norm_num) (le_max_left _ _)
  choose K hK hwindow using ordinary_ascent_eventually_in_clock_window a ha Q
  refine Exists.intro K (And.intro hK ?_)
  intro k hk m hm
  apply reversal_count_le_reference_eligible (ordinaryDensity k) k m
    (Real.exp (Real.exp (a * (k : Real))))
    (Nat.ceil (Real.exp (Real.exp ((k : Real) / 2))) + 1) _ hm
  intro i hi hX
  have hw := hwindow k hk i hX hi
  refine And.intro hw.2.1 ?_
  exact hgap i hw.1 k hw.2.2.2.1 hw.2.2.2.2 hi

theorem ordinary_reference_eligible_supply_of_RH (hRH : RiemannHypothesis) :
    exists c : Real, 0 < c /\ forall a : Real, 0 < a -> a < c ->
      exists K : Nat, 2 <= K /\ forall k : Nat, K <= k ->
        0 < ordinaryReferenceEligibleCount k (Real.exp (Real.exp (a * (k : Real))))
          (Nat.ceil (Real.exp (Real.exp ((k : Real) / 2))) + 1) /\
        Real.exp (Real.exp (c * (k : Real))) - Real.exp (Real.exp (a * (k : Real))) <=
          (ordinaryReferenceEligibleCount k (Real.exp (Real.exp (a * (k : Real))))
            (Nat.ceil (Real.exp (Real.exp ((k : Real) / 2))) + 1) : Real) := by
  choose c K0 hc hK0 hsupply using ordinary_eventually_last_ascent_with_reversal_number
  refine Exists.intro c (And.intro hc ?_)
  intro a ha hac
  choose K1 hK1 hcount using ordinary_reversal_count_reference_bound_of_RH hRH a ha
  refine Exists.intro (max K0 K1) (And.intro (hK0.trans (le_max_left _ _)) ?_)
  intro k hk
  have hk0 : K0 <= k := (le_max_left _ _).trans hk
  have hk1 : K1 <= k := (le_max_right _ _).trans hk
  choose N i hN hlow hi hlast hNpi using hsupply k hk0
  have hb := hcount k hk1 N hN.1
  let X := Real.exp (Real.exp (a * (k : Real)))
  let C := ordinaryReferenceEligibleCount k X
    (Nat.ceil (Real.exp (Real.exp ((k : Real) / 2))) + 1)
  have hpiNat : Nat.primeCounting (Nat.floor X) <= Nat.floor X := by
    rw [<- Nat.primesLE_card_eq_primeCounting]
    have hs : (Nat.primesLE (Nat.floor X)).card <= (Finset.Icc 1 (Nat.floor X)).card := by
      apply Finset.card_le_card
      intro p hp
      have h := Nat.mem_primesLE.mp hp
      exact Finset.mem_Icc.mpr (And.intro h.2.one_lt.le h.1)
    simpa using hs
  have hpi : (Nat.primeCounting (Nat.floor X) : Real) <= X :=
    (show (Nat.primeCounting (Nat.floor X) : Real) <= (Nat.floor X : Real) by
      exact_mod_cast hpiNat).trans (Nat.floor_le (Real.exp_pos _).le)
  have hbR : (N : Real) <= (Nat.primeCounting (Nat.floor X) : Real) + (C : Real) := by
    exact_mod_cast hb
  have hbound : Real.exp (Real.exp (c * (k : Real))) - X <= (C : Real) := by
    linarith only [hlow, hpi, hbR]
  have hkR : (0 : Real) < k := by
    exact_mod_cast (show 0 < k by omega)
  have hXsmall : X < Real.exp (Real.exp (c * (k : Real))) :=
    Real.exp_lt_exp.mpr (Real.exp_lt_exp.mpr (mul_lt_mul_of_pos_right hac hkR))
  have hC : (0 : Real) < C := by linarith only [hbound, hXsmall]
  exact And.intro (by exact_mod_cast hC) hbound

end PrimeFactorOscillations

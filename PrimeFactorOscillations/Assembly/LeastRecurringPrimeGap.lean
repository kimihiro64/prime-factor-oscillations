/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/

import PrimeFactorOscillations.Assembly.PrimeProfileRigidity

/-!
# The least recurring adjacent prime gap

The established bounded-gap supply makes the recurrence predicate nonempty.
Its least threshold is an eventual gap floor, and its exact gap occurs at
arbitrarily large prime indices. No improvement of the bounded-gap input
is asserted.
-/

set_option autoImplicit false
set_option Elab.async false

noncomputable section

attribute [local instance] Classical.propDecidable

namespace PrimeFactorOscillations.PrimeProfileRigidity

def RecurrentPrimeGapAtMost (h : Nat) : Prop :=
  forall B : Nat, exists i : Nat, B <= PrimeFactorUnimodality.primeAt i /\
    PrimeFactorUnimodality.primeAt (i + 1) <= PrimeFactorUnimodality.primeAt i + h

theorem recurrentPrimeGapAtMost_600 : RecurrentPrimeGapAtMost 600 := by
  classical
  intro B
  have hpairs := exists_bounded_prime_pair_above B
  let p := Classical.choose hpairs
  let q := Classical.choose (Classical.choose_spec hpairs)
  have hd : B < p /\ Nat.Prime p /\ Nat.Prime q /\ p < q /\ q <= p + 600 :=
    Classical.choose_spec (Classical.choose_spec hpairs)
  have hp : Membership.mem ((Finset.Icc p (p + 600)).filter Nat.Prime) p :=
    Finset.mem_filter.mpr (And.intro
      (Finset.mem_Icc.mpr (And.intro (le_refl p) (by omega))) hd.2.1)
  have hq : Membership.mem ((Finset.Icc p (p + 600)).filter Nat.Prime) q :=
    Finset.mem_filter.mpr (And.intro
      (Finset.mem_Icc.mpr (And.intro hd.2.2.2.1.le hd.2.2.2.2)) hd.2.2.1)
  have hcard : 2 <= ((Finset.Icc p (p + 600)).filter Nat.Prime).card :=
    Finset.one_lt_card.mpr (Exists.intro p (And.intro hp
      (Exists.intro q (And.intro hq (ne_of_lt hd.2.2.2.1)))))
  have hx := PrimeFactorUnimodality.exists_adjacent_primes_in_window hcard
  let i := Classical.choose hx
  have hi : p <= PrimeFactorUnimodality.primeAt i /\
      PrimeFactorUnimodality.primeAt (i + 1) <= p + 600 := Classical.choose_spec hx
  exact Exists.intro i (And.intro (hd.1.le.trans hi.1)
    (hi.2.trans (Nat.add_le_add_right hi.1 600)))

def leastRecurringPrimeGap : Nat :=
  Nat.find (Exists.intro 600 recurrentPrimeGapAtMost_600)

theorem leastRecurringPrimeGap_recurrent :
    RecurrentPrimeGapAtMost leastRecurringPrimeGap :=
  Nat.find_spec (Exists.intro 600 recurrentPrimeGapAtMost_600)

theorem leastRecurringPrimeGap_le_600 : leastRecurringPrimeGap <= 600 :=
  Nat.find_min' (Exists.intro 600 recurrentPrimeGapAtMost_600) recurrentPrimeGapAtMost_600

theorem two_le_adjacent_prime_gap (i : Nat)
    (hp : 3 <= PrimeFactorUnimodality.primeAt i) :
    PrimeFactorUnimodality.primeAt i + 2 <= PrimeFactorUnimodality.primeAt (i + 1) := by
  have hpi := (PrimeFactorUnimodality.prime_primeAt i).eq_two_or_odd
  have hqi := (PrimeFactorUnimodality.prime_primeAt (i + 1)).eq_two_or_odd
  have hlt : PrimeFactorUnimodality.primeAt i <
      PrimeFactorUnimodality.primeAt (i + 1) :=
    PrimeFactorUnimodality.primeAt_strictMono (Nat.lt_succ_self i)
  omega

theorem two_le_leastRecurringPrimeGap : 2 <= leastRecurringPrimeGap := by
  let i := Classical.choose (leastRecurringPrimeGap_recurrent 3)
  have hi : 3 <= PrimeFactorUnimodality.primeAt i /\
      PrimeFactorUnimodality.primeAt (i + 1) <=
        PrimeFactorUnimodality.primeAt i + leastRecurringPrimeGap :=
    Classical.choose_spec (leastRecurringPrimeGap_recurrent 3)
  have htwo := two_le_adjacent_prime_gap i hi.1
  omega

/-- Minimal recurrence has an actual eventual lower gap, not only a liminf. -/
theorem leastRecurringPrimeGap_eventual_floor :
    exists Q : Nat, forall i : Nat, Q <= PrimeFactorUnimodality.primeAt i ->
      PrimeFactorUnimodality.primeAt i + leastRecurringPrimeGap <=
        PrimeFactorUnimodality.primeAt (i + 1) := by
  classical
  have hpos := two_le_leastRecurringPrimeGap
  have hsmall : Not (RecurrentPrimeGapAtMost (leastRecurringPrimeGap - 1)) :=
    Nat.find_min (Exists.intro 600 recurrentPrimeGapAtMost_600) (by
      change leastRecurringPrimeGap - 1 < leastRecurringPrimeGap
      omega)
  by_contra hn
  apply hsmall
  intro B
  by_contra hnone
  apply hn
  refine Exists.intro B ?_
  intro i hBi
  have hnot : Not (PrimeFactorUnimodality.primeAt (i + 1) <=
      PrimeFactorUnimodality.primeAt i + (leastRecurringPrimeGap - 1)) := by
    intro hle
    exact hnone (Exists.intro i (And.intro hBi hle))
  omega

/-- The least threshold itself occurs exactly beyond every index cutoff. -/
theorem leastRecurringPrimeGap_exact_above (N : Nat) :
    exists i : Nat, N <= i /\ PrimeFactorUnimodality.primeAt (i + 1) =
      PrimeFactorUnimodality.primeAt i + leastRecurringPrimeGap := by
  let Q := Classical.choose leastRecurringPrimeGap_eventual_floor
  have hQ : forall i : Nat, Q <= PrimeFactorUnimodality.primeAt i ->
      PrimeFactorUnimodality.primeAt i + leastRecurringPrimeGap <=
        PrimeFactorUnimodality.primeAt (i + 1) :=
    Classical.choose_spec leastRecurringPrimeGap_eventual_floor
  let B := max Q (PrimeFactorUnimodality.primeAt N)
  let i := Classical.choose (leastRecurringPrimeGap_recurrent B)
  have hi : B <= PrimeFactorUnimodality.primeAt i /\
      PrimeFactorUnimodality.primeAt (i + 1) <=
        PrimeFactorUnimodality.primeAt i + leastRecurringPrimeGap :=
    Classical.choose_spec (leastRecurringPrimeGap_recurrent B)
  have hpi : PrimeFactorUnimodality.primeAt N <= PrimeFactorUnimodality.primeAt i :=
    (le_max_right Q _).trans hi.1
  have hNi : N <= i := by
    by_contra hn
    have hlt := PrimeFactorUnimodality.primeAt_strictMono (lt_of_not_ge hn)
    omega
  exact Exists.intro i (And.intro hNi
    (le_antisymm hi.2 (hQ i ((le_max_left Q _).trans hi.1))))

end PrimeFactorOscillations.PrimeProfileRigidity

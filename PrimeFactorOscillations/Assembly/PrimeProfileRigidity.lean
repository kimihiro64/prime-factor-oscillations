/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/

import PrimeFactorOscillations.Helpers.PrimeWindowPairs
import PrimeFactorOscillations.Mathlib.Analysis.SpecialFunctions.Log.CompensatedReciprocal
import PrimeFactorOscillations.Mathlib.NumberTheory.Primes.Translation
import PrimeFactorOscillations.Proof.PrimeClusters.WindowCount

/-!
# Bounded prime pairs for probability-profile swaps

The established bounded-gap supply gives arbitrarily high prime pairs of gap
at most 600. The imported scalar theorem retains the signed compensation.
-/

set_option autoImplicit false
set_option Elab.async false

open Filter
open scoped Topology

noncomputable section

namespace PrimeFactorOscillations.PrimeProfileRigidity

/-- The existing compiled bounded-gap supply produces arbitrarily high pairs. -/
theorem exists_bounded_prime_pair_above (B : Nat) :
    exists p q : Nat, B < p /\ Nat.Prime p /\ Nat.Prime q /\
      p < q /\ q <= p + 600 := by
  classical
  have hevent := PrimeGaps.eventually_many_prime_windows_600.and
    (eventually_ge_atTop (B + 1))
  let N := Classical.choose hevent.exists
  have hdata := Classical.choose_spec hevent.exists
  have hN : B + 1 <= N := hdata.2
  have hNpos : (0 : Real) < N := by exact_mod_cast (show 0 < N by omega)
  have hcardR : (0 : Real) <
      (((Finset.Ioc N (2 * N)).filter (fun n =>
        2 <= ((Finset.Icc n (n + 600)).filter Nat.Prime).card)).card : Real) :=
    (Real.rpow_pos_of_pos hNpos _).trans_le hdata.1
  have hcard : 0 <
      ((Finset.Ioc N (2 * N)).filter (fun n =>
        2 <= ((Finset.Icc n (n + 600)).filter Nat.Prime).card)).card := by
    exact_mod_cast hcardR
  let n := Classical.choose (Finset.card_pos.mp hcard)
  have hn := Finset.mem_filter.mp (Classical.choose_spec (Finset.card_pos.mp hcard))
  have hnN : N < n := (Finset.mem_Ioc.mp hn.1).1
  let hi := PrimeFactorUnimodality.exists_adjacent_primes_in_window hn.2
  let i := Classical.choose hi
  have hiData : n <= PrimeFactorUnimodality.primeAt i /\
      PrimeFactorUnimodality.primeAt (i + 1) <= n + 600 := Classical.choose_spec hi
  refine Exists.intro (PrimeFactorUnimodality.primeAt i)
    (Exists.intro (PrimeFactorUnimodality.primeAt (i + 1))
      (And.intro ?_ (And.intro (PrimeFactorUnimodality.prime_primeAt i)
        (And.intro (PrimeFactorUnimodality.prime_primeAt (i + 1))
          (And.intro ?_ ?_)))))
  . exact (lt_of_lt_of_le (Nat.lt_succ_self B) hN).trans (hnN.trans_le hiData.1)
  . exact PrimeFactorUnimodality.primeAt_strictMono (Nat.lt_succ_self i)
  . exact hiData.2.trans (Nat.add_le_add_right hiData.1 600)

end PrimeFactorOscillations.PrimeProfileRigidity

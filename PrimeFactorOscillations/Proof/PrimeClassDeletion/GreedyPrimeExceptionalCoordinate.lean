/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/

import PrimeFactorOscillations.Proof.PrimeClassDeletion.PrimeClassOddsExtraction

/-! # The actual greedy class contains the forced coordinate

Prime 2 is selected by the fixed greedy rule. Thus every cutoff at least 2
has exactly one forced affine endpoint coordinate, with its full survival
factor and the one-rank shift retained.
-/

set_option autoImplicit false
set_option Elab.async false

namespace PrimeFactorOscillations.PrimeClassDeletion

open PrimeFactorUnimodality
open PrimeFactorOscillations.PrimeClassSampling

theorem greedyPrimeClass_two : Membership.mem greedyPrimeClass 2 := by
  have hcount : Nat.count Nat.Prime 2 = 0 := by decide
  have hfirst := primeAt_count_prime 2 Nat.prime_two
  rw [hcount] at hfirst
  change And (Nat.Prime 2) (greedyPrimeIndices (Nat.count Nat.Prime 2))
  refine And.intro Nat.prime_two ?_
  rw [hcount]
  change 0 + Real.log (primeAt 0 : Real) <= (primeAt 0 : Real)
  rw [zero_add, hfirst]
  exact (Real.log_le_sub_one_of_pos (by norm_num)).trans (by norm_num)

theorem greedyPrimeClass_two_mem_prefix (X : Nat) (hX : 2 <= X) :
    Membership.mem (primeClassPrefix greedyPrimeClass X) 2 := by
  classical
  simpa only [primeClassPrefix, Finset.mem_filter, Finset.mem_Icc] using
    And.intro (And.intro (le_refl 2) hX)
      (And.intro Nat.prime_two greedyPrimeClass_two)

theorem greedyPrimeClass_two_mem_real_prefix (x : Real) (hx : 2 <= x) :
    Membership.mem (primeClassPrefix greedyPrimeClass (Nat.floor x)) 2 := by
  have hX : 2 <= Nat.floor x := Nat.le_floor hx
  exact greedyPrimeClass_two_mem_prefix (Nat.floor x) hX

theorem greedyPrimeClass_affine_endpoint_rank_shift (rho : Real) (hrho : 0 < rho)
    (x : Real) (hx : 2 <= x) :
    And (List.bernoulliOutcomeMass
      (primeClassCoordinates greedyPrimeClass (affinePrimeProbability rho (-2))
        (Nat.floor x)) 0 = 0)
    (And (forall r : Nat, List.bernoulliOutcomeMass
        (primeClassCoordinates greedyPrimeClass (affinePrimeProbability rho (-2))
          (Nat.floor x)) (r + 1) =
      List.bernoulliOutcomeMass
        (primeClassCoordinates (removePrimeClass greedyPrimeClass 2)
          (affinePrimeProbability rho (-2)) (Nat.floor x)) r)
    (forall r : Nat, primeClassBernoulliTail greedyPrimeClass
        (affinePrimeProbability rho (-2)) (Nat.floor x) (r + 1) =
      primeClassBernoulliTail (removePrimeClass greedyPrimeClass 2)
        (affinePrimeProbability rho (-2)) (Nat.floor x) r)) :=
  affinePrimeEndpoint_rank_shift rho hrho greedyPrimeClass (Nat.floor x)
    (greedyPrimeClass_two_mem_real_prefix x hx)

theorem greedyPrimeClass_affine_endpoint_odds_formula (rho : Real) (hrho : 0 < rho)
    (x : Real) (hx : 2 <= x) (r : Nat) :
    List.bernoulliOutcomeMass
      (primeClassCoordinates greedyPrimeClass (affinePrimeProbability rho (-2))
        (Nat.floor x)) (r + 1) =
    (primeClassPrefix (removePrimeClass greedyPrimeClass 2) (Nat.floor x)).prod
      (fun p => 1 - affinePrimeProbability rho (-2) p) *
    ((primeClassPrefix (removePrimeClass greedyPrimeClass 2) (Nat.floor x)).prod
      (fun p => 1 + Polynomial.C (affinePrimeOdds rho (-2) p) * Polynomial.X)).coeff r :=
  affinePrimeEndpoint_shifted_odds_formula rho hrho greedyPrimeClass (Nat.floor x) r
    (greedyPrimeClass_two_mem_real_prefix x hx)

end PrimeFactorOscillations.PrimeClassDeletion

/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/

import PrimeFactorOscillations.Proof.PrimeClassDeletion.PrimeClassForcedCoordinate

/-! # Full actual odds extraction after removing the exceptional prime

The survival product is retained. At beta=-2 it is strictly positive only
after the forced coordinate is removed. Present and absent prime2 cases have
their exact different ranks; no endpoint coefficient-order extension is claimed.
-/

set_option autoImplicit false
set_option Elab.async false

namespace PrimeFactorOscillations.PrimeClassDeletion

open PrimeFactorOscillations.PrimeClassSampling

theorem primeClassPrefix_remove_not_eq (P : Set Nat) (X q p : Nat)
    (hp : Membership.mem (primeClassPrefix (removePrimeClass P q) X) p) :
    Not (p = q) := by
  classical
  exact (Finset.mem_filter.mp hp).2.2.2

theorem primeClassBernoulliMass_eq_survival_esymm (P : Set Nat) (eta : Nat -> Real)
    (X : Nat) (hne : forall p, Membership.mem (primeClassPrefix P X) p -> Not (eta p = 1))
    (r : Nat) :
    List.bernoulliOutcomeMass (primeClassCoordinates P eta X) r =
      (primeClassPrefix P X).prod (fun p => 1 - eta p) *
        ((primeClassCoordinates P (fun p => eta p / (1 - eta p)) X : List Real) :
          Multiset Real).esymm r := by
  classical
  have hl : forall a : Real, List.Mem a (primeClassCoordinates P eta X) -> Not (a = 1) := by
    intro a ha
    choose k hk using (primeClassCoordinates_mem_iff P eta X a).mp ha
    have hs := primeClassRankValue_spec P X k hk.1
    have hp : Membership.mem (primeClassPrefix P X) (primeClassRankValue P k) := by
      simpa only [primeClassPrefix, Finset.mem_filter, Finset.mem_Icc] using
        And.intro (And.intro hs.1.two_le hs.2.2.1) (And.intro hs.1 hs.2.1)
    intro heq
    exact hne _ hp (hk.2.trans heq)
  rw [List.bernoulliOutcomeMass_eq, List.bernoulliMass_eq_survival_mul_esymm _ hl,
    primeClassCoordinates_map, primeClassCoordinates_prod, primeClassCoordinates_map]

theorem primeClassBernoulliMass_eq_survival_product_coeff
    (P : Set Nat) (eta : Nat -> Real) (X : Nat)
    (hne : forall p, Membership.mem (primeClassPrefix P X) p -> Not (eta p = 1))
    (r : Nat) :
    List.bernoulliOutcomeMass (primeClassCoordinates P eta X) r =
      (primeClassPrefix P X).prod (fun p => 1 - eta p) *
        ((primeClassPrefix P X).prod
          (fun p => 1 + Polynomial.C (eta p / (1 - eta p)) * Polynomial.X)).coeff r := by
  have h := primeClassBernoulliMass_eq_survival_esymm P eta X hne r
  rw [<- List.bernoulliOddsProduct_coeff, primeClassCoordinates_odds_product] at h
  exact h

theorem affinePrimeEndpoint_remaining_local (rho : Real) (hrho : 0 < rho)
    (P : Set Nat) (X p : Nat)
    (hp : Membership.mem (primeClassPrefix (removePrimeClass P 2) X) p) :
    And (0 < affinePrimeProbability rho (-2) p)
    (And (affinePrimeProbability rho (-2) p < 1)
    (And (0 < affinePrimeOdds rho (-2) p)
      (affinePrimeProbability rho (-2) p / (1 - affinePrimeProbability rho (-2) p) =
        affinePrimeOdds rho (-2) p))) := by
  have hprime := primeClassPrefix_prime (removePrimeClass P 2) X p hp
  have hp2 := hprime.two_le
  have hne := primeClassPrefix_remove_not_eq P X 2 p hp
  have hgt : 2 < p := by omega
  have hgtR : (2 : Real) < p := by exact_mod_cast hgt
  have hb : 0 < (p : Real) + -2 := by linarith only [hgtR]
  have hd : 0 < (p : Real) + -2 + rho := add_pos hb hrho
  have hunit := affinePrimeProbability_unit rho (-2) hrho (le_refl _) p hprime
  have hnot : Not (affinePrimeProbability rho (-2) p = 1) := by
    intro h
    exact hne ((affinePrimeProbability_endpoint_one_iff rho hrho p hprime).mp h)
  exact And.intro (div_pos hrho hd)
    (And.intro (lt_of_le_of_ne hunit.2 hnot)
      (And.intro (div_pos hrho hb) (affinePrimeProbability_odds rho (-2) hrho p hb)))

theorem affinePrimeEndpoint_survival_pos (rho : Real) (hrho : 0 < rho)
    (P : Set Nat) (X : Nat) :
    0 < (primeClassPrefix (removePrimeClass P 2) X).prod
      (fun p => 1 - affinePrimeProbability rho (-2) p) := by
  apply Finset.prod_pos
  intro p hp
  exact sub_pos.mpr (affinePrimeEndpoint_remaining_local rho hrho P X p hp).2.1

theorem affinePrimeEndpoint_removed_odds_formula (rho : Real) (hrho : 0 < rho)
    (P : Set Nat) (X r : Nat) :
    List.bernoulliOutcomeMass
      (primeClassCoordinates (removePrimeClass P 2) (affinePrimeProbability rho (-2)) X) r =
    (primeClassPrefix (removePrimeClass P 2) X).prod
      (fun p => 1 - affinePrimeProbability rho (-2) p) *
    ((primeClassPrefix (removePrimeClass P 2) X).prod
      (fun p => 1 + Polynomial.C (affinePrimeOdds rho (-2) p) * Polynomial.X)).coeff r := by
  have hne : forall p, Membership.mem (primeClassPrefix (removePrimeClass P 2) X) p ->
      Not (affinePrimeProbability rho (-2) p = 1) := by
    intro p hp
    exact ne_of_lt (affinePrimeEndpoint_remaining_local rho hrho P X p hp).2.1
  have h := primeClassBernoulliMass_eq_survival_product_coeff (removePrimeClass P 2)
    (affinePrimeProbability rho (-2)) X hne r
  have hpoly :
      (primeClassPrefix (removePrimeClass P 2) X).prod (fun p =>
        1 + Polynomial.C (affinePrimeProbability rho (-2) p /
          (1 - affinePrimeProbability rho (-2) p)) * Polynomial.X) =
      (primeClassPrefix (removePrimeClass P 2) X).prod (fun p =>
        1 + Polynomial.C (affinePrimeOdds rho (-2) p) * Polynomial.X) := by
    apply Finset.prod_congr rfl
    intro p hp
    rw [(affinePrimeEndpoint_remaining_local rho hrho P X p hp).2.2.2]
  rw [hpoly] at h
  exact h

theorem affinePrimeEndpoint_shifted_odds_formula (rho : Real) (hrho : 0 < rho)
    (P : Set Nat) (X r : Nat) (h2 : Membership.mem (primeClassPrefix P X) 2) :
    List.bernoulliOutcomeMass
      (primeClassCoordinates P (affinePrimeProbability rho (-2)) X) (r + 1) =
    (primeClassPrefix (removePrimeClass P 2) X).prod
      (fun p => 1 - affinePrimeProbability rho (-2) p) *
    ((primeClassPrefix (removePrimeClass P 2) X).prod
      (fun p => 1 + Polynomial.C (affinePrimeOdds rho (-2) p) * Polynomial.X)).coeff r := by
  exact (primeClass_forced_mass_succ P (affinePrimeProbability rho (-2)) X 2 h2
    (affinePrimeProbability_endpoint_two rho hrho) r).trans
      (affinePrimeEndpoint_removed_odds_formula rho hrho P X r)

theorem affinePrimeEndpoint_unshifted_odds_formula (rho : Real) (hrho : 0 < rho)
    (P : Set Nat) (X r : Nat) (h2 : Not (Membership.mem (primeClassPrefix P X) 2)) :
    List.bernoulliOutcomeMass
      (primeClassCoordinates P (affinePrimeProbability rho (-2)) X) r =
    (primeClassPrefix (removePrimeClass P 2) X).prod
      (fun p => 1 - affinePrimeProbability rho (-2) p) *
    ((primeClassPrefix (removePrimeClass P 2) X).prod
      (fun p => 1 + Polynomial.C (affinePrimeOdds rho (-2) p) * Polynomial.X)).coeff r := by
  exact (primeClass_removed_mass_eq_of_absent P (affinePrimeProbability rho (-2)) X 2 h2 r).trans
    (affinePrimeEndpoint_removed_odds_formula rho hrho P X r)

end PrimeFactorOscillations.PrimeClassDeletion

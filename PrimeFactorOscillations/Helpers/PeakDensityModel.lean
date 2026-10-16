import PrimeFactorOscillations.Helpers.PeakLocalizationBounds

/-!
# Full prime densities and exceptional small-prime factors

Full prime densities and exceptional small-prime factors for the peak-height comparison of regular prime Bernoulli laws.
-/

set_option autoImplicit false
set_option Elab.async false

open Filter Topology

namespace PrimeFactorOscillations

noncomputable def primeTailDensityWithFront (P : Nat) (eta : Nat -> Real)
    (front : List Real) (k p : Nat) : Real :=
  eta p * List.bernoulliMass
    (front ++ (p.primesBelow \ (P + 1).primesBelow).toList.map eta) k

end PrimeFactorOscillations
namespace PrimeFactorOscillations

noncomputable def smallPrimePositiveFront (P : Nat) (eta : Nat -> Real) : List Real :=
  ((P + 1).primesBelow.toList.map eta).filter (fun a => decide (Not (a = 0)))

noncomputable def primeBernoulliDensity (eta : Nat -> Real) (k p : Nat) : Real :=
  eta p * List.bernoulliMass (p.primesBelow.toList.map eta) k

theorem primeBernoulliDensity_eq_tailDensityWithFront
    (P p k : Nat) (eta : Nat -> Real) (hPp : P < p) :
    primeBernoulliDensity eta k p =
      primeTailDensityWithFront P eta (smallPrimePositiveFront P eta) k p := by
  classical
  let A := p.primesBelow
  let B := (P + 1).primesBelow
  have hBA : forall q, Membership.mem B q -> Membership.mem A q := by
    intro q hq
    have hh := Nat.mem_primesBelow.mp hq
    exact Nat.mem_primesBelow.mpr (And.intro (by omega) hh.2)
  have hfilter : A.filter (fun q => Membership.mem B q) = B := by
    ext q
    simp only [Finset.mem_filter]
    constructor
    case mp => exact fun h => h.2
    case mpr => exact fun h => And.intro (hBA q h) h
  have hp := Finset.toList_perm_filter_sdiff A B
  rw [hfilter] at hp
  have hm := List.bernoulliMass_perm (hp.map eta) k
  simp only [List.map_append] at hm
  dsimp [primeBernoulliDensity, primeTailDensityWithFront, smallPrimePositiveFront]
  rw [List.bernoulliMass_filter_front_nonzero]
  exact congrArg (fun x : Real => eta p * x) hm

theorem smallPrimePositiveFront_properties (P : Nat) (eta : Nat -> Real)
    (hunit : forall p, Nat.Prime p -> 0 <= eta p /\ eta p <= 1) :
    (forall a, List.Mem a (smallPrimePositiveFront P eta) -> 0 < a /\ a <= 1) /\
      0 < (smallPrimePositiveFront P eta).prod := by
  classical
  have hs : forall a, List.Mem a (smallPrimePositiveFront P eta) -> 0 < a /\ a <= 1 := by
    intro a ha
    have hh := List.mem_filter.mp ha
    have hm := List.mem_map.mp hh.1
    choose p hp using hm
    have hpp := (Nat.mem_primesBelow.mp (Finset.mem_toList.mp hp.1)).2
    have hne : Not (a = 0) := by simpa using hh.2
    have hnonneg : 0 <= a := by rw [<- hp.2]; exact (hunit p hpp).1
    have hpos : 0 < a := lt_of_le_of_ne hnonneg (Ne.symm hne)
    exact And.intro hpos (by rw [<- hp.2]; exact (hunit p hpp).2)
  refine And.intro hs ?_
  exact List.prod_pos (fun a ha => (hs a ha).1)

theorem primeBernoulliDensity_small_prime_eq_zero
    (P p k : Nat) (eta : Nat -> Real) (hpP : p <= P)
    (hk : (P + 1).primesBelow.card < k) :
    primeBernoulliDensity eta k p = 0 := by
  have hsub : forall q, Membership.mem p.primesBelow q ->
      Membership.mem (P + 1).primesBelow q := by
    intro q hq
    have hh := Nat.mem_primesBelow.mp hq
    exact Nat.mem_primesBelow.mpr (And.intro (by omega) hh.2)
  have hlen : (p.primesBelow.toList.map eta).length < k := by
    simpa only [List.length_map, Finset.length_toList] using
      (Finset.card_le_card hsub).trans_lt hk
  dsimp [primeBernoulliDensity]
  rw [List.bernoulliMass_eq_zero_of_length_lt _ k hlen, mul_zero]

end PrimeFactorOscillations


/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.FamilyForcedRank
import PrimeFactorOscillations.Helpers.QuadraticProbabilityRH
import PrimeFactorOscillations.Helpers.QuadraticProfileRH

/-!
# RH criteria for arbitrary qualifying probability laws

The exact finite prefix probability masses include all forced coordinates.
Only the quadratic odds condition is used; reciprocal smoothness is not needed.
-/

set_option autoImplicit false
set_option Elab.async false

namespace PrimeFactorOscillations

noncomputable def familyPrefixProbabilities (eta : Nat -> Real) (N : Nat) : List Real :=
  @List.map Nat.Primes Real (fun p : Nat.Primes => eta (p : Nat))
    (primeProfilePrefixSet N).toList

namespace QuadraticPrimeLaw

theorem probabilityMass_ratio_eq_densityRatio (law : QuadraticPrimeLaw)
    (eta : Nat -> Real)
    (hProb : forall p : Nat, Nat.Prime p -> eta p <= 1)
    (hWeight : forall p : Nat.Primes, law.weight p = eta (p : Nat) / (1 - eta (p : Nat)))
    (N r : Nat) (hr : 1 <= r) :
    let s := familyPrefixProbabilities eta N
    List.bernoulliMass s (s.count 1 + r - 1) /
      List.bernoulliMass s (s.count 1 + r) = law.densityRatio N r := by
  have hOne : forall a, List.Mem a (familyPrefixProbabilities eta N) -> a <= 1 := by
    intro a ha
    choose p hp using List.mem_map.mp ha
    rw [<- hp.2]
    exact hProb (p : Nat) p.property
  have hOdds :
      (((familyPrefixProbabilities eta N).map (fun a => a / (1 - a)) : List Real) :
        Multiset Real) = (primeProfilePrefixSet N).val.map law.weight := by
    simp only [familyPrefixProbabilities, List.map_map]
    rw [<- Multiset.map_coe, Finset.coe_toList]
    congr 1
    funext p
    exact (hWeight p).symm
  dsimp only
  rw [familyMass_ratio_eq_full_odds _ hOne r hr, hOdds]
  rfl

theorem riemannHypothesis_iff_eventually_probabilityMass_ratio
    (law : QuadraticPrimeLaw) (eta : Nat -> Real)
    (hProb : forall p : Nat, Nat.Prime p -> eta p <= 1)
    (hWeight : forall p : Nat.Primes, law.weight p = eta (p : Nat) / (1 - eta (p : Nat)))
    (alpha : Real) (ha : 0 < alpha) :
    RiemannHypothesis <-> Filter.Eventually (fun N : Nat =>
      let r := Nat.floor (alpha * law.referenceClock N)
      let s := familyPrefixProbabilities eta N
      List.bernoulliMass s (s.count 1 + r - 1) / List.bernoulliMass s (s.count 1 + r) <
        law.referenceRatio r (law.referenceClock N)) Filter.atTop := by
  rw [law.riemannHypothesis_iff_eventually_densityRatio_lt_reference alpha ha]
  choose C hC hSign using law.exists_eventually_densityRatio_reference_sign alpha ha
  apply Filter.eventually_congr
  filter_upwards [hSign] with N hN
  dsimp only
  rw [law.probabilityMass_ratio_eq_densityRatio eta hProb hWeight N _ hN.2.1]

theorem riemannHypothesis_iff_eventually_probabilityMass_ratio_le
    (law : QuadraticPrimeLaw) (eta : Nat -> Real)
    (hProb : forall p : Nat, Nat.Prime p -> eta p <= 1)
    (hWeight : forall p : Nat.Primes, law.weight p = eta (p : Nat) / (1 - eta (p : Nat)))
    (alpha : Real) (ha : 0 < alpha) :
    RiemannHypothesis <-> Filter.Eventually (fun N : Nat =>
      let r := Nat.floor (alpha * law.referenceClock N)
      let s := familyPrefixProbabilities eta N
      List.bernoulliMass s (s.count 1 + r - 1) / List.bernoulliMass s (s.count 1 + r) <=
        law.referenceRatio r (law.referenceClock N)) Filter.atTop := by
  rw [law.riemannHypothesis_iff_eventually_densityRatio_le_reference alpha ha]
  choose C hC hSign using law.exists_eventually_densityRatio_reference_sign alpha ha
  apply Filter.eventually_congr
  filter_upwards [hSign] with N hN
  dsimp only
  rw [law.probabilityMass_ratio_eq_densityRatio eta hProb hWeight N _ hN.2.1]

end QuadraticPrimeLaw

theorem riemannHypothesis_iff_eventually_quadraticProbabilityMass_ratio
    (eta : Nat -> Real) (nu E : Real) (hnu : 0 < nu) (hE : 0 <= E)
    (hProb : forall p : Nat, Nat.Prime p -> 0 <= eta p /\ eta p <= 1)
    (hError : exists P : Nat, forall p : Nat, P <= p -> Nat.Prime p ->
      abs (eta p - nu / p) <= E / (p : Real) ^ 2)
    (alpha : Real) (ha : 0 < alpha) :
    let law := quadraticPrimeLawOfEventualProbability eta nu E hnu hE hProb hError
    RiemannHypothesis <-> Filter.Eventually (fun N : Nat =>
      let r := Nat.floor (alpha * law.referenceClock N)
      let s := familyPrefixProbabilities eta N
      List.bernoulliMass s (s.count 1 + r - 1) / List.bernoulliMass s (s.count 1 + r) <
        law.referenceRatio r (law.referenceClock N)) Filter.atTop := by
  let law := quadraticPrimeLawOfEventualProbability eta nu E hnu hE hProb hError
  exact law.riemannHypothesis_iff_eventually_probabilityMass_ratio eta
      (fun p hp => (hProb p hp).2) (fun _ => rfl) alpha ha

end PrimeFactorOscillations

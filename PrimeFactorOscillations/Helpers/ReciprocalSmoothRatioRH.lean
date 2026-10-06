/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.FamilyForcedRank
import PrimeFactorOscillations.Helpers.QuadraticProfileRH
import PrimeFactorOscillations.Helpers.ReciprocalSmoothRH

/-!
# RH and actual finite prefix masses, with the exact forced-rank shift

The family coefficients are identified with the probability-mass ratio.
The rank is shifted by the actual number of forced coordinates in the prefix.
No prime is discarded silently and no arithmetic frequency hypothesis is added.
-/

set_option autoImplicit false
set_option Elab.async false

namespace PrimeFactorOscillations.ReciprocalSmoothLaw

noncomputable def rhPrefixProbabilities (law : ReciprocalSmoothLaw) (N : Nat) : List Real :=
  @List.map Nat.Primes Real (fun p : Nat.Primes => law.eta (p : Nat))
    (primeProfilePrefixSet N).toList

theorem rhPrefixProbabilities_le_one (law : ReciprocalSmoothLaw) (N : Nat) :
    forall a, List.Mem a (law.rhPrefixProbabilities N) -> a <= 1 := by
  intro a ha
  choose p hp using List.mem_map.mp ha
  rw [<- hp.2]
  exact (law.probability (p : Nat) p.property).2

theorem rhPrefixProbabilities_odds (law : ReciprocalSmoothLaw) (N : Nat) :
    (((law.rhPrefixProbabilities N).map (fun a => a / (1 - a)) : List Real) : Multiset Real) =
      (primeProfilePrefixSet N).val.map law.quadraticPrimeLaw.weight := by
  simp only [rhPrefixProbabilities, List.map_map]
  rw [<- Multiset.map_coe, Finset.coe_toList]
  rfl

theorem prefixMass_forced_ratio_eq_densityRatio (law : ReciprocalSmoothLaw)
    (N r : Nat) (hr : 1 <= r) :
    List.bernoulliMass (law.rhPrefixProbabilities N)
        ((law.rhPrefixProbabilities N).count 1 + r - 1) /
      List.bernoulliMass (law.rhPrefixProbabilities N)
        ((law.rhPrefixProbabilities N).count 1 + r) =
      law.quadraticPrimeLaw.densityRatio N r := by
  rw [familyMass_ratio_eq_full_odds _ (law.rhPrefixProbabilities_le_one N) r hr,
    law.rhPrefixProbabilities_odds]
  rfl

theorem riemannHypothesis_iff_eventually_prefixMass_ratio
    (law : ReciprocalSmoothLaw) (alpha : Real) (ha : 0 < alpha) :
    RiemannHypothesis <-> Filter.Eventually (fun N : Nat =>
      let r := Nat.floor (alpha * law.quadraticPrimeLaw.referenceClock N)
      let s := law.rhPrefixProbabilities N
      List.bernoulliMass s (s.count 1 + r - 1) / List.bernoulliMass s (s.count 1 + r) <
        law.quadraticPrimeLaw.referenceRatio r (law.quadraticPrimeLaw.referenceClock N))
      Filter.atTop := by
  rw [law.quadraticPrimeLaw.riemannHypothesis_iff_eventually_densityRatio_lt_reference alpha ha]
  choose C hC hSign using law.quadraticPrimeLaw.exists_eventually_densityRatio_reference_sign alpha ha
  apply Filter.eventually_congr
  filter_upwards [hSign] with N hN
  dsimp only
  rw [law.prefixMass_forced_ratio_eq_densityRatio N _ hN.2.1]

theorem riemannHypothesis_iff_eventually_prefixMass_ratio_le
    (law : ReciprocalSmoothLaw) (alpha : Real) (ha : 0 < alpha) :
    RiemannHypothesis <-> Filter.Eventually (fun N : Nat =>
      let r := Nat.floor (alpha * law.quadraticPrimeLaw.referenceClock N)
      let s := law.rhPrefixProbabilities N
      List.bernoulliMass s (s.count 1 + r - 1) / List.bernoulliMass s (s.count 1 + r) <=
        law.quadraticPrimeLaw.referenceRatio r (law.quadraticPrimeLaw.referenceClock N))
      Filter.atTop := by
  rw [law.quadraticPrimeLaw.riemannHypothesis_iff_eventually_densityRatio_le_reference alpha ha]
  choose C hC hSign using law.quadraticPrimeLaw.exists_eventually_densityRatio_reference_sign alpha ha
  apply Filter.eventually_congr
  filter_upwards [hSign] with N hN
  dsimp only
  rw [law.prefixMass_forced_ratio_eq_densityRatio N _ hN.2.1]

end PrimeFactorOscillations.ReciprocalSmoothLaw

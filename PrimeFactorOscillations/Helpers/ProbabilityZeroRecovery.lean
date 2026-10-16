/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/

import PrimeFactorOscillations.Helpers.NicolasSparseRecurrence
import PrimeFactorOscillations.Helpers.NicolasSparseZeroStrip
import PrimeFactorOscillations.Helpers.QuadraticMassRH
import PrimeFactorOscillations.Helpers.QuadraticWaveRate
import PrimeFactorOscillations.Helpers.XiZeroLogSpectrum
import PrimeFactorOscillations.Helpers.XiZetaMultiplicity

/-!
# Sparse RH detection and complete zero recovery

Actual finite Bernoulli masses retain every exceptional prime and forced rank. Sparse criteria, multiplicity recovery, sharp limsup, and error bounds are exposed.
-/

set_option autoImplicit false
set_option Elab.async false

open Filter
open scoped Topology

noncomputable section

namespace PrimeFactorOscillations

theorem xiFrequencyCoefficient_ne_zero_iff_zeta_zero (w : Real) :
    Not (xiFrequencyCoefficient w = 0) <->
      riemannZeta ((1 / 2 : Complex) + (w : Complex) * Complex.I) = 0 := by
  have hDen : Not (((1 / 4 + w ^ 2 : Real) : Complex) = 0) :=
    Complex.ofReal_ne_zero.mpr (ne_of_gt (by positivity : (0 : Real) < 1 / 4 + w ^ 2))
  constructor
  . intro hCoeff
    apply (xiZeroMultiplicity_criticalLine_pos_iff_zeta_zero w).mp
    apply Nat.pos_of_ne_zero
    intro hm
    apply hCoeff
    unfold xiFrequencyCoefficient
    rw [hm]
    simp
  . intro hZero
    have hPos := (xiZeroMultiplicity_criticalLine_pos_iff_zeta_zero w).mpr hZero
    have hNum : Not ((xiZeroMultiplicity
        ((1 / 2 : Complex) + (w : Complex) * Complex.I) : Complex) = 0) :=
      Nat.cast_ne_zero.mpr (Nat.ne_of_gt hPos)
    exact div_ne_zero hNum hDen

namespace QuadraticPrimeLaw

/-- The normalized observable written only with actual finite probability masses.
The exact forced-prime count appears in both adjacent ranks. -/
def probabilityNormalizedFloorRatioWave (law : QuadraticPrimeLaw) (eta : Nat -> Real)
    (alpha : Real) (N : Nat) : Real :=
  let r := law.floorRank alpha N;
  let s := familyPrefixProbabilities eta N;
  -((law.referenceClock N) ^ 2 / (law.nu * (r : Real))) *
    ((N : Real) ^ (1 / 2 : Real) * Real.log (N : Real)) *
      (List.bernoulliMass s (s.count 1 + r - 1) /
        List.bernoulliMass s (s.count 1 + r) -
          law.referenceRatio r (law.referenceClock N)) - 2

theorem probabilityNormalizedFloorRatioWave_eq_normalizedFloorRatioWave
    (law : QuadraticPrimeLaw) (eta : Nat -> Real)
    (hProb : forall p : Nat, Nat.Prime p -> eta p <= 1)
    (hWeight : forall p : Nat.Primes, law.weight p = eta (p : Nat) / (1 - eta (p : Nat)))
    (alpha : Real) (N : Nat) :
    law.probabilityNormalizedFloorRatioWave eta alpha N = law.normalizedFloorRatioWave alpha N := by
  by_cases hr : law.floorRank alpha N = 0
  . simp [probabilityNormalizedFloorRatioWave, normalizedFloorRatioWave, normalizedRatioWave, hr]
  . have hrOne : 1 <= law.floorRank alpha N := Nat.one_le_iff_ne_zero.mpr hr
    unfold probabilityNormalizedFloorRatioWave normalizedFloorRatioWave normalizedRatioWave
    dsimp only
    rw [law.probabilityMass_ratio_eq_densityRatio eta hProb hWeight N _ hrOne]

theorem probabilityMass_pos_of_prefixEsymm_pos (law : QuadraticPrimeLaw)
    (eta : Nat -> Real)
    (hProb : forall p : Nat, Nat.Prime p -> eta p <= 1)
    (hWeight : forall p : Nat.Primes, law.weight p = eta (p : Nat) / (1 - eta (p : Nat)))
    (N r : Nat) (hPrefix : 0 < law.prefixEsymm N r) :
    0 < List.bernoulliMass (familyPrefixProbabilities eta N)
      ((familyPrefixProbabilities eta N).count 1 + r) := by
  have hs : forall a, List.Mem a (familyPrefixProbabilities eta N) -> a <= 1 := by
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
  rw [familyMass_eq_survival_mul_odds _ hs r, hOdds]
  exact mul_pos (familyUnforcedList_survival_pos _ hs) hPrefix

theorem eventually_probabilityWave_denominators_pos (law : QuadraticPrimeLaw)
    (eta : Nat -> Real)
    (hProb : forall p : Nat, Nat.Prime p -> eta p <= 1)
    (hWeight : forall p : Nat.Primes, law.weight p = eta (p : Nat) / (1 - eta (p : Nat)))
    (alpha : Real) (ha : 0 < alpha) :
    Filter.Eventually (fun N : Nat =>
      1 <= law.floorRank alpha N /\
      0 < List.bernoulliMass (familyPrefixProbabilities eta N)
        ((familyPrefixProbabilities eta N).count 1 + law.floorRank alpha N) /\
      0 < Nat.factorialConvolution law.realCoefficient (law.floorRank alpha N)
        (law.referenceClock N)) atTop := by
  choose K C hK hC hEv using law.exists_eventually_normalizedFloorRatioWave_error alpha ha
  filter_upwards [hEv] with N hN
  refine And.intro (by omega) (And.intro ?_ hN.2.2.1)
  exact law.probabilityMass_pos_of_prefixEsymm_pos eta hProb hWeight N _ hN.2.1

/-- The recovered coefficient is the actual analytic multiplicity of zeta,
including multiplicities greater than one. -/
theorem tendsto_probabilityWave_fourthPower_zetaCoefficient
    (law : QuadraticPrimeLaw) (eta : Nat -> Real)
    (hProb : forall p : Nat, Nat.Prime p -> eta p <= 1)
    (hWeight : forall p : Nat.Primes, law.weight p = eta (p : Nat) / (1 - eta (p : Nat)))
    (alpha : Real) (ha : 0 < alpha) (hRH : RiemannHypothesis) (w : Real) :
    Tendsto
      (harmonicWaveMean (fun n : Nat => law.probabilityNormalizedFloorRatioWave eta alpha (n ^ 4)) w)
      atTop (nhds
        ((analyticOrderNatAt riemannZeta ((1 / 2 : Complex) + (w : Complex) * Complex.I) : Complex) /
          ((1 / 4 + w ^ 2 : Real) : Complex))) := by
  simpa only [law.probabilityNormalizedFloorRatioWave_eq_normalizedFloorRatioWave eta hProb hWeight,
    xiFrequencyCoefficient, xiZeroMultiplicity_criticalLine_eq_zetaOrder] using
    law.tendsto_harmonicWaveMean_normalizedFloorRatioWave alpha ha hRH w

theorem riemannHypothesis_iff_probabilityWave_subpower_mesh_bounded_below
    (law : QuadraticPrimeLaw) (eta : Nat -> Real)
    (hProb : forall p : Nat, Nat.Prime p -> eta p <= 1)
    (hWeight : forall p : Nat.Primes, law.weight p = eta (p : Nat) / (1 - eta (p : Nat)))
    (alpha : Real) (ha : 0 < alpha) (u : Nat -> Nat) (hu : StrictMono u)
    (hmesh : Nat.SubpowerGapBound u (3 / 4 : Real)) :
    RiemannHypothesis <-> Exists (fun B : Real =>
      Filter.Eventually (fun j : Nat => B <= law.probabilityNormalizedFloorRatioWave eta alpha (u j))
        atTop) := by
  simpa only [law.probabilityNormalizedFloorRatioWave_eq_normalizedFloorRatioWave eta hProb hWeight]
    using law.riemannHypothesis_iff_subpower_mesh_normalizedFloorRatioWave_bounded_below
      alpha ha u hu hmesh

theorem limsup_probabilityWave_subpower_mesh
    (law : QuadraticPrimeLaw) (eta : Nat -> Real)
    (hProb : forall p : Nat, Nat.Prime p -> eta p <= 1)
    (hWeight : forall p : Nat.Primes, law.weight p = eta (p : Nat) / (1 - eta (p : Nat)))
    (alpha : Real) (ha : 0 < alpha) (hRH : RiemannHypothesis)
    (u : Nat -> Nat) (hu : StrictMono u) (hmesh : Nat.SubpowerGapBound u (3 / 4 : Real)) :
    Filter.limsup (fun j : Nat => law.probabilityNormalizedFloorRatioWave eta alpha (u j)) atTop =
      Real.eulerMascheroniConstant + 2 - Real.log (4 * Real.pi) := by
  simpa only [law.probabilityNormalizedFloorRatioWave_eq_normalizedFloorRatioWave eta hProb hWeight]
    using law.limsup_normalizedFloorRatioWave_subpower_mesh alpha ha hRH u hu hmesh

theorem riemannHypothesis_iff_subpower_mesh_probabilityMass_ratio
    (law : QuadraticPrimeLaw) (eta : Nat -> Real)
    (hProb : forall p : Nat, Nat.Prime p -> eta p <= 1)
    (hWeight : forall p : Nat.Primes, law.weight p = eta (p : Nat) / (1 - eta (p : Nat)))
    (alpha : Real) (ha : 0 < alpha) (u : Nat -> Nat) (hu : StrictMono u)
    (hmesh : Nat.SubpowerGapBound u (3 / 4 : Real)) :
    RiemannHypothesis <-> Filter.Eventually (fun j : Nat =>
      let N := u j
      let r := law.floorRank alpha N
      let s := familyPrefixProbabilities eta N
      List.bernoulliMass s (s.count 1 + r - 1) / List.bernoulliMass s (s.count 1 + r) <
        law.referenceRatio r (law.referenceClock N)) atTop := by
  rw [law.riemannHypothesis_iff_subpower_mesh_densityRatio_lt_reference alpha ha u hu hmesh]
  apply Filter.eventually_congr
  have hRank := (law.tendsto_floorRank_atTop alpha ha).comp hu.tendsto_atTop
  filter_upwards [hRank.eventually_ge_atTop 1] with j hj
  dsimp only [Function.comp_def] at hj
  dsimp only
  rw [law.probabilityMass_ratio_eq_densityRatio eta hProb hWeight (u j) _ hj]
  rfl

theorem riemannHypothesis_iff_subpower_mesh_probabilityMass_ratio_le
    (law : QuadraticPrimeLaw) (eta : Nat -> Real)
    (hProb : forall p : Nat, Nat.Prime p -> eta p <= 1)
    (hWeight : forall p : Nat.Primes, law.weight p = eta (p : Nat) / (1 - eta (p : Nat)))
    (alpha : Real) (ha : 0 < alpha) (u : Nat -> Nat) (hu : StrictMono u)
    (hmesh : Nat.SubpowerGapBound u (3 / 4 : Real)) :
    RiemannHypothesis <-> Filter.Eventually (fun j : Nat =>
      let N := u j
      let r := law.floorRank alpha N
      let s := familyPrefixProbabilities eta N
      List.bernoulliMass s (s.count 1 + r - 1) / List.bernoulliMass s (s.count 1 + r) <=
        law.referenceRatio r (law.referenceClock N)) atTop := by
  rw [law.riemannHypothesis_iff_subpower_mesh_densityRatio_le_reference alpha ha u hu hmesh]
  apply Filter.eventually_congr
  have hRank := (law.tendsto_floorRank_atTop alpha ha).comp hu.tendsto_atTop
  filter_upwards [hRank.eventually_ge_atTop 1] with j hj
  dsimp only [Function.comp_def] at hj
  dsimp only
  rw [law.probabilityMass_ratio_eq_densityRatio eta hProb hWeight (u j) _ hj]
  rfl

theorem riemannHypothesis_iff_probabilityWave_fourthPower_bounded_below
    (law : QuadraticPrimeLaw) (eta : Nat -> Real)
    (hProb : forall p : Nat, Nat.Prime p -> eta p <= 1)
    (hWeight : forall p : Nat.Primes, law.weight p = eta (p : Nat) / (1 - eta (p : Nat)))
    (alpha : Real) (ha : 0 < alpha) :
    RiemannHypothesis <-> Exists (fun B : Real =>
      Filter.Eventually (fun j : Nat =>
        B <= law.probabilityNormalizedFloorRatioWave eta alpha (j ^ 4)) atTop) := by
  exact law.riemannHypothesis_iff_probabilityWave_subpower_mesh_bounded_below eta hProb hWeight
    alpha ha (fun j : Nat => j ^ 4) Nat.strictMono_fourthPower Nat.subpowerGapBound_fourthPower

theorem frequently_probabilityWave_lt_of_not_RH
    (law : QuadraticPrimeLaw) (eta : Nat -> Real)
    (hProb : forall p : Nat, Nat.Prime p -> eta p <= 1)
    (hWeight : forall p : Nat.Primes, law.weight p = eta (p : Nat) / (1 - eta (p : Nat)))
    (alpha : Real) (ha : 0 < alpha) (u : Nat -> Nat) (hu : StrictMono u)
    (hmesh : Nat.SubpowerGapBound u (3 / 4 : Real))
    (hNotRH : Not RiemannHypothesis) (A : Real) :
    Filter.Frequently (fun j : Nat => law.probabilityNormalizedFloorRatioWave eta alpha (u j) < A)
      atTop := by
  simpa only [law.probabilityNormalizedFloorRatioWave_eq_normalizedFloorRatioWave eta hProb hWeight]
    using law.frequently_normalizedFloorRatioWave_lt_of_not_RH alpha ha u hu hmesh hNotRH A

theorem exists_eventually_probabilityWave_error_div_loglog
    (law : QuadraticPrimeLaw) (eta : Nat -> Real)
    (hProb : forall p : Nat, Nat.Prime p -> eta p <= 1)
    (hWeight : forall p : Nat.Primes, law.weight p = eta (p : Nat) / (1 - eta (p : Nat)))
    (alpha : Real) (ha : 0 < alpha) (hRH : RiemannHypothesis) :
    exists K : Real, 0 <= K /\ Filter.Eventually (fun N : Nat =>
      0 < Real.log (Real.log (N : Real)) /\
      abs (law.probabilityNormalizedFloorRatioWave eta alpha N - nicolasZeroWave (N : Real)) <=
        K / Real.log (Real.log (N : Real))) atTop := by
  simpa only [law.probabilityNormalizedFloorRatioWave_eq_normalizedFloorRatioWave eta hProb hWeight]
    using law.exists_eventually_normalizedFloorRatioWave_error_div_loglog alpha ha hRH

/-- Positive moving ranks identify the actual and odds comparisons eventually. -/
theorem eventually_probabilityMass_ratio_le_iff
    (law : QuadraticPrimeLaw) (eta : Nat -> Real)
    (hProb : forall p : Nat, Nat.Prime p -> eta p <= 1)
    (hWeight : forall p : Nat.Primes, law.weight p = eta (p : Nat) / (1 - eta (p : Nat)))
    (alpha : Real) (ha : 0 < alpha) (u : Nat -> Nat) (hu : StrictMono u) :
    Filter.Eventually (fun j : Nat =>
      let N := u j
      let r := law.floorRank alpha N
      let s := familyPrefixProbabilities eta N
      List.bernoulliMass s (s.count 1 + r - 1) / List.bernoulliMass s (s.count 1 + r) <=
        law.referenceRatio r (law.referenceClock N)) atTop <->
    Filter.Eventually (fun j : Nat =>
      let N := u j
      let r := Nat.floor (alpha * law.referenceClock N)
      law.densityRatio N r <= law.referenceRatio r (law.referenceClock N)) atTop := by
  apply Filter.eventually_congr
  have hRank := (law.tendsto_floorRank_atTop alpha ha).comp hu.tendsto_atTop
  filter_upwards [hRank.eventually_ge_atTop 1] with j hj
  dsimp only [Function.comp_def] at hj
  dsimp only
  rw [law.probabilityMass_ratio_eq_densityRatio eta hProb hWeight (u j) _ hj]
  rfl

/-- A sampled mass comparison forces the stated zero strip for every real q >= 1. -/
theorem re_zero_le_max_of_powerSamples_probabilityMass_ratio_le
    (law : QuadraticPrimeLaw) (eta : Nat -> Real)
    (hProb : forall p : Nat, Nat.Prime p -> eta p <= 1)
    (hWeight : forall p : Nat.Primes, law.weight p = eta (p : Nat) / (1 - eta (p : Nat)))
    (alpha : Real) (ha : 0 < alpha) (q : Real) (hq : 1 <= q)
    (hRatio : Filter.Eventually (fun j : Nat =>
      let N := Nat.powerSamples q j
      let r := law.floorRank alpha N
      let s := familyPrefixProbabilities eta N
      List.bernoulliMass s (s.count 1 + r - 1) / List.bernoulliMass s (s.count 1 + r) <=
        law.referenceRatio r (law.referenceClock N)) atTop)
    {rho : Complex} (hZero : riemannZeta rho = 0) (hOne : rho.re < 1) :
    rho.re <= max (1 / 2 : Real) (1 - 2 / q) := by
  have h := (law.eventually_probabilityMass_ratio_le_iff eta hProb hWeight alpha ha
    (Nat.powerSamples q) (Nat.strictMono_powerSamples q hq)).mp hRatio
  exact law.re_zero_le_max_of_powerSamples_densityRatio_le alpha ha q hq h hZero hOne

theorem riemannHypothesis_iff_powerSamples_probabilityMass_ratio_le
    (law : QuadraticPrimeLaw) (eta : Nat -> Real)
    (hProb : forall p : Nat, Nat.Prime p -> eta p <= 1)
    (hWeight : forall p : Nat.Primes, law.weight p = eta (p : Nat) / (1 - eta (p : Nat)))
    (alpha : Real) (ha : 0 < alpha) (q : Real) (hq : 1 <= q) (hqUpper : q <= 4) :
    RiemannHypothesis <-> Filter.Eventually (fun j : Nat =>
      let N := Nat.powerSamples q j
      let r := law.floorRank alpha N
      let s := familyPrefixProbabilities eta N
      List.bernoulliMass s (s.count 1 + r - 1) / List.bernoulliMass s (s.count 1 + r) <=
        law.referenceRatio r (law.referenceClock N)) atTop := by
  rw [law.eventually_probabilityMass_ratio_le_iff eta hProb hWeight alpha ha
    (Nat.powerSamples q) (Nat.strictMono_powerSamples q hq)]
  exact law.riemannHypothesis_iff_powerSamples_densityRatio_le alpha ha q hq hqUpper

end QuadraticPrimeLaw

/-- The probability hypothesis is only a quadratic tail estimate; all finite
exceptional, forced, and excluded prime coordinates are retained exactly. -/
theorem quadraticProbability_fourthPower_zero_recovery
    (eta : Nat -> Real) (nu E : Real) (hnu : 0 < nu) (hE : 0 <= E)
    (hProb : forall p : Nat, Nat.Prime p -> 0 <= eta p /\ eta p <= 1)
    (hError : exists P : Nat, forall p : Nat, P <= p -> Nat.Prime p ->
      abs (eta p - nu / p) <= E / (p : Real) ^ 2)
    (alpha : Real) (ha : 0 < alpha) (hRH : RiemannHypothesis) (w : Real) :
    let law := quadraticPrimeLawOfEventualProbability eta nu E hnu hE hProb hError
    Tendsto
      (harmonicWaveMean (fun n : Nat => law.probabilityNormalizedFloorRatioWave eta alpha (n ^ 4)) w)
      atTop (nhds
        ((analyticOrderNatAt riemannZeta ((1 / 2 : Complex) + (w : Complex) * Complex.I) : Complex) /
          ((1 / 4 + w ^ 2 : Real) : Complex))) := by
  let law := quadraticPrimeLawOfEventualProbability eta nu E hnu hE hProb hError
  exact law.tendsto_probabilityWave_fourthPower_zetaCoefficient eta
    (fun p hp => (hProb p hp).2) (fun _ => rfl) alpha ha hRH w

end PrimeFactorOscillations

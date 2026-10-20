/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/

import PrimeFactorOscillations.Assembly.PrimeProfileQuadrupletAttainment
import PrimeFactorOscillations.Helpers.PrimeProfileBoundedReindexing

/-!
# RH readout on the actual short-quadruplet transport

Every prime value moved by the existing quadruplet witness changes by six.
Its local odds therefore form a qualifying quadratic law with nu=1 and
error=42, including the exceptional small primes. The moving-rank sign of
this same fixed law is equivalent to RH. Existence of a recurrent witness
with that sign is equivalent to RH together with quadruplet recurrence.
-/

set_option autoImplicit false
set_option Elab.async false

noncomputable section

attribute [local instance] Classical.propDecidable

open Filter

namespace PrimeFactorOscillations.PrimeProfileRigidity

/-- Both directions of every selected distance-two swap move its actual prime value by six. -/
theorem twoStepSwap_prime_value_displacement (B : Set Nat)
    (hB : forall n, Membership.mem B n -> Not (Membership.mem B (n + 2)))
    (hgap : forall n, Membership.mem B n ->
      PrimeFactorUnimodality.primeAt (n + 2) = PrimeFactorUnimodality.primeAt n + 6)
    (i : Nat) :
    abs ((PrimeFactorUnimodality.primeAt (Finset.twoStepSwapPerm B hB i) : Real) -
      (PrimeFactorUnimodality.primeAt i : Real)) <= 6 := by
  by_cases hi : Membership.mem B i
  . have he : Finset.twoStepSwapPerm B hB i = i + 2 := by
      change Finset.twoStepSwapPartner B i = i + 2
      simp only [Finset.twoStepSwapPartner, ite_eq_left hi]
    have hg : (PrimeFactorUnimodality.primeAt (i + 2) : Real) =
        (PrimeFactorUnimodality.primeAt i : Real) + 6 := by
      exact_mod_cast hgap i hi
    rw [he]
    have hd : (PrimeFactorUnimodality.primeAt (i + 2) : Real) -
        (PrimeFactorUnimodality.primeAt i : Real) = 6 := by linarith only [hg]
    rw [hd]
    norm_num
  . by_cases hpos : 2 <= i
    . by_cases hprev : Membership.mem B (i - 2)
      . have he : Finset.twoStepSwapPerm B hB i = i - 2 := by
          change Finset.twoStepSwapPartner B i = i - 2
          simp only [Finset.twoStepSwapPartner, ite_eq_right hi, ite_eq_left hpos,
            ite_eq_left hprev]
        have hidx : i - 2 + 2 = i := by omega
        have hgNat := hgap (i - 2) hprev
        rw [hidx] at hgNat
        have hg : (PrimeFactorUnimodality.primeAt i : Real) =
            (PrimeFactorUnimodality.primeAt (i - 2) : Real) + 6 := by
          exact_mod_cast hgNat
        rw [he]
        have hd : (PrimeFactorUnimodality.primeAt (i - 2) : Real) -
            (PrimeFactorUnimodality.primeAt i : Real) = -6 := by linarith only [hg]
        rw [hd]
        norm_num
      . have he : Finset.twoStepSwapPerm B hB i = i := by
          change Finset.twoStepSwapPartner B i = i
          simp only [Finset.twoStepSwapPartner, ite_eq_right hi, ite_eq_left hpos,
            ite_eq_right hprev]
        rw [he, sub_self, abs_zero]
        norm_num
    . have he : Finset.twoStepSwapPerm B hB i = i := by
        change Finset.twoStepSwapPartner B i = i
        simp only [Finset.twoStepSwapPartner, ite_eq_right hi, ite_eq_right hpos]
      rw [he, sub_self, abs_zero]
      norm_num

/-- The odds of the actual quadruplet permutation are a quadratic prime law with radius six. -/
def quadrupletSwapPrimeLaw (B : Set Nat)
    (hB : forall n, Membership.mem B n -> Not (Membership.mem B (n + 2)))
    (hgap : forall n, Membership.mem B n ->
      PrimeFactorUnimodality.primeAt (n + 2) = PrimeFactorUnimodality.primeAt n + 6) :
    QuadraticPrimeLaw :=
  boundedPrimeReindexingLaw (permutedPrimeValue (Finset.twoStepSwapPerm B hB))
    (permutedPrimeValue_prime _) 6 (by norm_num)
    (permutedPrimeValue_displacement _ 6 (twoStepSwap_prime_value_displacement B hB hgap))

/-- The RH law uses the actual odds of the same constellation probability profile. -/
theorem quadrupletSwapPrimeLaw_weight_eq_profile_odds (B : Set Nat)
    (hB : forall n, Membership.mem B n -> Not (Membership.mem B (n + 2)))
    (hgap : forall n, Membership.mem B n ->
      PrimeFactorUnimodality.primeAt (n + 2) = PrimeFactorUnimodality.primeAt n + 6)
    (p : Nat.Primes) :
    (quadrupletSwapPrimeLaw B hB hgap).weight p =
      primePermutationProfileLaw (Finset.twoStepSwapPerm B hB) (Nat.count Nat.Prime (p : Nat)) /
        (1 - primePermutationProfileLaw (Finset.twoStepSwapPerm B hB)
          (Nat.count Nat.Prime (p : Nat))) := by
  let q := permutedPrimeValue (Finset.twoStepSwapPerm B hB) p
  have hq : Nat.Prime q := permutedPrimeValue_prime _ _
  have hqR : (1 : Real) < q := by exact_mod_cast hq.one_lt
  have hqpos : (0 : Real) < q := by linarith only [hqR]
  have hpred : (0 : Real) < (q : Real) - 1 := by linarith only [hqR]
  have hinv : 1 / (q : Real) < 1 := by
    have h := one_div_lt_one_div_of_lt (by norm_num : (0 : Real) < 1) hqR
    simpa only [one_div_one] using h
  have hprob : 0 < 1 - 1 / (q : Real) := sub_pos.mpr hinv
  change primeProfileWeight q = (1 / (q : Real)) / (1 - 1 / (q : Real))
  unfold primeProfileWeight
  rw [Nat.cast_sub hq.one_le, Nat.cast_one]
  field_simp [hqpos.ne', hpred.ne', hprob.ne']

/-- The constants are explicit and independent of the chosen sparse constellation support. -/
theorem quadrupletSwapPrimeLaw_parameters (B : Set Nat)
    (hB : forall n, Membership.mem B n -> Not (Membership.mem B (n + 2)))
    (hgap : forall n, Membership.mem B n ->
      PrimeFactorUnimodality.primeAt (n + 2) = PrimeFactorUnimodality.primeAt n + 6) :
    (quadrupletSwapPrimeLaw B hB hgap).nu = 1 /\
      (quadrupletSwapPrimeLaw B hB hgap).error = 42 := by
  constructor
  . rfl
  . norm_num [quadrupletSwapPrimeLaw, boundedPrimeReindexingLaw]

/-- For each fixed support, its actual moving coefficient sign is equivalent to RH. -/
theorem quadruplet_swap_rh_iff (B : Set Nat)
    (hB : forall n, Membership.mem B n -> Not (Membership.mem B (n + 2)))
    (hgap : forall n, Membership.mem B n ->
      PrimeFactorUnimodality.primeAt (n + 2) = PrimeFactorUnimodality.primeAt n + 6)
    (alpha : Real) (ha : 0 < alpha) :
    let law := quadrupletSwapPrimeLaw B hB hgap
    RiemannHypothesis <-> Filter.Eventually (fun N : Nat =>
      let r := Nat.floor (alpha * law.referenceClock N)
      law.densityRatio N r < law.referenceRatio r (law.referenceClock N)) atTop := by
  exact QuadraticPrimeLaw.riemannHypothesis_iff_eventually_densityRatio_lt_reference
    (quadrupletSwapPrimeLaw B hB hgap) alpha ha

/-- This existential sign criterion detects the conjunction of RH and recurrent short quadruplets. -/
theorem recurrent_quadruplet_and_rh_iff_transport_sign (alpha : Real) (ha : 0 < alpha) :
    (RiemannHypothesis /\
      (forall N : Nat, exists k : Nat, N <= k /\ IsShortPrimeQuadruplet k)) <->
    (exists B : Set Nat,
      exists hB : forall n, Membership.mem B n -> Not (Membership.mem B (n + 2)),
      exists hgap : forall n, Membership.mem B n ->
        PrimeFactorUnimodality.primeAt (n + 2) = PrimeFactorUnimodality.primeAt n + 6,
      (forall N : Nat, exists k : Nat, N <= k /\
        Membership.mem B k /\ Membership.mem B (k + 1)) /\
      (let law := quadrupletSwapPrimeLaw B hB hgap
       Filter.Eventually (fun N : Nat =>
         let r := Nat.floor (alpha * law.referenceClock N)
         law.densityRatio N r < law.referenceRatio r (law.referenceClock N)) atTop)) := by
  constructor
  . intro hh
    have hs := exists_unbounded_quadruplet_twoStepSupport hh.2
    let B := Classical.choose hs
    have hd := Classical.choose_spec hs
    refine Exists.intro B (Exists.intro hd.1 (Exists.intro hd.2.1 ?_))
    exact And.intro hd.2.2 ((quadruplet_swap_rh_iff B hd.1 hd.2.1 alpha ha).mp hh.1)
  . intro hh
    let B := Classical.choose hh
    have hfirst := Classical.choose_spec hh
    let hB := Classical.choose hfirst
    have hsecond := Classical.choose_spec hfirst
    let hgap := Classical.choose hsecond
    have hd := Classical.choose_spec hsecond
    have hRH : RiemannHypothesis := (quadruplet_swap_rh_iff B hB hgap alpha ha).mpr hd.2
    let e := Finset.twoStepSwapPerm B hB
    have hcross : forall N : Nat, exists k : Nat,
        N <= k /\ 2 <= Finset.prefixDisplacement e (k + 2) := by
      intro N
      let k := Classical.choose (hd.1 N)
      have hk := Classical.choose_spec (hd.1 N)
      exact Exists.intro k (And.intro hk.1
        (Finset.two_le_prefixDisplacement_twoStepSwapPerm B hB k hk.2.1 hk.2.2))
    have hu := eventual_uniform_twoStepSwap_cost_le B hB hgap 1 (by norm_num)
    let M := Classical.choose hu
    have hM := Classical.choose_spec hu
    let t : Nat -> Real := fun _ => 1
    have ht : forall n, 0 < t n := fun _ => by norm_num [t]
    have hupper : Filter.Eventually (fun k : Nat =>
        normalizedPrimePrefixDefect e t (k + 1) <= 13) atTop := by
      apply eventually_atTop.mpr
      refine Exists.intro M ?_
      intro k hk
      have hb := hM k hk t (ht (k + 1))
      norm_num at hb
      exact hb
    exact And.intro hRH
      (recurrent_quadruplet_of_infinite_double_crossings e t ht 13
        (by norm_num) hupper hcross)

end PrimeFactorOscillations.PrimeProfileRigidity

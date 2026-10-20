/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/

import PrimeFactorOscillations.Assembly.PrimeProfileQuadrupletRH
import PrimeFactorOscillations.Helpers.PrimeProfileReferenceInvariance

/-!
# A single canonical RH reference for every short-quadruplet transport

The complete signed logarithmic pairing identifies every actual constellation
reference with the fixed canonical reciprocal-odds reference. Both the
fixed-witness RH criterion and the existential conjunction criterion therefore
use the same reference, independent of the chosen support.
-/

set_option autoImplicit false
set_option Elab.async false

noncomputable section

open Filter

namespace PrimeFactorOscillations.PrimeProfileRigidity

/-- The actual distance-six permutation preserves the entire canonical odds reference. -/
theorem quadrupletSwapPrimeLaw_complexProfile_canonical (B : Set Nat)
    (hB : forall n, Membership.mem B n -> Not (Membership.mem B (n + 2)))
    (hgap : forall n, Membership.mem B n ->
      PrimeFactorUnimodality.primeAt (n + 2) = PrimeFactorUnimodality.primeAt n + 6) :
    (quadrupletSwapPrimeLaw B hB hgap).complexProfile =
      canonicalPrimeOddsLaw.complexProfile := by
  let e := Finset.twoStepSwapPerm B hB
  have hinv : Function.Involutive e := Finset.twoStepSwapPartner_involutive B hB
  apply QuadraticPrimeLaw.complexProfile_eq_of_involutive_weights
    (quadrupletSwapPrimeLaw B hB hgap) canonicalPrimeOddsLaw
    (primeValuePermutation e) (primeValuePermutation_involutive e hinv) rfl
  intro p
  rfl

/-- Every reference coefficient ratio is fixed independently of the constellation support. -/
theorem quadrupletSwapPrimeLaw_referenceRatio_canonical (B : Set Nat)
    (hB : forall n, Membership.mem B n -> Not (Membership.mem B (n + 2)))
    (hgap : forall n, Membership.mem B n ->
      PrimeFactorUnimodality.primeAt (n + 2) = PrimeFactorUnimodality.primeAt n + 6)
    (r : Nat) (u : Real) :
    (quadrupletSwapPrimeLaw B hB hgap).referenceRatio r u =
      canonicalPrimeOddsLaw.referenceRatio r u := by
  unfold QuadraticPrimeLaw.referenceRatio QuadraticPrimeLaw.realCoefficient
  rw [quadrupletSwapPrimeLaw_complexProfile_canonical B hB hgap]

/-- The clock is the same canonical clock at every natural cutoff, including small cutoffs. -/
theorem quadrupletSwapPrimeLaw_referenceClock_canonical (B : Set Nat)
    (hB : forall n, Membership.mem B n -> Not (Membership.mem B (n + 2)))
    (hgap : forall n, Membership.mem B n ->
      PrimeFactorUnimodality.primeAt (n + 2) = PrimeFactorUnimodality.primeAt n + 6)
    (N : Nat) :
    (quadrupletSwapPrimeLaw B hB hgap).referenceClock N =
      canonicalPrimeOddsLaw.referenceClock N := by
  rfl

/-- Each fixed constellation transport reads RH against one canonical reference at all positive rank scales. -/
theorem quadruplet_swap_rh_iff_canonical (B : Set Nat)
    (hB : forall n, Membership.mem B n -> Not (Membership.mem B (n + 2)))
    (hgap : forall n, Membership.mem B n ->
      PrimeFactorUnimodality.primeAt (n + 2) = PrimeFactorUnimodality.primeAt n + 6)
    (alpha : Real) (ha : 0 < alpha) :
    RiemannHypothesis <-> Filter.Eventually (fun N : Nat =>
      let L := canonicalPrimeOddsLaw.referenceClock N
      let r := Nat.floor (alpha * L)
      (quadrupletSwapPrimeLaw B hB hgap).densityRatio N r <
        canonicalPrimeOddsLaw.referenceRatio r L) atTop := by
  have h := quadruplet_swap_rh_iff B hB hgap alpha ha
  dsimp only at h
  simpa only [quadrupletSwapPrimeLaw_referenceRatio_canonical,
    quadrupletSwapPrimeLaw_referenceClock_canonical] using h

/-- The exact existential constellation/RH criterion also has one fixed canonical reference. -/
theorem recurrent_quadruplet_and_rh_iff_canonical_transport_sign (alpha : Real) (ha : 0 < alpha) :
    (RiemannHypothesis /\
      (forall N : Nat, exists k : Nat, N <= k /\ IsShortPrimeQuadruplet k)) <->
    (exists B : Set Nat,
      exists hB : forall n, Membership.mem B n -> Not (Membership.mem B (n + 2)),
      exists hgap : forall n, Membership.mem B n ->
        PrimeFactorUnimodality.primeAt (n + 2) = PrimeFactorUnimodality.primeAt n + 6,
      (forall N : Nat, exists k : Nat, N <= k /\
        Membership.mem B k /\ Membership.mem B (k + 1)) /\
      Filter.Eventually (fun N : Nat =>
        let L := canonicalPrimeOddsLaw.referenceClock N
        let r := Nat.floor (alpha * L)
        (quadrupletSwapPrimeLaw B hB hgap).densityRatio N r <
          canonicalPrimeOddsLaw.referenceRatio r L) atTop) := by
  have h := recurrent_quadruplet_and_rh_iff_transport_sign alpha ha
  dsimp only at h
  simpa only [quadrupletSwapPrimeLaw_referenceRatio_canonical,
    quadrupletSwapPrimeLaw_referenceClock_canonical] using h

end PrimeFactorOscillations.PrimeProfileRigidity

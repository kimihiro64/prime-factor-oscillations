/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Assembly.FiniteFieldNativeWordEvents
import PrimeFactorOscillations.Assembly.FiniteFieldPrimeCycleKernel

/-! # The complete signed native character word law

The limit is an explicit finite sum over even-sized cycle masks. All word
supports and sign assignments are fixed before the independent field scale.
-/

set_option autoImplicit false
set_option Elab.async false

noncomputable section
namespace PrimeFactorOscillations.FiniteFieldIntegerSignature
open Filter FiniteFieldIntegerWindowTransfer
open scoped Classical
attribute [local instance] Classical.propDecidable

def nativeSignedCycleMask (P : Finset Nat) (O T : Finset (Prod Nat Nat)) : Prop :=
  And (O = T) (And (forall p : Nat, Membership.mem P p ->
    nativePrimeVertexCycleDegree O p % 2 = 0) (O.card % 2 = 0))

def nativeSignedWordRate (P : Finset Nat) (A B : Finset (Prod Nat Nat))
    (a b : Prod Nat Nat -> Bool) : Real :=
  (1 / (2 : Real) ^ (A.card + B.card)) *
    A.powerset.sum (fun O => B.powerset.sum (fun T =>
      nativeSignedWordMaskCoefficient O T a b *
        (if nativeSignedCycleMask P O T then 1 else 0)))

theorem native_signed_word_ratio_tendsto (P : Finset Nat)
    (hP : forall p : Nat, Membership.mem P p -> Nat.Prime p)
    (hind : nativePrimeVertexGapIndependent P) (A B : Finset (Prod Nat Nat))
    (hA : A <= nativePrimeVertexEdges P) (hB : B <= nativePrimeVertexEdges P)
    (a b : Prod Nat Nat -> Bool) :
    Tendsto (fun U : Nat =>
      nativeSignedWordMass A B a b (preciseCore U + 1) (preciseCore U * preciseCore U + 1) /
        reciprocalBand (preciseCore U + 1) (preciseCore U * preciseCore U + 1))
      atTop (nhds (nativeSignedWordRate P A B a b)) := by
  let C : Real := 1 / (2 : Real) ^ (A.card + B.card)
  let F : Nat -> Real := fun U =>
    C * A.powerset.sum (fun O => B.powerset.sum (fun T =>
      nativeSignedWordMaskCoefficient O T a b *
        (nativeSignedRowMoment O T (preciseCore U + 1) (preciseCore U * preciseCore U + 1) /
          reciprocalBand (preciseCore U + 1) (preciseCore U * preciseCore U + 1))))
  have hlim : Tendsto F atTop (nhds (nativeSignedWordRate P A B a b)) := by
    dsimp only [F, C, nativeSignedWordRate]
    apply Filter.Tendsto.const_mul
    apply tendsto_finsetSum A.powerset
    intro O hO
    apply tendsto_finsetSum B.powerset
    intro T hT
    have hm := native_signed_cycle_moment_ratio_tendsto P hP hind O T
      ((Finset.mem_powerset.mp hO).trans hA) ((Finset.mem_powerset.mp hT).trans hB)
    have hw := Filter.Tendsto.const_mul (nativeSignedWordMaskCoefficient O T a b) hm
    by_cases hc : nativeSignedCycleMask P O T
    . have hraw : And (O = T) (And (forall p : Nat, Membership.mem P p ->
          nativePrimeVertexCycleDegree O p % 2 = 0) (O.card % 2 = 0)) := hc
      rw [ite_eq_left hc]
      simpa only [ite_eq_left hraw] using hw
    . have hraw : Not (And (O = T) (And (forall p : Nat, Membership.mem P p ->
          nativePrimeVertexCycleDegree O p % 2 = 0) (O.card % 2 = 0))) := hc
      rw [ite_eq_right hc]
      simpa only [ite_eq_right hraw] using hw
  apply hlim.congr'
  filter_upwards [native_signed_word_mass_expansion_eventually P hP A B hA hB a b] with U hU
  dsimp only [F, C]
  rw [hU]
  simp only [mul_div_assoc, Finset.sum_div]

theorem native_reservoir_signed_word_ratio_tendsto
    (R : Nat -> Prop) [DecidablePred R] (P : Finset Nat)
    (hP : forall p : Nat, Membership.mem P p ->
      Membership.mem (nativePrimeVertexGapReservoirClass R) p)
    (A B : Finset (Prod Nat Nat))
    (hA : A <= nativePrimeVertexEdges P) (hB : B <= nativePrimeVertexEdges P)
    (a b : Prod Nat Nat -> Bool) :
    Tendsto (fun U : Nat =>
      nativeSignedWordMass A B a b (preciseCore U + 1) (preciseCore U * preciseCore U + 1) /
        reciprocalBand (preciseCore U + 1) (preciseCore U * preciseCore U + 1))
      atTop (nhds (nativeSignedWordRate P A B a b)) :=
  native_signed_word_ratio_tendsto P
    (fun p hp => (native_gap_reservoir_class_geometry R p (hP p hp)).1)
    (native_gap_reservoir_class_finite_independent R P hP) A B hA hB a b

theorem native_infinite_signed_word_family_in_reservoir
    (R : Nat -> Prop) [DecidablePred R]
    (hR : Not (Filter.Tendsto (fun N : Nat => primeEventProbability N R)
      Filter.atTop (nhds 0))) :
    And (Set.Infinite (nativePrimeVertexGapReservoirClass R))
      (And (forall p : Nat, Membership.mem (nativePrimeVertexGapReservoirClass R) p ->
          And (Nat.Prime p) (R p))
        (forall P : Finset Nat,
          (forall p : Nat, Membership.mem P p ->
            Membership.mem (nativePrimeVertexGapReservoirClass R) p) ->
          forall A B : Finset (Prod Nat Nat),
            A <= nativePrimeVertexEdges P -> B <= nativePrimeVertexEdges P ->
            forall a b : Prod Nat Nat -> Bool,
              Tendsto (fun U : Nat => nativeSignedWordMass A B a b
                (preciseCore U + 1) (preciseCore U * preciseCore U + 1) /
                  reciprocalBand (preciseCore U + 1) (preciseCore U * preciseCore U + 1))
                atTop (nhds (nativeSignedWordRate P A B a b)))) := by
  have h := native_infinite_prime_gap_independent_family_in_reservoir R hR
  exact And.intro h.1 (And.intro h.2.1 (native_reservoir_signed_word_ratio_tendsto R))

theorem native_infinite_signed_word_family :
    And (Set.Infinite (nativePrimeVertexGapReservoirClass (fun _ => True)))
      (And (forall p : Nat,
          Membership.mem (nativePrimeVertexGapReservoirClass (fun _ => True)) p -> Nat.Prime p)
        (forall P : Finset Nat,
          (forall p : Nat, Membership.mem P p ->
            Membership.mem (nativePrimeVertexGapReservoirClass (fun _ => True)) p) ->
          forall A B : Finset (Prod Nat Nat),
            A <= nativePrimeVertexEdges P -> B <= nativePrimeVertexEdges P ->
            forall a b : Prod Nat Nat -> Bool,
              Tendsto (fun U : Nat => nativeSignedWordMass A B a b
                (preciseCore U + 1) (preciseCore U * preciseCore U + 1) /
                  reciprocalBand (preciseCore U + 1) (preciseCore U * preciseCore U + 1))
                atTop (nhds (nativeSignedWordRate P A B a b)))) := by
  have h := native_infinite_prime_gap_independent_family
  exact And.intro h.1 (And.intro h.2.1
    (native_reservoir_signed_word_ratio_tendsto (fun _ => True)))

end PrimeFactorOscillations.FiniteFieldIntegerSignature

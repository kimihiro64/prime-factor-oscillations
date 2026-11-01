/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Assembly.FiniteFieldIndependentPrimeVertices
import PrimeFactorOscillations.Helpers.NativePrimeVertexGapCycles

/-! # A computable infinite prime graph with exactly the native cycle relations

The same class has full independent vertex/gap coordinates. Its lower/upper
row relations are precisely the doubled even-degree edge sets.
-/

set_option autoImplicit false
set_option Elab.async false

namespace PrimeFactorOscillations.FiniteFieldIntegerSignature

theorem native_gap_reservoir_row_product_square_iff
    (R : Nat -> Prop) [DecidablePred R] (P : Finset Nat)
    (hP : forall p : Nat, Membership.mem P p ->
      Membership.mem (nativePrimeVertexGapReservoirClass R) p)
    (A B : Finset (Prod Nat Nat))
    (hA : A <= nativePrimeVertexEdges P) (hB : B <= nativePrimeVertexEdges P) :
    IsSquare (A.prod (fun e => e.1 * (e.2 - e.1)) *
      B.prod (fun e => e.2 * (e.2 - e.1))) <->
        And (A = B) (forall p : Nat, Membership.mem P p ->
          nativePrimeVertexCycleDegree A p % 2 = 0) :=
  native_gap_row_product_square_iff P
    (fun p hp => (native_gap_reservoir_class_geometry R p (hP p hp)).1)
    (native_gap_reservoir_class_finite_independent R P hP) A B hA hB

theorem native_prime_cycle_kernel_family_in_reservoir
    (R : Nat -> Prop) [DecidablePred R]
    (hR : Not (Filter.Tendsto (fun N : Nat => primeEventProbability N R)
      Filter.atTop (nhds 0))) :
    And (Set.Infinite (nativePrimeVertexGapReservoirClass R))
      (And (forall p : Nat, Membership.mem (nativePrimeVertexGapReservoirClass R) p ->
          And (Nat.Prime p) (R p))
        (And (forall P : Finset Nat,
          (forall p : Nat, Membership.mem P p ->
            Membership.mem (nativePrimeVertexGapReservoirClass R) p) ->
              nativePrimeVertexGapIndependent P)
          (forall P : Finset Nat,
            (forall p : Nat, Membership.mem P p ->
              Membership.mem (nativePrimeVertexGapReservoirClass R) p) ->
            forall A B : Finset (Prod Nat Nat),
              A <= nativePrimeVertexEdges P -> B <= nativePrimeVertexEdges P ->
                (IsSquare (A.prod (fun e => e.1 * (e.2 - e.1)) *
                  B.prod (fun e => e.2 * (e.2 - e.1))) <->
                    And (A = B) (forall p : Nat, Membership.mem P p ->
                      nativePrimeVertexCycleDegree A p % 2 = 0))))) := by
  have h := native_infinite_prime_gap_independent_family_in_reservoir R hR
  exact And.intro h.1 (And.intro h.2.1
    (And.intro h.2.2 (native_gap_reservoir_row_product_square_iff R)))

theorem native_prime_cycle_kernel_family :
    And (Set.Infinite (nativePrimeVertexGapReservoirClass (fun _ => True)))
      (And (forall p : Nat,
          Membership.mem (nativePrimeVertexGapReservoirClass (fun _ => True)) p -> Nat.Prime p)
        (And (forall P : Finset Nat,
          (forall p : Nat, Membership.mem P p ->
            Membership.mem (nativePrimeVertexGapReservoirClass (fun _ => True)) p) ->
              nativePrimeVertexGapIndependent P)
          (forall P : Finset Nat,
            (forall p : Nat, Membership.mem P p ->
              Membership.mem (nativePrimeVertexGapReservoirClass (fun _ => True)) p) ->
            forall A B : Finset (Prod Nat Nat),
              A <= nativePrimeVertexEdges P -> B <= nativePrimeVertexEdges P ->
                (IsSquare (A.prod (fun e => e.1 * (e.2 - e.1)) *
                  B.prod (fun e => e.2 * (e.2 - e.1))) <->
                    And (A = B) (forall p : Nat, Membership.mem P p ->
                      nativePrimeVertexCycleDegree A p % 2 = 0))))) := by
  have h := native_infinite_prime_gap_independent_family
  exact And.intro h.1 (And.intro h.2.1
    (And.intro h.2.2 (native_gap_reservoir_row_product_square_iff (fun _ => True))))

end PrimeFactorOscillations.FiniteFieldIntegerSignature

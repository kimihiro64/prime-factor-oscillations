/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Definitions.NativePrimeVertexGapExtension
import PrimeFactorOscillations.Helpers.NativePrimeVertexGapInsertion
import PrimeFactorOscillations.Proof.AffinePairs.PrimeSplitSquarePolynomials

/-! # Density-zero rejection of every new vertex/gap square relation

The finite index set contains every old subproduct and every nonempty subset
of new gaps. Overlaps between these rejection events are retained.
-/

set_option autoImplicit false
set_option Elab.async false

namespace PrimeFactorOscillations.FiniteFieldIntegerSignature

open scoped Classical
attribute [local instance] Classical.propDecidable

theorem tendsto_native_prime_gap_unclear_zero (P : Finset Nat)
    (hP : forall p : Nat, Membership.mem P p -> Nat.Prime p) :
    Filter.Tendsto (fun N : Nat => primeEventProbability N
      (fun q => Not (nativePrimeVertexGapExtensionClear P q)))
        Filter.atTop (nhds 0) := by
  let J : Finset (Prod (Finset (Sum Nat (Prod Nat Nat))) (Finset Nat)) :=
    (nativeVertexGapBasis P).powerset.product (P.powerset.filter Finset.Nonempty)
  let I : Type := J
  let F : I -> Nat -> Prop := fun i q =>
    IsSquare (i.val.1.prod nativeVertexGapValue * i.val.2.prod (fun p => q - p))
  have hEach : forall i : I, Filter.Tendsto
      (fun N : Nat => primeEventProbability N (F i)) Filter.atTop (nhds 0) := by
    intro i
    have hi : And (Membership.mem (nativeVertexGapBasis P).powerset i.val.1)
        (Membership.mem (P.powerset.filter Finset.Nonempty) i.val.2) :=
      Finset.mem_product.mp i.property
    have hO : i.val.1 <= nativeVertexGapBasis P := Finset.mem_powerset.mp hi.1
    have hT : i.val.2.Nonempty := (Finset.mem_filter.mp hi.2).2
    exact tendsto_prime_split_product_square_values_zero i.val.2
      (i.val.1.prod nativeVertexGapValue) hT
      (native_gap_subfamily_product_positive P hP i.val.1 hO)
  have hImp : forall q : Nat, Not (nativePrimeVertexGapExtensionClear P q) ->
      exists i : I, F i q := by
    intro q hq
    by_contra hnone
    apply hq
    intro O hO T hT hnon hsq
    apply hnone
    let i : I := Subtype.mk (O, T) (Finset.mem_product.mpr
      (And.intro hO (Finset.mem_filter.mpr (And.intro hT hnon))))
    exact Exists.intro i hsq
  exact tendsto_prime_probability_zero_of_imp
    (fun q => Not (nativePrimeVertexGapExtensionClear P q))
    (fun q => exists i : I, F i q) hImp
    (tendsto_prime_probability_finite_union_zero F hEach)

theorem tendsto_native_prime_gap_rejection_zero (P : Finset Nat) (B : Nat)
    (hP : forall p : Nat, Membership.mem P p -> Nat.Prime p) :
    Filter.Tendsto (fun N : Nat => primeEventProbability N (fun q => Or (q <= B)
      (Not (nativePrimeVertexGapExtensionClear P q)))) Filter.atTop (nhds 0) := by
  let E : Bool -> Nat -> Prop
    | false, q => q <= B
    | true, q => Not (nativePrimeVertexGapExtensionClear P q)
  have hEach : forall b : Bool, Filter.Tendsto
      (fun N : Nat => primeEventProbability N (E b)) Filter.atTop (nhds 0) := by
    intro b
    cases b with
    | false => exact tendsto_prime_probability_bounded_zero B
    | true => exact tendsto_native_prime_gap_unclear_zero P hP
  apply tendsto_prime_probability_zero_of_imp
    (fun q => Or (q <= B) (Not (nativePrimeVertexGapExtensionClear P q)))
    (fun q => exists b : Bool, E b q)
  . intro q hq
    cases hq with
    | inl h => exact Exists.intro false h
    | inr h => exact Exists.intro true h
  . exact tendsto_prime_probability_finite_union_zero E hEach

end PrimeFactorOscillations.FiniteFieldIntegerSignature

/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Assembly.FiniteFieldNativeVertexInsertion
import PrimeFactorOscillations.Proof.AffinePairs.FiniteEventProbability
import PrimeFactorOscillations.Proof.AffinePairs.PrimeSquarePolynomials

/-! # Density-one extension of every finite flat prime vertex set

Every fixed old/new and new/new rejection polynomial has prime-relative
density zero. Their full finite union retains all overlaps.
-/

set_option autoImplicit false
set_option Elab.async false

namespace PrimeFactorOscillations.FiniteFieldIntegerSignature

open scoped Classical
attribute [local instance] Classical.propDecidable

theorem tendsto_native_prime_vertex_unclear_zero (P : Finset Nat)
    (hP : forall p : Nat, Membership.mem P p -> Nat.Prime p) :
    Filter.Tendsto (fun N : Nat => primeEventProbability N
      (fun q => Not (nativePrimeVertexExtensionClear P q))) Filter.atTop (nhds 0) := by
  let A : Type := Prod P {nm : Prod P P // nm.1.val < nm.2.val}
  let B : Type := {pr : Prod P P // Not (pr.1.val = pr.2.val)}
  let I : Type := Sum A (Sum B B)
  let f : I -> Nat -> Prop
    | Sum.inl a, q =>
      IsSquare ((((a.1.val * a.2.val.1.val *
        (a.2.val.2.val - a.2.val.1.val) : Nat) : Int)) *
          ((q : Int) - (a.1.val : Int)))
    | Sum.inr (Sum.inl b), q =>
      IsSquare ((((b.val.1.val * b.val.2.val : Nat) : Int)) *
        ((q : Int) - (b.val.1.val : Int)) * ((q : Int) - (b.val.2.val : Int)))
    | Sum.inr (Sum.inr b), q =>
      IsSquare (((q : Int) - (b.val.1.val : Int)) *
        ((q : Int) - (b.val.2.val : Int)))
  have hEach : forall i : I, Filter.Tendsto (fun N : Nat => primeEventProbability N (f i))
        Filter.atTop (nhds 0) := by
    intro i
    cases i with
    | inl a =>
      have ht : 0 < a.1.val * a.2.val.1.val * (a.2.val.2.val - a.2.val.1.val) :=
        Nat.mul_pos (Nat.mul_pos (hP a.1.val a.1.property).pos
          (hP a.2.val.1.val a.2.val.1.property).pos)
          (Nat.sub_pos_of_lt a.2.property)
      simpa only [prime_filter_ratio_eq_probability, f] using tendsto_prime_affine_square_values_zero
        (a.1.val * a.2.val.1.val * (a.2.val.2.val - a.2.val.1.val)) a.1.val ht
    | inr b =>
      cases b with
      | inl b =>
        have ht : 0 < b.val.1.val * b.val.2.val :=
          Nat.mul_pos (hP b.val.1.val b.val.1.property).pos
            (hP b.val.2.val b.val.2.property).pos
        simpa only [prime_filter_ratio_eq_probability, f] using tendsto_prime_split_quadratic_square_values_zero
          (b.val.1.val * b.val.2.val) b.val.1.val b.val.2.val ht b.property
      | inr b =>
        simpa only [prime_filter_ratio_eq_probability, f, Nat.cast_one, one_mul] using
          tendsto_prime_split_quadratic_square_values_zero
            1 b.val.1.val b.val.2.val (by decide) b.property
  have hImp : forall q : Nat, Not (nativePrimeVertexExtensionClear P q) ->
      exists i : I, f i q := by
    intro q hnot
    by_contra hnone
    apply hnot
    constructor
    . intro p hp n hn m hm hnm hs
      apply hnone
      exact Exists.intro (Sum.inl
        (Subtype.mk p hp, Subtype.mk (Subtype.mk n hn, Subtype.mk m hm) hnm)) hs
    . constructor
      . intro p hp r hr hpr hs
        apply hnone
        exact Exists.intro (Sum.inr (Sum.inl
          (Subtype.mk (Subtype.mk p hp, Subtype.mk r hr) hpr))) hs
      . intro p hp r hr hpr hs
        apply hnone
        exact Exists.intro (Sum.inr (Sum.inr
          (Subtype.mk (Subtype.mk p hp, Subtype.mk r hr) hpr))) hs
  exact tendsto_prime_probability_zero_of_imp
    (fun q => Not (nativePrimeVertexExtensionClear P q))
    (fun q => exists i : I, f i q) hImp (tendsto_prime_probability_finite_union_zero f hEach)

theorem tendsto_native_prime_vertex_clear_one (P : Finset Nat)
    (hP : forall p : Nat, Membership.mem P p -> Nat.Prime p) :
    Filter.Tendsto (fun N : Nat => primeEventProbability N (nativePrimeVertexExtensionClear P))
      Filter.atTop (nhds 1) :=
  tendsto_prime_probability_one_of_complement_zero (nativePrimeVertexExtensionClear P)
    (tendsto_native_prime_vertex_unclear_zero P hP)

theorem tendsto_native_prime_vertex_valid_extensions_one (P : Finset Nat) (B : Nat)
    (hP : forall p : Nat, Membership.mem P p -> Nat.Prime p)
    (hflat : nativePrimeVertexSquareFlat P)
    (hB : forall p : Nat, Membership.mem P p -> p <= B) :
    Filter.Tendsto (fun N : Nat => primeEventProbability N (fun q => And (B < q)
      (nativePrimeVertexSquareFlat (insert q P)))) Filter.atTop (nhds 1) := by
  let V : Nat -> Prop := fun q => And (B < q) (nativePrimeVertexSquareFlat (insert q P))
  let E : Bool -> Nat -> Prop
    | false, q => q <= B
    | true, q => Not (nativePrimeVertexExtensionClear P q)
  have hEach : forall b : Bool, Filter.Tendsto
      (fun N : Nat => primeEventProbability N (E b)) Filter.atTop (nhds 0) := by
    intro b
    cases b with
    | false => exact tendsto_prime_probability_bounded_zero B
    | true => exact tendsto_native_prime_vertex_unclear_zero P hP
  have hImp : forall q : Nat, Not (Nat.Prime q -> V q) -> exists b : Bool, E b q := by
    intro q hnot
    by_cases hle : q <= B
    . exact Exists.intro false hle
    . by_cases hc : nativePrimeVertexExtensionClear P q
      . apply False.elim
        apply hnot
        intro hq
        have hlarge : forall p : Nat, Membership.mem P p -> p < q := by
          intro p hp
          exact (hB p hp).trans_lt (lt_of_not_ge hle)
        exact And.intro (lt_of_not_ge hle)
          (native_prime_vertex_clear_insertion_flat P q hP hflat hq hlarge hc)
      . exact Exists.intro true hc
  have hzero := tendsto_prime_probability_zero_of_imp
    (fun q => Not (Nat.Prime q -> V q)) (fun q => exists b : Bool, E b q)
      hImp (tendsto_prime_probability_finite_union_zero E hEach)
  have hone := tendsto_prime_probability_one_of_complement_zero (fun q => Nat.Prime q -> V q)
    hzero
  refine Filter.Tendsto.congr' (Filter.Eventually.of_forall (fun N => ?_)) hone
  have heq :
      @Finset.filter Nat (fun q => Nat.Prime q -> V q)
        (fun q => Classical.propDecidable (Nat.Prime q -> V q)) (Nat.primesLE N) =
      @Finset.filter Nat V (fun q => Classical.propDecidable (V q)) (Nat.primesLE N) := by
    apply Finset.ext
    intro q
    simp only [Finset.mem_filter]
    constructor
    . intro h
      exact And.intro h.1 (h.2 (Nat.mem_primesLE.mp h.1).2)
    . intro h
      exact And.intro h.1 (fun _ => h.2)
  change primeEventProbability N (fun q => Nat.Prime q -> V q) = primeEventProbability N V
  unfold primeEventProbability
  rw [heq]

theorem exists_native_prime_vertex_extension_above (P : Finset Nat) (B : Nat)
    (hP : forall p : Nat, Membership.mem P p -> Nat.Prime p)
    (hflat : nativePrimeVertexSquareFlat P)
    (hB : forall p : Nat, Membership.mem P p -> p <= B) :
    exists q : Nat, And (Nat.Prime q)
      (And (B < q) (nativePrimeVertexSquareFlat (insert q P))) := by
  have hlim := tendsto_native_prime_vertex_valid_extensions_one P B hP hflat hB
  choose N hN using (hlim.neg.eventually_lt_const (by norm_num : (-1 : Real) < 0)).exists
  let V : Nat -> Prop := fun q => And (B < q) (nativePrimeVertexSquareFlat (insert q P))
  let T : Finset Nat := @Finset.filter Nat V
    (fun q => Classical.propDecidable (V q)) (Nat.primesLE N)
  change -((T.card : Real) / (Nat.primeCounting N : Real)) < 0 at hN
  have hcard : 0 < T.card := by
    by_contra hn
    have hz : T.card = 0 := by omega
    norm_num only [hz, Nat.cast_zero, zero_div, neg_zero, lt_self_iff_false] at hN
  choose q hq using Finset.card_pos.mp hcard
  have hh : And (Membership.mem (Nat.primesLE N) q) (V q) := by
    simpa only [T, Finset.mem_filter] using hq
  exact Exists.intro q (And.intro (Nat.mem_primesLE.mp hh.1).2 hh.2)

end PrimeFactorOscillations.FiniteFieldIntegerSignature

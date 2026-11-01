/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Assembly.FiniteFieldNativeVertexDensity

/-! # Prime-reservoir supply for complete vertex extensions

The full finite rejection union has density zero. The signed supply bound
keeps the reservoir mass and every collision and bounded-cutoff loss.
-/

set_option autoImplicit false
set_option Elab.async false

namespace PrimeFactorOscillations.FiniteFieldIntegerSignature

open scoped Classical
attribute [local instance] Classical.propDecidable

theorem native_prime_vertex_reservoir_supply (P : Finset Nat) (B N : Nat)
    (R : Nat -> Prop)
    (hP : forall p : Nat, Membership.mem P p -> Nat.Prime p)
    (hflat : nativePrimeVertexSquareFlat P)
    (hB : forall p : Nat, Membership.mem P p -> p <= B) :
    primeEventProbability N R -
      primeEventProbability N (fun q => Or (q <= B)
        (Not (nativePrimeVertexExtensionClear P q))) <=
      primeEventProbability N (fun q => And (R q)
        (And (B < q) (nativePrimeVertexSquareFlat (insert q P)))) := by
  let V : Nat -> Prop := fun q => And (B < q) (nativePrimeVertexSquareFlat (insert q P))
  let Bad : Nat -> Prop := fun q => Or (q <= B) (Not (nativePrimeVertexExtensionClear P q))
  let A : Finset Nat := @Finset.filter Nat R
    (fun q => Classical.propDecidable (R q)) (Nat.primesLE N)
  let G : Finset Nat := @Finset.filter Nat (fun q => And (R q) (V q))
    (fun q => Classical.propDecidable (And (R q) (V q))) (Nat.primesLE N)
  let E : Finset Nat := @Finset.filter Nat Bad
    (fun q => Classical.propDecidable (Bad q)) (Nat.primesLE N)
  have hsub : A <= Union.union G E := by
    intro q hq
    have hh : And (Membership.mem (Nat.primesLE N) q) (R q) := by
      simpa only [A, Finset.mem_filter] using hq
    by_cases hle : q <= B
    . apply Finset.mem_union.mpr
      right
      simpa only [E, Finset.mem_filter] using And.intro hh.1 (Or.inl hle : Bad q)
    . by_cases hc : nativePrimeVertexExtensionClear P q
      . have hlarge : forall p : Nat, Membership.mem P p -> p < q := by
          intro p hp
          exact (hB p hp).trans_lt (lt_of_not_ge hle)
        have hv : V q := And.intro (lt_of_not_ge hle)
          (native_prime_vertex_clear_insertion_flat P q hP hflat
            (Nat.mem_primesLE.mp hh.1).2 hlarge hc)
        apply Finset.mem_union.mpr
        left
        simpa only [G, Finset.mem_filter] using And.intro hh.1 (And.intro hh.2 hv)
      . apply Finset.mem_union.mpr
        right
        simpa only [E, Finset.mem_filter] using And.intro hh.1 (Or.inr hc : Bad q)
  have hcard : A.card <= G.card + E.card :=
    (Finset.card_le_card hsub).trans (by apply Finset.card_union_le)
  have hr : (A.card : Real) <= (G.card : Real) + (E.card : Real) := by
    exact_mod_cast hcard
  have hd := div_le_div_of_nonneg_right hr (Nat.cast_nonneg (Nat.primeCounting N) :
    (0 : Real) <= (Nat.primeCounting N : Real))
  rw [add_div] at hd
  change (A.card : Real) / (Nat.primeCounting N : Real) -
    (E.card : Real) / (Nat.primeCounting N : Real) <=
      (G.card : Real) / (Nat.primeCounting N : Real)
  linarith only [hd]

theorem tendsto_native_prime_vertex_rejection_zero (P : Finset Nat) (B : Nat)
    (hP : forall p : Nat, Membership.mem P p -> Nat.Prime p) :
    Filter.Tendsto (fun N : Nat => primeEventProbability N (fun q => Or (q <= B)
      (Not (nativePrimeVertexExtensionClear P q)))) Filter.atTop (nhds 0) := by
  let E : Bool -> Nat -> Prop
    | false, q => q <= B
    | true, q => Not (nativePrimeVertexExtensionClear P q)
  have hEach : forall b : Bool, Filter.Tendsto
      (fun N : Nat => primeEventProbability N (E b)) Filter.atTop (nhds 0) := by
    intro b
    cases b with
    | false => exact tendsto_prime_probability_bounded_zero B
    | true => exact tendsto_native_prime_vertex_unclear_zero P hP
  apply tendsto_prime_probability_zero_of_imp
    (fun q => Or (q <= B) (Not (nativePrimeVertexExtensionClear P q)))
    (fun q => exists b : Bool, E b q)
  . intro q hq
    cases hq with
    | inl h => exact Exists.intro false h
    | inr h => exact Exists.intro true h
  . exact tendsto_prime_probability_finite_union_zero E hEach

theorem exists_native_prime_vertex_reservoir_extension_above
    (R : Nat -> Prop)
    (hR : Not (Filter.Tendsto (fun N : Nat => primeEventProbability N R)
      Filter.atTop (nhds 0)))
    (P : Finset Nat) (B : Nat)
    (hP : forall p : Nat, Membership.mem P p -> Nat.Prime p)
    (hflat : nativePrimeVertexSquareFlat P)
    (hB : forall p : Nat, Membership.mem P p -> p <= B) :
    exists q : Nat, And (Nat.Prime q)
      (And (R q) (And (B < q) (nativePrimeVertexSquareFlat (insert q P)))) := by
  by_contra hnone
  apply hR
  refine squeeze_zero' (Filter.Eventually.of_forall (fun N => ?_)) ?_
    (tendsto_native_prime_vertex_rejection_zero P B hP)
  . unfold primeEventProbability
    exact div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
  . apply Filter.Eventually.of_forall
    intro N
    have hzero : primeEventProbability N (fun q => And (R q)
        (And (B < q) (nativePrimeVertexSquareFlat (insert q P)))) = 0 := by
      let V : Nat -> Prop := fun q => And (R q)
        (And (B < q) (nativePrimeVertexSquareFlat (insert q P)))
      let T : Finset Nat := @Finset.filter Nat V
        (fun q => Classical.propDecidable (V q)) (Nat.primesLE N)
      have hc : T.card = 0 := by
        by_contra hnonzero
        have hpos : 0 < T.card := by omega
        choose q hq using Finset.card_pos.mp hpos
        have hh : And (Membership.mem (Nat.primesLE N) q) (V q) := by
          simpa only [T, Finset.mem_filter] using hq
        apply hnone
        exact Exists.intro q (And.intro (Nat.mem_primesLE.mp hh.1).2 hh.2)
      change (T.card : Real) / (Nat.primeCounting N : Real) = 0
      rw [hc]
      norm_num
    have hsupply := native_prime_vertex_reservoir_supply P B N R hP hflat hB
    rw [hzero] at hsupply
    linarith only [hsupply]

end PrimeFactorOscillations.FiniteFieldIntegerSignature

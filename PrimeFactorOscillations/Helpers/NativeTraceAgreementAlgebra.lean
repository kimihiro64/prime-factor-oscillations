/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.NativeWordBooleanAlgebra

/-! # Coupled zero-trace and simultaneous-agreement selector algebra

The paired zero event keeps both signed rows on each selected edge.
Its expansion retains every supported mask and its cardinality sign.
-/

set_option autoImplicit false
set_option Elab.async false

namespace PrimeFactorOscillations.FiniteFieldIntegerSignature
open scoped Classical
attribute [local instance] Classical.propDecidable

theorem native_trace_zero_selector_product (G : Finset (Prod Nat Nat))
    (x y : Prod Nat Nat -> Real)
    (hx : forall e : Prod Nat Nat, Membership.mem G e -> x e ^ 2 = 1)
    (hy : forall e : Prod Nat Nat, Membership.mem G e -> y e ^ 2 = 1) :
    G.prod (fun e => nativeWordBit false (x e * y e)) =
      if (forall e : Prod Nat Nat, Membership.mem G e -> x e + y e = 0)
        then 1 else 0 := by
  have hxy : forall e : Prod Nat Nat, Membership.mem G e -> (x e * y e) ^ 2 = 1 := by
    intro e he
    rw [mul_pow, hx e he, hy e he, one_mul]
  have hzero : forall e : Prod Nat Nat, Membership.mem G e ->
      (x e + y e = 0 <-> x e * y e = nativeWordSign false) := by
    intro e he
    change x e + y e = 0 <-> x e * y e = -1
    constructor
    . intro h
      have hs : x e = -y e := by linarith only [h]
      rw [hs]
      nlinarith only [hy e he]
    . intro h
      have hs : (x e + y e) * (x e + y e) = 0 := by
        nlinarith only [hx e he, hy e he, h]
      cases mul_eq_zero.mp hs with
      | inl hz => exact hz
      | inr hz => exact hz
  rw [native_word_selector_product G (fun _ => false) (fun e => x e * y e) hxy]
  by_cases hz : forall e : Prod Nat Nat, Membership.mem G e -> x e + y e = 0
  . have hp : forall e : Prod Nat Nat, Membership.mem G e ->
        x e * y e = nativeWordSign false := fun e he => (hzero e he).mp (hz e he)
    rw [ite_eq_left hp, ite_eq_left hz]
  . have hp : Not (forall e : Prod Nat Nat, Membership.mem G e ->
        x e * y e = nativeWordSign false) := by
      intro h
      exact hz (fun e he => (hzero e he).mpr (h e he))
    rw [ite_eq_right hp, ite_eq_right hz]

theorem native_trace_zero_full_mask_expansion (G : Finset (Prod Nat Nat))
    (x y : Prod Nat Nat -> Real) :
    G.prod (fun e => nativeWordBit false (x e * y e)) =
      (1 / (2 : Real) ^ G.card) *
        G.powerset.sum (fun S => (-1 : Real) ^ S.card * (S.prod x * S.prod y)) := by
  have h := native_word_full_mask_expansion G {} (fun _ => false) (fun _ => true)
    (fun e => x e * y e) (fun _ => 1)
  simpa [nativeWordSign, Finset.prod_mul_distrib, Finset.prod_const, mul_assoc] using h

theorem native_trace_agreement_selector_product (G : Finset (Prod Nat Nat))
    (hG : G.Nonempty) (x y : Prod Nat Nat -> Real)
    (hx : forall e : Prod Nat Nat, Membership.mem G e -> x e ^ 2 = 1)
    (hy : forall e : Prod Nat Nat, Membership.mem G e -> y e ^ 2 = 1) :
    (if (forall e : Prod Nat Nat, Membership.mem G e ->
        forall f : Prod Nat Nat, Membership.mem G f -> x e + y e = x f + y f)
      then (1 : Real) else 0) =
      G.prod (fun e => nativeWordBit false (x e * y e)) +
        G.prod (fun e => nativeWordBit true (x e)) *
          G.prod (fun e => nativeWordBit true (y e)) +
        G.prod (fun e => nativeWordBit false (x e)) *
          G.prod (fun e => nativeWordBit false (y e)) := by
  let H : Prop := forall e : Prod Nat Nat, Membership.mem G e ->
    forall f : Prod Nat Nat, Membership.mem G f -> x e + y e = x f + y f
  let Z : Prop := forall e : Prod Nat Nat, Membership.mem G e -> x e + y e = 0
  let P : Prop := And (forall e : Prod Nat Nat, Membership.mem G e -> x e = 1)
    (forall e : Prod Nat Nat, Membership.mem G e -> y e = 1)
  let N : Prop := And (forall e : Prod Nat Nat, Membership.mem G e -> x e = -1)
    (forall e : Prod Nat Nat, Membership.mem G e -> y e = -1)
  choose e he using hG
  have hsplit (z : Real) (hz : z ^ 2 = 1) : Or (z = 1) (z = -1) := by
    have hm : (z - 1) * (z + 1) = 0 := by nlinarith only [hz]
    cases mul_eq_zero.mp hm with
    | inl h => exact Or.inl (by linarith only [h])
    | inr h => exact Or.inr (by linarith only [h])
  have hupper (z : Real) (hz : z ^ 2 = 1) : z <= 1 := by
    nlinarith only [hz, sq_nonneg (z - 1)]
  have hlower (z : Real) (hz : z ^ 2 = 1) : -1 <= z := by
    nlinarith only [hz, sq_nonneg (z + 1)]
  have hchar : H <-> Or Z (Or P N) := by
    constructor
    . intro h
      cases hsplit (x e) (hx e he) with
      | inl hxe =>
        cases hsplit (y e) (hy e he) with
        | inl hye =>
          have hv : forall i : Prod Nat Nat, Membership.mem G i -> And (x i = 1) (y i = 1) := by
            intro i hi
            have ht := h i hi e he
            have hxu := hupper (x i) (hx i hi)
            have hyu := hupper (y i) (hy i hi)
            constructor <;> linarith only [ht, hxe, hye, hxu, hyu]
          exact Or.inr (Or.inl (And.intro (fun i hi => (hv i hi).1)
            (fun i hi => (hv i hi).2)))
        | inr hye =>
          apply Or.inl
          intro i hi
          have ht := h i hi e he
          linarith only [ht, hxe, hye]
      | inr hxe =>
        cases hsplit (y e) (hy e he) with
        | inl hye =>
          apply Or.inl
          intro i hi
          have ht := h i hi e he
          linarith only [ht, hxe, hye]
        | inr hye =>
          have hv : forall i : Prod Nat Nat, Membership.mem G i -> And (x i = -1) (y i = -1) := by
            intro i hi
            have ht := h i hi e he
            have hxl := hlower (x i) (hx i hi)
            have hyl := hlower (y i) (hy i hi)
            constructor <;> linarith only [ht, hxe, hye, hxl, hyl]
          exact Or.inr (Or.inr (And.intro (fun i hi => (hv i hi).1)
            (fun i hi => (hv i hi).2)))
    . intro h
      rcases h with hz | hp | hn
      . intro i hi j hj
        rw [hz i hi, hz j hj]
      . intro i hi j hj
        rw [hp.1 i hi, hp.2 i hi, hp.1 j hj, hp.2 j hj]
      . intro i hi j hj
        rw [hn.1 i hi, hn.2 i hi, hn.1 j hj, hn.2 j hj]
  have hZP : Not (And Z P) := by
    intro h
    have h0 := h.1 e he
    have h1 := h.2.1 e he
    have h2 := h.2.2 e he
    linarith only [h0, h1, h2]
  have hZN : Not (And Z N) := by
    intro h
    have h0 := h.1 e he
    have h1 := h.2.1 e he
    have h2 := h.2.2 e he
    linarith only [h0, h1, h2]
  have hPN : Not (And P N) := by
    intro h
    have h1 := h.1.1 e he
    have h2 := h.2.1 e he
    linarith only [h1, h2]
  have hword (b : Bool) :
      G.prod (fun i => nativeWordBit b (x i)) *
        G.prod (fun i => nativeWordBit b (y i)) =
        if And (forall i : Prod Nat Nat, Membership.mem G i -> x i = nativeWordSign b)
          (forall i : Prod Nat Nat, Membership.mem G i -> y i = nativeWordSign b)
          then 1 else 0 := by
    rw [native_word_selector_product G (fun _ => b) x hx,
      native_word_selector_product G (fun _ => b) y hy]
    by_cases ha : forall i : Prod Nat Nat, Membership.mem G i -> x i = nativeWordSign b
    . by_cases hb : forall i : Prod Nat Nat, Membership.mem G i -> y i = nativeWordSign b
      . rw [ite_eq_left ha, ite_eq_left hb, ite_eq_left (And.intro ha hb), one_mul]
      . have hn : Not (And (forall i : Prod Nat Nat, Membership.mem G i -> x i = nativeWordSign b)
            (forall i : Prod Nat Nat, Membership.mem G i -> y i = nativeWordSign b)) :=
          fun h => hb h.2
        rw [ite_eq_left ha, ite_eq_right hb, ite_eq_right hn, mul_zero]
    . have hn : Not (And (forall i : Prod Nat Nat, Membership.mem G i -> x i = nativeWordSign b)
          (forall i : Prod Nat Nat, Membership.mem G i -> y i = nativeWordSign b)) :=
        fun h => ha h.1
      rw [ite_eq_right ha, ite_eq_right hn, zero_mul]
  rw [native_trace_zero_selector_product G x y hx hy, hword true, hword false]
  change (if H then (1 : Real) else 0) =
    (if Z then 1 else 0) + (if P then 1 else 0) + (if N then 1 else 0)
  by_cases hz : Z
  . have hp : Not P := fun h => hZP (And.intro hz h)
    have hn : Not N := fun h => hZN (And.intro hz h)
    have hh : H := hchar.mpr (Or.inl hz)
    norm_num only [ite_eq_left hh, ite_eq_left hz, ite_eq_right hp, ite_eq_right hn]
  . by_cases hp : P
    . have hn : Not N := fun h => hPN (And.intro hp h)
      have hh : H := hchar.mpr (Or.inr (Or.inl hp))
      norm_num only [ite_eq_left hh, ite_eq_right hz, ite_eq_left hp, ite_eq_right hn]
    . by_cases hn : N
      . have hh : H := hchar.mpr (Or.inr (Or.inr hn))
        norm_num only [ite_eq_left hh, ite_eq_right hz, ite_eq_right hp, ite_eq_left hn]
      . have hh : Not H := by
          intro h
          rcases hchar.mp h with h0 | h0 | h0
          . exact hz h0
          . exact hp h0
          . exact hn h0
        norm_num only [ite_eq_right hh, ite_eq_right hz, ite_eq_right hp, ite_eq_right hn]

end PrimeFactorOscillations.FiniteFieldIntegerSignature

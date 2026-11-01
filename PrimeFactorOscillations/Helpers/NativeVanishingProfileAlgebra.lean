/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.NativeWordBooleanAlgebra

/-! # Exact Boolean selectors for paired zero and nonzero trace profiles -/

set_option autoImplicit false
set_option Elab.async false

noncomputable section
namespace PrimeFactorOscillations.FiniteFieldIntegerSignature

theorem native_trace_zero_iff_paired_negative (x y : Real)
    (hx : x ^ 2 = 1) (hy : y ^ 2 = 1) :
    x + y = 0 <-> x * y = -1 := by
  constructor
  . intro h
    have hs : (x + y) ^ 2 = 0 := by rw [h]; norm_num
    nlinarith only [hx, hy, hs]
  . intro h
    have hs : (x + y) ^ 2 = 0 := by nlinarith only [hx, hy, h]
    rw [pow_two] at hs
    rcases mul_eq_zero.mp hs with hz | hz
    . exact hz
    . exact hz

theorem native_trace_status_iff_paired_sign (b : Bool) (x y : Real)
    (hx : x ^ 2 = 1) (hy : y ^ 2 = 1) :
    (if b then Not (x + y = 0) else x + y = 0) <->
      x * y = nativeWordSign b := by
  cases b with
  | false =>
    exact native_trace_zero_iff_paired_negative x y hx hy
  | true =>
    change Not (x + y = 0) <-> x * y = 1
    constructor
    . intro hn
      have hp : (x * y) ^ 2 = 1 := by rw [mul_pow, hx, hy]; norm_num
      have hz : (x * y - 1) * (x * y + 1) = 0 := by nlinarith only [hp]
      rcases mul_eq_zero.mp hz with h | h
      . linarith only [h]
      . exact False.elim (hn ((native_trace_zero_iff_paired_negative x y hx hy).mpr
          (by linarith only [h])))
    . intro hp hz
      have hn := (native_trace_zero_iff_paired_negative x y hx hy).mp hz
      linarith only [hp, hn]

theorem native_paired_profile_selector (G : Finset (Prod Nat Nat))
    (a : Prod Nat Nat -> Bool) (x y : Prod Nat Nat -> Real)
    (hx : forall e : Prod Nat Nat, Membership.mem G e -> x e ^ 2 = 1)
    (hy : forall e : Prod Nat Nat, Membership.mem G e -> y e ^ 2 = 1) :
    G.prod (fun e => nativeWordBit (a e) (x e * y e)) =
      if (forall e : Prod Nat Nat, Membership.mem G e ->
        if a e then Not (x e + y e = 0) else x e + y e = 0) then 1 else 0 := by
  classical
  have hr : forall e : Prod Nat Nat, Membership.mem G e -> (x e * y e) ^ 2 = 1 := by
    intro e he
    rw [mul_pow, hx e he, hy e he]
    norm_num
  rw [native_word_selector_product G a (fun e => x e * y e) hr]
  have hi : (forall e : Prod Nat Nat, Membership.mem G e ->
      x e * y e = nativeWordSign (a e)) <->
      (forall e : Prod Nat Nat, Membership.mem G e ->
        if a e then Not (x e + y e = 0) else x e + y e = 0) := by
    constructor
    . intro h e he
      exact (native_trace_status_iff_paired_sign (a e) (x e) (y e)
        (hx e he) (hy e he)).mpr (h e he)
    . intro h e he
      exact (native_trace_status_iff_paired_sign (a e) (x e) (y e)
        (hx e he) (hy e he)).mp (h e he)
  by_cases h : (forall e : Prod Nat Nat, Membership.mem G e ->
      if a e then Not (x e + y e = 0) else x e + y e = 0)
  . rw [ite_eq_left h, ite_eq_left (hi.mpr h)]
  . have hn : Not (forall e : Prod Nat Nat, Membership.mem G e ->
        x e * y e = nativeWordSign (a e)) := fun hs => h (hi.mp hs)
    rw [ite_eq_right h, ite_eq_right hn]

theorem native_paired_profile_full_mask_expansion (G : Finset (Prod Nat Nat))
    (a : Prod Nat Nat -> Bool) (x y : Prod Nat Nat -> Real) :
    G.prod (fun e => nativeWordBit (a e) (x e * y e)) =
      (1 / (2 : Real) ^ G.card) *
        G.powerset.sum (fun C =>
          C.prod (fun e => nativeWordSign (a e)) * (C.prod x * C.prod y)) := by
  have h := native_word_full_mask_expansion G {} a (fun _ => true)
    (fun e => x e * y e) (fun _ => 1)
  simpa only [Finset.prod_empty, mul_one, one_mul, Finset.card_empty, Nat.add_zero,
    Finset.powerset_empty, Finset.sum_singleton, Finset.prod_mul_distrib, mul_assoc] using h

end PrimeFactorOscillations.FiniteFieldIntegerSignature

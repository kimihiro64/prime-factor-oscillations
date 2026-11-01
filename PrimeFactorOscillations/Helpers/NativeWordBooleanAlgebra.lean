/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import PrimeFactorOscillations.Definitions.NativePrimeWordSigns

/-! # Complete Boolean selector algebra for native row words

The expansion retains every pair of finite masks. Pointwise Boolean
interpretation requires the actual character values to have square one.
-/

set_option autoImplicit false
set_option Elab.async false

namespace PrimeFactorOscillations.FiniteFieldIntegerSignature

open scoped Classical
attribute [local instance] Classical.propDecidable

theorem native_word_sign_square (b : Bool) : nativeWordSign b ^ 2 = 1 := by
  cases b <;> norm_num [nativeWordSign]

theorem native_word_bit_eq_indicator (b : Bool) (x : Real) (hx : x ^ 2 = 1) :
    nativeWordBit b x = if x = nativeWordSign b then 1 else 0 := by
  have hsplit : Or (x = 1) (x = -1) := by
    have hz : (x - 1) * (x + 1) = 0 := by nlinarith only [hx]
    cases mul_eq_zero.mp hz with
    | inl h => exact Or.inl (by linarith only [h])
    | inr h => exact Or.inr (by linarith only [h])
  cases hsplit with
  | inl h =>
    subst x
    cases b <;> norm_num [nativeWordBit, nativeWordSign]
  | inr h =>
    subst x
    cases b <;> norm_num [nativeWordBit, nativeWordSign]

theorem native_word_selector_product (A : Finset (Prod Nat Nat))
    (a : Prod Nat Nat -> Bool) (x : Prod Nat Nat -> Real)
    (hx : forall e : Prod Nat Nat, Membership.mem A e -> x e ^ 2 = 1) :
    A.prod (fun e => nativeWordBit (a e) (x e)) =
      if (forall e : Prod Nat Nat, Membership.mem A e -> x e = nativeWordSign (a e))
        then 1 else 0 := by
  induction A using Finset.induction_on with
  | empty => simp
  | @insert e A he ih =>
    have hxe := hx e (Finset.mem_insert_self e A)
    have hrest := ih (fun i hi => hx i (Finset.mem_insert_of_mem hi))
    rw [Finset.prod_insert he, native_word_bit_eq_indicator (a e) (x e) hxe, hrest]
    by_cases hsign : x e = nativeWordSign (a e) <;> simp [hsign]

theorem native_word_full_mask_expansion (A B : Finset (Prod Nat Nat))
    (a b : Prod Nat Nat -> Bool) (x y : Prod Nat Nat -> Real) :
    A.prod (fun e => nativeWordBit (a e) (x e)) *
        B.prod (fun e => nativeWordBit (b e) (y e)) =
      (1 / (2 : Real) ^ (A.card + B.card)) *
        A.powerset.sum (fun O => B.powerset.sum (fun T =>
          O.prod (fun e => nativeWordSign (a e)) * T.prod (fun e => nativeWordSign (b e)) *
            O.prod x * T.prod y)) := by
  have hdouble :
      A.powerset.sum (fun O => O.prod (fun e => nativeWordSign (a e) * x e)) *
        B.powerset.sum (fun T => T.prod (fun e => nativeWordSign (b e) * y e)) =
      A.powerset.sum (fun O => B.powerset.sum (fun T =>
        O.prod (fun e => nativeWordSign (a e)) * T.prod (fun e => nativeWordSign (b e)) *
          O.prod x * T.prod y)) := by
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro O _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro T _
    rw [Finset.prod_mul_distrib, Finset.prod_mul_distrib]
    ring
  unfold nativeWordBit
  rw [Finset.prod_div_distrib, Finset.prod_div_distrib, Finset.prod_const,
    Finset.prod_const, div_mul_div_comm]
  rw [Finset.prod_one_add, Finset.prod_one_add, hdouble, <- pow_add]
  ring

end PrimeFactorOscillations.FiniteFieldIntegerSignature

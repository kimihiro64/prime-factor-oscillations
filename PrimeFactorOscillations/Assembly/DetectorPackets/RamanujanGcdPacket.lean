/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/

import PrimeFactorOscillations.Assembly.DetectorPackets.QuarticPowerfulPacket

/-!
# RamanujanGcdPacket

Maintained extraction of completed detector/packet proof components.
All original theorem hypotheses and retained proof bodies are preserved.
This module alone asserts no improved zero-free boundary.
-/

set_option autoImplicit false
set_option Elab.async false

/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/

/-!
# Exact squarefree Ramanujan factors

The predicate b selects the divisor primes shared with the frequency.
Every complement remains inside the displayed finite support S.
The modulus gain is cross-multiplied; no zero denominator is hidden.
-/


noncomputable section
namespace PrimeFactorOscillations.RamanujanGcdPacket

theorem signed_split {I : Type} (S : Finset I) (q : I -> Real)
    (b : I -> Prop) [DecidablePred b] :
    (S.prod (fun p => if b p then q p - 1 else -1)) =
      (-1) ^ ((S.filter (fun p => Not (b p))).card) *
        (S.filter b).prod (fun p => q p - 1) := by
  classical
  induction S using Finset.induction_on with
  | empty => simp
  | @insert p S hp ih =>
    by_cases hb : b p
    . simp [hp, hb, Finset.filter_insert, ih] <;> ring
    . simp [hp, hb, Finset.filter_insert, ih, pow_succ] <;> ring

theorem product_partition {I : Type} (S : Finset I) (q : I -> Real)
    (b : I -> Prop) [DecidablePred b] :
    S.prod q = (S.filter b).prod q *
      (S.filter (fun p => Not (b p))).prod q := by
  classical
  induction S using Finset.induction_on with
  | empty => simp
  | @insert p S hp ih =>
    by_cases hb : b p
    . simp [hp, hb, Finset.filter_insert, ih]
      ring
    . simp [hp, hb, Finset.filter_insert, ih]
      ring

theorem absolute_selected_bound {I : Type} (S : Finset I) (q : I -> Real)
    (b : I -> Prop) [DecidablePred b]
    (hq : forall p, Membership.mem S p -> 1 <= q p) :
    abs (S.prod (fun p => if b p then q p - 1 else -1)) <=
      (S.filter b).prod q := by
  have hnonneg : 0 <= (S.filter b).prod (fun p => q p - 1) := by
    apply Finset.prod_nonneg
    intro p hp
    exact sub_nonneg.mpr (hq p (Finset.mem_filter.mp hp).1)
  rw [signed_split S q b, abs_mul, abs_pow, abs_neg, abs_one,
    one_pow, one_mul, abs_of_nonneg hnonneg]
  suffices h : forall U : Finset I,
      (forall p, Membership.mem U p -> 1 <= q p) ->
      U.prod (fun p => q p - 1) <= U.prod q by
    exact h (S.filter b) (fun p hp => hq p (Finset.mem_filter.mp hp).1)
  intro U
  classical
  induction U using Finset.induction_on with
  | empty => intro h; simp
  | @insert p U hp ih =>
    intro h
    have hqp : 1 <= q p := h p (by simp)
    have hU : forall k, Membership.mem U k -> 1 <= q k :=
      fun k hk => h k (Finset.mem_insert_of_mem hk)
    have hn : 0 <= U.prod (fun k => q k - 1) :=
      Finset.prod_nonneg (fun k hk => sub_nonneg.mpr (hU k hk))
    simp only [Finset.prod_insert hp]
    exact mul_le_mul (sub_le_self (q p) zero_le_one) (ih hU) hn
      (le_trans zero_le_one hqp)

theorem complementary_modulus_positive {I : Type} (S : Finset I) (q : I -> Real)
    (b : I -> Prop) [DecidablePred b]
    (hq : forall p, Membership.mem S p -> 1 <= q p) :
    0 < (S.filter (fun p => Not (b p))).prod q := by
  apply Finset.prod_pos
  intro p hp
  exact lt_of_lt_of_le zero_lt_one (hq p (Finset.mem_filter.mp hp).1)

theorem nonshared_modulus_gain {I : Type} (S : Finset I) (q : I -> Real)
    (b : I -> Prop) [DecidablePred b]
    (hq : forall p, Membership.mem S p -> 1 <= q p) :
    abs (S.prod (fun p => if b p then q p - 1 else -1)) *
      (S.filter (fun p => Not (b p))).prod q <= S.prod q := by
  have hpos := complementary_modulus_positive S q b hq
  calc
    abs (S.prod (fun p => if b p then q p - 1 else -1)) *
        (S.filter (fun p => Not (b p))).prod q <=
      (S.filter b).prod q * (S.filter (fun p => Not (b p))).prod q :=
        mul_le_mul_of_nonneg_right (absolute_selected_bound S q b hq) hpos.le
    _ = S.prod q := (product_partition S q b).symm

theorem quartic_phase_period (z : Complex) (hz : z ^ 4 = 1) (j : Nat) :
    z ^ j = z ^ (j % 4) := by
  have he : j = j % 4 + 4 * (j / 4) := (Nat.mod_add_div j 4).symm
  calc
    z ^ j = z ^ (j % 4 + 4 * (j / 4)) := congrArg (fun n : Nat => z ^ n) he
    _ = z ^ (j % 4) := by rw [pow_add, pow_mul, hz, one_pow, mul_one]

end PrimeFactorOscillations.RamanujanGcdPacket

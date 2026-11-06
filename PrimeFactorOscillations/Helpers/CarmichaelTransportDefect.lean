/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Field.GeomSum
import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Finite signed transport defects

An injective transport with finite escape depth controls the total covered
mass by the complete nonnegative deficit. This is the finite summation input
for the two-power zero-carrier application, not a zero-free theorem.
-/

set_option autoImplicit false
set_option Elab.async false

noncomputable section

namespace PrimeFactorOscillations.CarmichaelStripCarrier

def transportIter {alpha : Type*} (M : alpha -> alpha) : Nat -> alpha -> alpha
  | 0 => id
  | n + 1 => fun x => M (transportIter M n x)

theorem transportIter_injective {alpha : Type*} (M : alpha -> alpha)
    (hM : Function.Injective M) (n : Nat) :
    Function.Injective (transportIter M n) := by
  induction n with
  | zero => exact Function.injective_id
  | succ n ih => exact hM.comp ih

theorem finite_support_comp_sum_le {alpha : Type*} [DecidableEq alpha]
    (S : Finset alpha) (f : alpha -> Real) (g : alpha -> alpha)
    (hf : forall x, 0 <= f x)
    (hSupport : forall x, Not (Membership.mem S x) -> f x = 0)
    (hg : Function.Injective g) :
    S.sum (fun x => f (g x)) <= S.sum f := by
  have hUnion : S.sum f = (Union.union S (S.image g)).sum f := by
    apply Finset.sum_subset Finset.subset_union_left
    intro x hx hNot
    exact hSupport x hNot
  calc
    S.sum (fun x => f (g x)) <= (Union.union S (S.image g)).sum f := by
      apply Finset.sum_le_sum_of_injOn g
      . intro x hx y hy heq
        exact hg heq
      . exact Finset.subset_union_right
      . intro x hx
        exact le_rfl
      . intro x hx hNot
        exact hf x
    _ = S.sum f := hUnion.symm

theorem signed_transport_iter_bound {alpha : Type*}
    (M : alpha -> alpha) (b D : alpha -> Real) (r : Real) (hr : 0 <= r)
    (hStep : forall x, b x <= D x + r * b (M x)) (n : Nat) (x : alpha) :
    b x <= (Finset.range n).sum (fun j => r ^ j * D (transportIter M j x)) +
      r ^ n * b (transportIter M n x) := by
  induction n with
  | zero => simp [transportIter]
  | succ n ih =>
    have hLast := mul_le_mul_of_nonneg_left (hStep (transportIter M n x))
      (pow_nonneg hr n)
    calc
      b x <= (Finset.range n).sum (fun j => r ^ j * D (transportIter M j x)) +
          r ^ n * b (transportIter M n x) := ih
      _ <= (Finset.range n).sum (fun j => r ^ j * D (transportIter M j x)) +
          r ^ n * (D (transportIter M n x) + r * b (M (transportIter M n x))) :=
        add_le_add le_rfl hLast
      _ = (Finset.range (n + 1)).sum
          (fun j => r ^ j * D (transportIter M j x)) +
          r ^ (n + 1) * b (transportIter M (n + 1) x) := by
        rw [Finset.sum_range_succ]
        simp only [transportIter, pow_succ]
        ring

theorem finite_nilpotent_transport_mass_defect {alpha : Type*} [DecidableEq alpha]
    (S : Finset alpha) (M : alpha -> alpha) (hM : Function.Injective M)
    (b c : alpha -> Real) (r : Real) (hr : 0 <= r)
    (hcb : forall x, c x <= b x)
    (hbSupport : forall x, Not (Membership.mem S x) -> b x = 0)
    (hcSupport : forall x, Not (Membership.mem S x) -> c x = 0)
    (hTransport : forall x, c x <= r * b (M x))
    (L : Nat) (hNilpotent : forall x, Membership.mem S x ->
      b (transportIter M L x) = 0) :
    S.sum b <= (Finset.range L).sum (fun j => r ^ j) * (S.sum b - S.sum c) := by
  let D : alpha -> Real := fun x => b x - c x
  have hD : forall x, 0 <= D x := fun x => sub_nonneg.mpr (hcb x)
  have hDSupport : forall x, Not (Membership.mem S x) -> D x = 0 := by
    intro x hx
    simp only [D, hbSupport x hx, hcSupport x hx, sub_self]
  have hStep : forall x, b x <= D x + r * b (M x) := by
    intro x
    have h := hTransport x
    dsimp [D]
    linarith
  have hPoint : forall x, Membership.mem S x ->
      b x <= (Finset.range L).sum (fun j => r ^ j * D (transportIter M j x)) := by
    intro x hx
    have h := signed_transport_iter_bound M b D r hr hStep L x
    simpa only [hNilpotent x hx, mul_zero, add_zero] using h
  calc
    S.sum b <= S.sum (fun x =>
        (Finset.range L).sum (fun j => r ^ j * D (transportIter M j x))) :=
      Finset.sum_le_sum hPoint
    _ = (Finset.range L).sum (fun j => r ^ j *
        S.sum (fun x => D (transportIter M j x))) := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro j hj
      rw [Finset.mul_sum]
    _ <= (Finset.range L).sum (fun j => r ^ j * S.sum D) := by
      apply Finset.sum_le_sum
      intro j hj
      exact mul_le_mul_of_nonneg_left
        (finite_support_comp_sum_le S D (transportIter M j) hD hDSupport
          (transportIter_injective M hM j)) (pow_nonneg hr j)
    _ = (Finset.range L).sum (fun j => r ^ j) * (S.sum b - S.sum c) := by
      rw [Finset.sum_mul, <- Finset.sum_sub_distrib]

theorem finite_nilpotent_transport_covered_mass {alpha : Type*} [DecidableEq alpha]
    (S : Finset alpha) (M : alpha -> alpha) (hM : Function.Injective M)
    (b c : alpha -> Real) (r : Real) (hr : 0 <= r)
    (hcb : forall x, c x <= b x)
    (hbSupport : forall x, Not (Membership.mem S x) -> b x = 0)
    (hcSupport : forall x, Not (Membership.mem S x) -> c x = 0)
    (hTransport : forall x, c x <= r * b (M x))
    (L : Nat) (hNilpotent : forall x, Membership.mem S x ->
      b (transportIter M L x) = 0)
    (hH : 0 < (Finset.range L).sum (fun j => r ^ j)) :
    S.sum c <= (1 - 1 / (Finset.range L).sum (fun j => r ^ j)) * S.sum b := by
  let H := (Finset.range L).sum (fun j => r ^ j)
  have hH' : 0 < H := hH
  have h := finite_nilpotent_transport_mass_defect S M hM b c r hr hcb
    hbSupport hcSupport hTransport L hNilpotent
  change S.sum b <= H * (S.sum b - S.sum c) at h
  change S.sum c <= (1 - 1 / H) * S.sum b
  have hCancel : H * ((1 - 1 / H) * S.sum b) = (H - 1) * S.sum b := by
    field_simp
  by_contra hNot
  have hlt : (1 - 1 / H) * S.sum b < S.sum c := lt_of_not_ge hNot
  have hmul := mul_lt_mul_of_pos_left hlt hH'
  rw [hCancel] at hmul
  nlinarith only [h, hmul]

end PrimeFactorOscillations.CarmichaelStripCarrier

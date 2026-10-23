/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import Mathlib.Algebra.Group.Subgroup.Ker
import Mathlib.Basic.Real.Basic
import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Tactic.FieldSimp

/-!
# Uniform finite-group sampling through a surjective homomorphism

The exact fiber equivalence retains the full kernel multiplicity. This is
used by the prime-order return law to sample all modular unit bases, not
only powers of one chosen base or uniformly sampled scalar indices.
-/

set_option autoImplicit false
set_option Elab.async false

noncomputable section

namespace PrimeFactorOscillations.FiniteHomProbability

variable {G H : Type*} [Group G] [Group H]

/-- Uniform counting probability on a finite type, written without a measure. -/
def uniformProbability {A : Type*} (P : A -> Prop) : Real :=
  (Nat.card {a : A // P a} : Real) / (Nat.card A : Real)

/-- Each allowed output has one complete translated copy of the kernel. -/
def preimageEquivKernelProduct (f : MonoidHom G H) (hf : Function.Surjective f)
    (P : H -> Prop) :
    Equiv {g : G // P (f g)} (Prod {h : H // P h} f.ker) := by
  classical
  choose s hs using hf
  refine
    { toFun := fun x =>
        Prod.mk (Subtype.mk (f x.val) x.property)
          (Subtype.mk (x.val * (s (f x.val)) ^ (-1 : Int)) ?_)
      invFun := fun y => Subtype.mk (y.2.val * s y.1.val) ?_
      left_inv := ?_
      right_inv := ?_ }
  { change f (x.val * (s (f x.val)) ^ (-1 : Int)) = 1
    rw [map_mul, map_zpow, hs, zpow_neg_one, mul_inv_cancel] }
  { change P (f (y.2.val * s y.1.val))
    have hy : f y.2.val = 1 := y.2.property
    simpa only [map_mul, hy, hs, one_mul] using y.1.property }
  { intro x
    apply Subtype.ext
    change (x.val * (s (f x.val)) ^ (-1 : Int)) * s (f x.val) = x.val
    simp }
  { intro y
    apply Prod.ext
    { apply Subtype.ext
      change f (y.2.val * s y.1.val) = y.1.val
      have hy : f y.2.val = 1 := y.2.property
      rw [map_mul, hy, hs, one_mul] }
    { apply Subtype.ext
      change (y.2.val * s y.1.val) *
        (s (f (y.2.val * s y.1.val))) ^ (-1 : Int) = y.2.val
      have hy : f y.2.val = 1 := y.2.property
      rw [map_mul, hy, hs, one_mul]
      simp } }

/-- Exact preimage cardinality, with no division or discarded multiplicity. -/
theorem preimage_card (f : MonoidHom G H) (hf : Function.Surjective f) (P : H -> Prop) :
    Nat.card {g : G // P (f g)} = Nat.card {h : H // P h} * Nat.card f.ker := by
  rw [Nat.card_congr (preimageEquivKernelProduct f hf P), Nat.card_prod]

/-- The same decomposition for the entire source group. -/
theorem source_card (f : MonoidHom G H) (hf : Function.Surjective f) :
    Nat.card G = Nat.card H * Nat.card f.ker := by
  let eG : Equiv {g : G // True} G :=
    { toFun := Subtype.val
      invFun := fun g => Subtype.mk g True.intro
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  let eH : Equiv {h : H // True} H :=
    { toFun := Subtype.val
      invFun := fun h => Subtype.mk h True.intro
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  have h := preimage_card f hf (fun _ => True)
  rw [Nat.card_congr eG, Nat.card_congr eH] at h
  exact h

/-- Uniform sampling pushes forward uniformly, including every signed pattern. -/
theorem uniformProbability_preimage [Fintype G] [Fintype H]
    (f : MonoidHom G H) (hf : Function.Surjective f) (P : H -> Prop) :
    uniformProbability (fun g : G => P (f g)) = uniformProbability P := by
  classical
  have hk : Not ((Nat.card f.ker : Real) = 0) := by
    have h : 0 < Nat.card f.ker := by
      rw [Nat.card_eq_fintype_card]
      exact Fintype.card_pos_iff.mpr (Nonempty.intro 1)
    exact_mod_cast (Nat.ne_of_gt h)
  have hh : Not ((Nat.card H : Real) = 0) := by
    have h : 0 < Nat.card H := by
      rw [Nat.card_eq_fintype_card]
      exact Fintype.card_pos_iff.mpr (Nonempty.intro 1)
    exact_mod_cast (Nat.ne_of_gt h)
  unfold uniformProbability
  rw [preimage_card f hf P, source_card f hf, Nat.cast_mul, Nat.cast_mul]
  field_simp

end PrimeFactorOscillations.FiniteHomProbability

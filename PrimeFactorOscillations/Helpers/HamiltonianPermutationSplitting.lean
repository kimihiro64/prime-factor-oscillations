/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.HamiltonianOrbitSigns
import PrimeFactorOscillations.Helpers.HamiltonianPermanentLaplace

/-! # Exact complementary permutation splitting

Permutations on a finite set and its complement are equivalent to a full
permutation preserving that set. Every matrix-product factor is retained
under this equivalence, in the actual row orientation of the permanent.
-/

set_option autoImplicit false
set_option Elab.async false

noncomputable section

namespace PrimeFactorOscillations

variable {Iota R : Type*} [Fintype Iota] [DecidableEq Iota]

def hamiltonianSplitPermutation (S : Finset Iota)
    (a : Equiv.Perm {x : Iota // Membership.mem S x})
    (b : Equiv.Perm {x : Iota // Not (Membership.mem S x)}) : Equiv.Perm Iota :=
  Equiv.Perm.ofSubtype a * Equiv.Perm.ofSubtype b

theorem hamiltonianSplitPermutation_invariant (S : Finset Iota)
    (a : Equiv.Perm {x : Iota // Membership.mem S x})
    (b : Equiv.Perm {x : Iota // Not (Membership.mem S x)}) :
    hamiltonianPermutationInvariant (hamiltonianSplitPermutation S a b) S := by
  classical
  intro x
  rw [hamiltonianSplitPermutation, Equiv.Perm.mul_apply,
    Equiv.Perm.ofSubtype_apply_mem_iff_mem a]
  simpa only [not_not] using
    not_congr (Equiv.Perm.ofSubtype_apply_mem_iff_mem b x)

theorem hamiltonianSplitPermutation_apply_mem (S : Finset Iota)
    (a : Equiv.Perm {x : Iota // Membership.mem S x})
    (b : Equiv.Perm {x : Iota // Not (Membership.mem S x)})
    (x : Iota) (hx : Membership.mem S x) :
    hamiltonianSplitPermutation S a b x = (a (Subtype.mk x hx)).val := by
  classical
  rw [hamiltonianSplitPermutation, Equiv.Perm.mul_apply,
    Equiv.Perm.ofSubtype_apply_of_not_mem b (not_not_intro hx),
    Equiv.Perm.ofSubtype_apply_of_mem a hx]

theorem hamiltonianSplitPermutation_apply_not_mem (S : Finset Iota)
    (a : Equiv.Perm {x : Iota // Membership.mem S x})
    (b : Equiv.Perm {x : Iota // Not (Membership.mem S x)})
    (x : Iota) (hx : Not (Membership.mem S x)) :
    hamiltonianSplitPermutation S a b x = (b (Subtype.mk x hx)).val := by
  classical
  have hb : Not (Membership.mem S (Equiv.Perm.ofSubtype b x)) :=
    (Equiv.Perm.ofSubtype_apply_mem_iff_mem b x).mpr hx
  rw [hamiltonianSplitPermutation, Equiv.Perm.mul_apply,
    Equiv.Perm.ofSubtype_apply_of_not_mem a hb,
    Equiv.Perm.ofSubtype_apply_of_mem b hx]

theorem hamiltonianSplitPermutation_restrict_mem (S : Finset Iota)
    (a : Equiv.Perm {x : Iota // Membership.mem S x})
    (b : Equiv.Perm {x : Iota // Not (Membership.mem S x)}) :
    Equiv.Perm.subtypePerm (hamiltonianSplitPermutation S a b)
        (p := fun x => Membership.mem S x)
        (hamiltonianSplitPermutation_invariant S a b) = a := by
  classical
  apply Equiv.ext
  intro x
  apply Subtype.ext
  exact hamiltonianSplitPermutation_apply_mem S a b x.val x.property

theorem hamiltonianSplitPermutation_restrict_not_mem (S : Finset Iota)
    (a : Equiv.Perm {x : Iota // Membership.mem S x})
    (b : Equiv.Perm {x : Iota // Not (Membership.mem S x)}) :
    Equiv.Perm.subtypePerm (hamiltonianSplitPermutation S a b)
        (p := fun x => Not (Membership.mem S x))
        (fun x => not_congr (hamiltonianSplitPermutation_invariant S a b x)) = b := by
  classical
  apply Equiv.ext
  intro x
  apply Subtype.ext
  exact hamiltonianSplitPermutation_apply_not_mem S a b x.val x.property

theorem hamiltonianSplitPermutation_restrictions (S : Finset Iota)
    (f : Equiv.Perm Iota) (hS : hamiltonianPermutationInvariant f S) :
    hamiltonianSplitPermutation S
      (Equiv.Perm.subtypePerm f (p := fun x => Membership.mem S x) hS)
      (Equiv.Perm.subtypePerm f (p := fun x => Not (Membership.mem S x))
        (fun x => not_congr (hS x))) = f := by
  classical
  apply Equiv.ext
  intro x
  by_cases hx : Membership.mem S x
  next =>
    rw [hamiltonianSplitPermutation_apply_mem S _ _ x hx]
    rfl
  next =>
    rw [hamiltonianSplitPermutation_apply_not_mem S _ _ x hx]
    rfl

def hamiltonianSplitPermutationEquiv (S : Finset Iota) :
    Equiv
      (Prod (Equiv.Perm {x : Iota // Membership.mem S x})
        (Equiv.Perm {x : Iota // Not (Membership.mem S x)}))
      {f : Equiv.Perm Iota // hamiltonianPermutationInvariant f S} := by
  classical
  exact {
    toFun := fun p => Subtype.mk (hamiltonianSplitPermutation S p.1 p.2)
      (hamiltonianSplitPermutation_invariant S p.1 p.2)
    invFun := fun f =>
      (Equiv.Perm.subtypePerm f.val (p := fun x => Membership.mem S x) f.property,
        Equiv.Perm.subtypePerm f.val (p := fun x => Not (Membership.mem S x))
          (fun x => not_congr (f.property x)))
    left_inv := by
      intro p
      apply Prod.ext
      next => exact hamiltonianSplitPermutation_restrict_mem S p.1 p.2
      next => exact hamiltonianSplitPermutation_restrict_not_mem S p.1 p.2
    right_inv := by
      intro f
      apply Subtype.ext
      exact hamiltonianSplitPermutation_restrictions S f.val f.property }

theorem hamiltonianSplitPermutation_weight [CommMonoid R]
    (M : Matrix Iota Iota R) (S : Finset Iota)
    (a : Equiv.Perm {x : Iota // Membership.mem S x})
    (b : Equiv.Perm {x : Iota // Not (Membership.mem S x)}) :
    Finset.prod Finset.univ (fun i => M (hamiltonianSplitPermutation S a b i) i) =
      Finset.prod Finset.univ (fun i : {x : Iota // Membership.mem S x} => M (a i).val i.val) *
      Finset.prod Finset.univ
        (fun i : {x : Iota // Not (Membership.mem S x)} => M (b i).val i.val) := by
  classical
  rw [<- Fintype.prod_subtype_mul_prod_subtype (fun x => Membership.mem S x)
    (fun i => M (hamiltonianSplitPermutation S a b i) i)]
  congr 1
  next =>
    apply Finset.prod_congr (by apply Finset.ext; intro i; simp only [Finset.mem_univ])
    intro i hi
    rw [hamiltonianSplitPermutation_apply_mem S a b i.val i.property]
  next =>
    apply Finset.prod_congr (by apply Finset.ext; intro i; simp only [Finset.mem_univ])
    intro i hi
    rw [hamiltonianSplitPermutation_apply_not_mem S a b i.val i.property]

end PrimeFactorOscillations

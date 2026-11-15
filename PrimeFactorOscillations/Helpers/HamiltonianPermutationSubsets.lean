/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.HamiltonianPermanentLaplace

/-! # Supported permutation recursion with every completion retained

Removing a selected column and its image gives an exact recursion for
restricted permutation products. The support loses one element, so the
factorial completion weight is unchanged on every contraction branch.
-/

set_option autoImplicit false
set_option Elab.async false

noncomputable section

namespace PrimeFactorOscillations

def finDeleteEmbedding {n : Nat} (i : Fin (n + 1)) :
    Function.Embedding (Fin n) (Fin (n + 1)) where
  toFun k := Equiv.swap 0 i k.succ
  inj' _ _ h := Fin.succ_injective _ ((Equiv.swap 0 i).injective h)

@[simp] theorem finDeleteEmbedding_apply {n : Nat} (i : Fin (n + 1)) (k : Fin n) :
    finDeleteEmbedding i k = Equiv.swap 0 i k.succ := rfl

theorem finDeleteEmbedding_ne {n : Nat} (i : Fin (n + 1)) (k : Fin n) :
    Not (finDeleteEmbedding i k = i) := by
  intro h
  change Equiv.swap 0 i k.succ = i at h
  have hZero : k.succ = (0 : Fin (n + 1)) := by
    simpa using congrArg (Equiv.swap 0 i) h
  exact Fin.succ_ne_zero k hZero

theorem finDeleteEmbedding_surj {n : Nat} (i a : Fin (n + 1))
    (h : Not (a = i)) :
    exists k : Fin n, finDeleteEmbedding i k = a := by
  have hZero : Not (Equiv.swap 0 i a = (0 : Fin (n + 1))) := by
    intro hEq
    apply h
    simpa using congrArg (Equiv.swap 0 i) hEq
  have hSucc : forall b : Fin (n + 1), Not (b = 0) ->
      exists k : Fin n, k.succ = b := by
    intro b
    exact Fin.cases (fun hEq => False.elim (hEq rfl))
      (fun k _ => Exists.intro k rfl) b
  cases hSucc _ hZero with
  | intro k hk =>
    refine Exists.intro k ?_
    change Equiv.swap 0 i k.succ = a
    simpa using congrArg (Equiv.swap 0 i) hk

def finDeleteSupport {n : Nat} (S : Finset (Fin (n + 1))) (i : Fin (n + 1)) :
    Finset (Fin n) :=
  (S.erase i).preimage (finDeleteEmbedding i) (finDeleteEmbedding i).injective.injOn

theorem finDeleteSupport_image {n : Nat}
    (S : Finset (Fin (n + 1))) (i : Fin (n + 1)) :
    (finDeleteSupport S i).image (finDeleteEmbedding i) = S.erase i := by
  ext a
  constructor
  case mp =>
    intro h
    cases Finset.mem_image.mp h with
    | intro k hk =>
      cases hk with
      | intro hkS hkA =>
        rw [<- hkA]
        exact Finset.mem_preimage.mp hkS
  case mpr =>
    intro h
    cases finDeleteEmbedding_surj i a (Finset.mem_erase.mp h).1 with
    | intro k hk =>
      apply Finset.mem_image.mpr
      refine Exists.intro k (And.intro ?_ hk)
      apply Finset.mem_preimage.mpr
      simpa only [hk] using h

theorem finDeleteSupport_card {n : Nat}
    (S : Finset (Fin (n + 1))) (i : Fin (n + 1)) :
    (finDeleteSupport S i).card = (S.erase i).card := by
  have h := congrArg Finset.card (finDeleteSupport_image S i)
  rw [Finset.card_image_of_injective _ (finDeleteEmbedding i).injective] at h
  exact h

theorem finDeleteSupport_card_add_one {n : Nat}
    (S : Finset (Fin (n + 1))) (i : Fin (n + 1)) (hi : Membership.mem S i) :
    (finDeleteSupport S i).card + 1 = S.card := by
  rw [finDeleteSupport_card]
  exact Finset.card_erase_add_one hi

theorem finDeleteSupport_product {R : Type*} [CommMonoid R] {n : Nat}
    (S : Finset (Fin (n + 1))) (i : Fin (n + 1)) (f : Fin (n + 1) -> R) :
    Finset.prod (S.erase i) f =
      Finset.prod (finDeleteSupport S i) (fun k => f (finDeleteEmbedding i k)) := by
  rw [<- finDeleteSupport_image S i,
    Finset.prod_image (fun a _ b _ h => (finDeleteEmbedding i).injective h)]

theorem finDeleteSupport_product_insert {R : Type*} [CommMonoid R] {n : Nat}
    (S : Finset (Fin (n + 1))) (i : Fin (n + 1)) (hi : Membership.mem S i)
    (f : Fin (n + 1) -> R) :
    Finset.prod S f = f i *
      Finset.prod (finDeleteSupport S i) (fun k => f (finDeleteEmbedding i k)) := by
  rw [<- Finset.mul_prod_erase S f hi, finDeleteSupport_product S i f]

def finPermutationDeleteEquiv {n : Nat} (i : Fin (n + 1)) :
    Equiv (Prod (Fin (n + 1)) (Equiv.Perm (Fin n))) (Equiv.Perm (Fin (n + 1))) where
  toFun p := Equiv.Perm.decomposeFin.symm p * Equiv.swap 0 i
  invFun sigma := Equiv.Perm.decomposeFin (sigma * Equiv.swap 0 i)
  left_inv p := by simp [mul_assoc]
  right_inv sigma := by simp [mul_assoc]

theorem finPermutationDeleteEquiv_selected {n : Nat} (i j : Fin (n + 1))
    (sigma : Equiv.Perm (Fin n)) :
    finPermutationDeleteEquiv i (j, sigma) i = j := by
  simp [finPermutationDeleteEquiv, Equiv.Perm.mul_apply]

theorem finPermutationDeleteEquiv_remaining {n : Nat} (i j : Fin (n + 1))
    (sigma : Equiv.Perm (Fin n)) (k : Fin n) :
    finPermutationDeleteEquiv i (j, sigma) (finDeleteEmbedding i k) =
      finDeleteEmbedding j (sigma k) := by
  change (Equiv.Perm.decomposeFin.symm (j, sigma))
      (Equiv.swap 0 i (Equiv.swap 0 i k.succ)) = Equiv.swap 0 j (sigma k).succ
  simp

theorem finitePermutationSubsetSum_delete {R : Type*} [CommSemiring R] {n : Nat}
    (M : Matrix (Fin (n + 1)) (Fin (n + 1)) R)
    (S : Finset (Fin (n + 1))) (i : Fin (n + 1)) (hi : Membership.mem S i) :
    Finset.sum Finset.univ (fun sigma : Equiv.Perm (Fin (n + 1)) =>
        Finset.prod S (fun k => M (sigma k) k)) =
      Finset.sum Finset.univ (fun j : Fin (n + 1) =>
        M j i * Finset.sum Finset.univ (fun sigma : Equiv.Perm (Fin n) =>
          Finset.prod (finDeleteSupport S i) (fun k =>
            M (finDeleteEmbedding j (sigma k)) (finDeleteEmbedding i k)))) := by
  classical
  calc
    _ = Finset.sum Finset.univ
        (fun p : Prod (Fin (n + 1)) (Equiv.Perm (Fin n)) =>
          Finset.prod S (fun k => M (finPermutationDeleteEquiv i p k) k)) := by
      exact (Equiv.sum_comp (finPermutationDeleteEquiv i)
        (fun sigma => Finset.prod S (fun k => M (sigma k) k))).symm
    _ = _ := by
      rw [Fintype.sum_prod_type]
      apply Finset.sum_congr rfl
      intro j hj
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro sigma hs
      rw [finDeleteSupport_product_insert S i hi]
      simp only [finPermutationDeleteEquiv_selected,
        finPermutationDeleteEquiv_remaining]

end PrimeFactorOscillations

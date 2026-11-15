/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import Mathlib.Data.List.OfFn
import PrimeFactorOscillations.Helpers.HamiltonianRevealPermutationAverage

/-! # Exact available-column suffixes for every reveal order

These identities connect the full sequential log-partition estimate to
actual row-order permutations. Every suffix contains exactly the still
unrevealed matched columns. The matching weights are independent of the
order; no denominator or overlap is omitted.
-/

set_option autoImplicit false
set_option Elab.async false

noncomputable section

namespace PrimeFactorOscillations

variable {R C : Type*} [DecidableEq R] [DecidableEq C]

def hamiltonianSuffixLogCost (A : R -> C -> Real) : List R -> (R -> C) -> Real
  | [], _ => 0
  | i :: rows, f =>
      Real.log ((i :: rows).toFinset.sum (fun j => A i (f j))) +
        hamiltonianSuffixLogCost A rows f

theorem hamiltonian_reveal_row_product_to_finset
    (A : R -> C -> Real) (rows : List R) (f : R -> C) (hRows : rows.Nodup) :
    hamiltonianRevealRowProduct A rows f =
      rows.toFinset.prod (fun i => A i (f i)) := by
  induction rows with
  | nil => simp [hamiltonianRevealRowProduct]
  | cons i rows ih =>
    have hNodup := List.nodup_cons.mp hRows
    simp only [hamiltonianRevealRowProduct, List.toFinset_cons]
    rw [Finset.prod_insert (by simpa only [List.mem_toFinset] using hNodup.1), ih hNodup.2]

theorem hamiltonian_reveal_cost_as_suffix
    (A : R -> C -> Real) (rows : List R) (f : R -> C)
    (hf : Function.Injective f) (hRows : rows.Nodup) :
    hamiltonianRevealLogCost A rows (rows.toFinset.image f) f =
      hamiltonianSuffixLogCost A rows f := by
  induction rows with
  | nil => simp [hamiltonianRevealLogCost, hamiltonianSuffixLogCost]
  | cons i rows ih =>
    have hNodup := List.nodup_cons.mp hRows
    have hNot : Not (Membership.mem (rows.toFinset.image f) (f i)) := by
      intro hMem
      cases Finset.mem_image.mp hMem with
      | intro j hj =>
        have hji := hf hj.2
        subst j
        exact hNodup.1 (List.mem_toFinset.mp hj.1)
    rw [hamiltonianRevealLogCost, hamiltonianSuffixLogCost]
    congr 1
    case e_a =>
      congr 1
      exact Finset.sum_image (fun j _ k _ h => hf h)
    case e_a =>
      rw [List.toFinset_cons, Finset.image_insert, Finset.erase_insert hNot]
      exact ih hNodup.2

theorem hamiltonian_ofFn_to_finset {n : Nat} (nu : Fin n -> R) :
    (List.ofFn nu).toFinset = Finset.univ.image nu := by
  ext i
  simp only [List.mem_toFinset, List.mem_ofFn, Finset.mem_image,
    Finset.mem_univ, true_and]

theorem hamiltonian_suffix_cost_ofFn (A : R -> C -> Real) (n : Nat)
    (nu : Fin n -> R) (f : R -> C) (hNu : Function.Injective nu) :
    hamiltonianSuffixLogCost A (List.ofFn nu) f =
      Finset.univ.sum (fun k : Fin n => Real.log (Finset.univ.sum
        (fun j : Fin n => if k <= j then A (nu k) (f (nu j)) else 0))) := by
  induction n with
  | zero => simp [hamiltonianSuffixLogCost]
  | succ n ih =>
    have hHead : (List.ofFn nu).toFinset.sum (fun j => A (nu 0) (f j)) =
        Finset.univ.sum (fun j => A (nu 0) (f (nu j))) := by
      rw [hamiltonian_ofFn_to_finset, Finset.sum_image (fun j _ k _ h => hNu h)]
    rw [List.ofFn_succ] at hHead
    rw [List.ofFn_succ, hamiltonianSuffixLogCost, hHead,
      ih (fun k => nu k.succ) (fun i j h => Fin.succ_injective _ (hNu h))]
    have hSplit := Fin.sum_univ_succ
      (fun k : Fin (n + 1) => Real.log (Finset.univ.sum
        (fun j : Fin (n + 1) => if k <= j then A (nu k) (f (nu j)) else 0)))
    rw [hSplit]
    congr 1
    all_goals
      first
      | solve | simp
      | apply Finset.sum_congr rfl
        intro k hk
        congr 1
        rw [Fin.sum_univ_succ]
        simp

theorem hamiltonian_permutation_order_log_bound (n : Nat)
    (A : Matrix (Fin n) (Fin n) Real) (hA : forall i j, 0 <= A i j)
    (nu : Equiv.Perm (Fin n))
    (hMass : 0 < Finset.univ.sum (fun sigma : Equiv.Perm (Fin n) =>
      Finset.univ.prod (fun i => A i (sigma i)))) :
    Real.log (Finset.univ.sum (fun sigma : Equiv.Perm (Fin n) =>
      Finset.univ.prod (fun i => A i (sigma i)))) <=
      Finset.univ.sum (fun sigma : Equiv.Perm (Fin n) =>
        Finset.univ.prod (fun i => A i (sigma i)) *
          Finset.univ.sum (fun k : Fin n => Real.log (Finset.univ.sum
            (fun j : Fin n => if k <= j then A (nu k) (sigma (nu j)) else 0)))) /
      Finset.univ.sum (fun sigma : Equiv.Perm (Fin n) =>
        Finset.univ.prod (fun i => A i (sigma i))) := by
  have hRows : (List.ofFn nu).Nodup := List.nodup_ofFn.mpr nu.injective
  have hFull : (List.ofFn nu).toFinset = Finset.univ := by
    rw [hamiltonian_ofFn_to_finset]
    exact Finset.image_univ_of_surjective nu.surjective
  have hWeight (sigma : Equiv.Perm (Fin n)) :
      hamiltonianRevealRowProduct A (List.ofFn nu) sigma =
        Finset.univ.prod (fun i => A i (sigma i)) := by
    rw [hamiltonian_reveal_row_product_to_finset A _ _ hRows, hFull]
  have hCost (sigma : Equiv.Perm (Fin n)) :
      hamiltonianRevealLogCost A (List.ofFn nu) Finset.univ sigma =
        Finset.univ.sum (fun k : Fin n => Real.log (Finset.univ.sum
          (fun j : Fin n => if k <= j then A (nu k) (sigma (nu j)) else 0))) := by
    have hImage : (List.ofFn nu).toFinset.image sigma = Finset.univ := by
      rw [hFull]
      exact Finset.image_univ_of_surjective sigma.surjective
    calc
      _ = hamiltonianRevealLogCost A (List.ofFn nu)
          ((List.ofFn nu).toFinset.image sigma) sigma := by rw [hImage]
      _ = hamiltonianSuffixLogCost A (List.ofFn nu) sigma :=
        hamiltonian_reveal_cost_as_suffix A _ _ sigma.injective hRows
      _ = _ := hamiltonian_suffix_cost_ofFn A n nu sigma nu.injective
  have hMap : forall sigma : Equiv.Perm (Fin n), Membership.mem Finset.univ sigma ->
      forall i, Membership.mem (List.ofFn nu) i ->
        Membership.mem (Finset.univ : Finset (Fin n)) (sigma i) := by
    intro sigma hs i hi
    exact Finset.mem_univ _
  have hDistinct : forall sigma : Equiv.Perm (Fin n), Membership.mem Finset.univ sigma ->
      List.Pairwise (fun i j => Not (sigma i = sigma j)) (List.ofFn nu) := by
    intro sigma hs
    apply List.pairwise_ofFn.mpr
    intro i j hij hEq
    exact (ne_of_lt hij) (nu.injective (sigma.injective hEq))
  have hSeparate : forall sigma : Equiv.Perm (Fin n), Membership.mem Finset.univ sigma ->
      forall tau : Equiv.Perm (Fin n), Membership.mem Finset.univ tau ->
      (forall i, Membership.mem (List.ofFn nu) i -> sigma i = tau i) -> sigma = tau := by
    intro sigma hs tau ht hEqual
    apply Equiv.ext
    intro i
    apply hEqual i
    exact List.mem_toFinset.mp (by rw [hFull]; exact Finset.mem_univ i)
  have h := hamiltonian_reveal_log_partition_bound A hA (List.ofFn nu) Finset.univ
    Finset.univ (fun sigma : Equiv.Perm (Fin n) => (sigma : Fin n -> Fin n))
    hMap hDistinct hSeparate (by simpa only [hWeight] using hMass)
  simpa only [hWeight, hCost] using h

end PrimeFactorOscillations

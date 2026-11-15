/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import Mathlib.Order.Interval.Finset.Fin
import PrimeFactorOscillations.Helpers.HamiltonianRevealPermutationAverage

/-! # The complete row-order average of one reveal stage

Every permutation of the full row order is retained. Conditioning on
the currently revealed row leaves an actual uniform permutation of
its complement, and the suffix support has its exact cardinality.
-/

set_option autoImplicit false
set_option Elab.async false

noncomputable section

namespace PrimeFactorOscillations

theorem hamiltonian_fin_sum_delete {n : Nat} (i : Fin (n + 1))
    (f : Fin (n + 1) -> Real) :
    Finset.univ.sum f = f i +
      Finset.univ.sum (fun k : Fin n => f (finDeleteEmbedding i k)) := by
  calc
    _ = Finset.univ.sum (fun j => f (Equiv.swap 0 i j)) :=
      (Equiv.sum_comp (Equiv.swap 0 i) f).symm
    _ = _ := by
      rw [Fin.sum_univ_succ]
      simp only [Equiv.swap_apply_left, finDeleteEmbedding_apply]

def hamiltonianRevealSuffixSupport {n : Nat} (k : Fin (n + 1)) : Finset (Fin n) :=
  finDeleteSupport (Finset.Ioi k) k

theorem hamiltonian_reveal_suffix_support_mem {n : Nat} (k : Fin (n + 1)) (j : Fin n) :
    Membership.mem (hamiltonianRevealSuffixSupport k) j <->
      k < finDeleteEmbedding k j := by
  simp only [hamiltonianRevealSuffixSupport, finDeleteSupport, Finset.mem_preimage,
    Finset.mem_erase, Finset.mem_Ioi]
  constructor
  case mp => exact fun h => h.2
  case mpr => exact fun h => And.intro (ne_of_gt h) h

theorem hamiltonian_reveal_suffix_support_card {n : Nat} (k : Fin (n + 1)) :
    (hamiltonianRevealSuffixSupport k).card = n - k.val := by
  have hErase : (Finset.Ioi k).erase k = Finset.Ioi k := by
    ext j
    simp only [Finset.mem_erase, Finset.mem_Ioi]
    constructor
    case mp => exact fun h => h.2
    case mpr => exact fun h => And.intro (ne_of_gt h) h
  rw [hamiltonianRevealSuffixSupport, finDeleteSupport_card, hErase, Fin.card_Ioi]
  simp only [Nat.add_sub_cancel]

theorem hamiltonian_reveal_stage_delete {n : Nat}
    (A : Matrix (Fin (n + 1)) (Fin (n + 1)) Real)
    (sigma : Equiv.Perm (Fin (n + 1))) (k i : Fin (n + 1))
    (tau : Equiv.Perm (Fin n)) :
    Finset.univ.sum (fun j : Fin (n + 1) => if k <= j then
      A (finPermutationDeleteEquiv k (i, tau) k)
        (sigma (finPermutationDeleteEquiv k (i, tau) j)) else 0) =
      A i (sigma i) + (hamiltonianRevealSuffixSupport k).sum
        (fun j => A i (sigma (finDeleteEmbedding i (tau j)))) := by
  rw [hamiltonian_fin_sum_delete k]
  simp only [finPermutationDeleteEquiv_selected, finPermutationDeleteEquiv_remaining,
    le_refl, if_true]
  congr 1
  let S := hamiltonianRevealSuffixSupport k
  have hCondition (j : Fin n) : k <= finDeleteEmbedding k j <-> Membership.mem S j := by
    rw [hamiltonian_reveal_suffix_support_mem]
    exact Iff.intro
      (fun h => lt_of_le_of_ne h (Ne.symm (finDeleteEmbedding_ne k j)))
      (fun h => le_of_lt h)
  calc
    _ = S.sum (fun j => if k <= finDeleteEmbedding k j then
        A i (sigma (finDeleteEmbedding i (tau j))) else 0) := by
      symm
      apply Finset.sum_subset (Finset.subset_univ S)
      intro j hj hNot
      rw [if_neg (fun h => hNot ((hCondition j).mp h))]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro j hj
      rw [if_pos ((hCondition j).mpr hj)]

theorem hamiltonian_reveal_stage_order_average (n : Nat)
    (A : Matrix (Fin (n + 2)) (Fin (n + 2)) Real)
    (sigma : Equiv.Perm (Fin (n + 2))) (k : Fin (n + 2)) (c : Real)
    (hNonneg : forall i j, 0 <= A i j)
    (hRow : forall i, Finset.univ.sum (fun j => A i j) <= 1)
    (hCap : forall i j, A i j <= c)
    (hMatching : forall i, 0 < A i (sigma i)) :
    Finset.univ.sum (fun nu : Equiv.Perm (Fin (n + 2)) =>
      Real.log (Finset.univ.sum (fun j : Fin (n + 2) =>
        if k <= j then A (nu k) (sigma (nu j)) else 0))) <=
      (Fintype.card (Equiv.Perm (Fin (n + 2))) : Real) *
        Real.log (c + ((n + 1 - k.val : Nat) : Real) / (n + 1 : Real)) := by
  let S := hamiltonianRevealSuffixSupport k
  let m : Real := Fintype.card (Equiv.Perm (Fin (n + 1)))
  have hInner (i : Fin (n + 2)) :
      Finset.univ.sum (fun tau : Equiv.Perm (Fin (n + 1)) =>
        Real.log (A i (sigma i) + S.sum
          (fun j => A i (sigma (finDeleteEmbedding i (tau j)))))) <=
        m * Real.log (c + ((n + 1 - k.val : Nat) : Real) / (n + 1 : Real)) := by
    have hRest : Finset.univ.sum (fun j : Fin (n + 1) =>
        A i (sigma (finDeleteEmbedding i j))) <= 1 := by
      have hDelete := hamiltonian_fin_sum_delete i (fun j => A i (sigma j))
      have hTotal : Finset.univ.sum (fun j => A i (sigma j)) <= 1 := by
        rw [Equiv.sum_comp sigma (fun j => A i j)]
        exact hRow i
      nlinarith only [hDelete, hTotal, hNonneg i (sigma i)]
    have h := hamiltonian_conditional_reveal_log_bound n S
      (fun j => A i (sigma (finDeleteEmbedding i j))) (A i (sigma i)) c
      (hMatching i) (hCap i (sigma i)) (fun j => hNonneg _ _) hRest
    simpa only [S, hamiltonian_reveal_suffix_support_card] using h
  calc
    _ = Finset.univ.sum
        (fun p : Prod (Fin (n + 2)) (Equiv.Perm (Fin (n + 1))) =>
          Real.log (Finset.univ.sum (fun j : Fin (n + 2) =>
            if k <= j then
              A (finPermutationDeleteEquiv k p k)
                (sigma (finPermutationDeleteEquiv k p j)) else 0))) :=
      (Equiv.sum_comp (finPermutationDeleteEquiv k) _).symm
    _ = Finset.univ.sum (fun i : Fin (n + 2) =>
        Finset.univ.sum (fun tau : Equiv.Perm (Fin (n + 1)) =>
          Real.log (A i (sigma i) + S.sum
            (fun j => A i (sigma (finDeleteEmbedding i (tau j))))))) := by
      rw [Fintype.sum_prod_type]
      simp only [hamiltonian_reveal_stage_delete, S]
    _ <= Finset.univ.sum (fun _ : Fin (n + 2) =>
        m * Real.log (c + ((n + 1 - k.val : Nat) : Real) / (n + 1 : Real))) :=
      Finset.sum_le_sum (fun i _ => hInner i)
    _ = _ := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      rw [hamiltonian_permutation_card_step]
      dsimp only [m]
      norm_num only [Nat.cast_add, Nat.cast_one]
      ring

end PrimeFactorOscillations

/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.HamiltonianCoprimeMarkedMass
import PrimeFactorOscillations.Helpers.HamiltonianPathContraction

/-! # Injective weighted cutting from marked cycles to endpoint paths

One usable edge is selected per marked cycle. Two exact nonzero
insertions retain the full orbit and every other weight. Decomposing
the inserted permutation recovers the original cycle, so multiple
usable edges introduce no counting multiplicity.
-/

set_option autoImplicit false
set_option Elab.async false

open scoped Classical

noncomputable section

namespace PrimeFactorOscillations

def hamiltonianCutInsertion {m : Nat} (tau : Equiv.Perm (Fin m)) (i : Fin m) :
    Equiv.Perm (Fin (m + 1)) :=
  Equiv.Perm.decomposeFin.symm ((tau i).succ, tau)

theorem hamiltonian_cut_insertion_zero {m : Nat}
    (tau : Equiv.Perm (Fin m)) (i : Fin m) :
    hamiltonianCutInsertion tau i 0 = (tau i).succ := by
  exact Equiv.Perm.decomposeFin_symm_apply_zero _ _

theorem hamiltonian_cut_insertion_succ {m : Nat}
    (tau : Equiv.Perm (Fin m)) (i j : Fin m) :
    hamiltonianCutInsertion tau i j.succ =
      if j = i then 0 else (tau j).succ := by
  rw [hamiltonianCutInsertion, Equiv.Perm.decomposeFin_symm_apply_succ]
  by_cases hji : j = i
  . subst j
    simp only [Equiv.swap_apply_right, ite_true]
  . rw [ite_eq_right hji]
    apply Equiv.swap_apply_of_ne_of_ne
    . intro h
      have hv := congrArg (fun x : Fin (m + 1) => x.val) h
      simp only [Fin.val_succ, Fin.val_zero] at hv
      omega
    . intro h
      have hv := congrArg (fun x : Fin (m + 1) => x.val) h
      simp only [Fin.val_succ] at hv
      have heq : tau j = tau i := Fin.ext (by omega)
      exact hji (tau.injective heq)

theorem hamiltonian_cut_insertion_injective_base {m : Nat}
    (tau sigma : Equiv.Perm (Fin m)) (i j : Fin m)
    (h : hamiltonianCutInsertion tau i = hamiltonianCutInsertion sigma j) :
    tau = sigma := by
  have hBase := congrArg (fun f : Equiv.Perm (Fin (m + 1)) =>
    (Equiv.Perm.decomposeFin f).2) h
  simpa only [hamiltonianCutInsertion, Equiv.apply_symm_apply] using hBase

theorem hamiltonian_cut_insertion_one_orbit {m : Nat}
    (tau : Equiv.Perm (Fin m)) (i : Fin m)
    (hTau : (hamiltonianPermutationOrbits tau).card = 1) :
    (hamiltonianPermutationOrbits (hamiltonianCutInsertion tau i)).card = 1 := by
  apply hamiltonian_one_orbit_insert_zero (tau i).succ _ tau hTau
  intro h
  have hv := congrArg (fun x : Fin (m + 1) => x.val) h
  simp only [Fin.val_succ, Fin.val_zero] at hv
  omega

theorem hamiltonian_swap_endpoint_tail {m : Nat} (x : Fin m) :
    Equiv.swap (0 : Fin (m + 2)) 1 x.succ.succ = x.succ.succ := by
  apply Equiv.swap_apply_of_ne_of_ne
  . intro h
    have hv := congrArg (fun y : Fin (m + 2) => y.val) h
    simp only [Fin.val_succ, Fin.val_zero] at hv
    omega
  . intro h
    have hOne : (1 : Fin (m + 2)) = (0 : Fin (m + 1)).succ := by
      apply Fin.ext
      simp
    rw [hOne] at h
    have hv := congrArg (fun y : Fin (m + 2) => y.val) h
    simp only [Fin.val_succ, Fin.val_zero] at hv
    omega

theorem hamiltonian_cut_insertion_tail {m : Nat}
    (tau : Equiv.Perm (Fin m)) (i j : Fin m) :
    Equiv.swap (0 : Fin (m + 2)) 1 (hamiltonianCutInsertion tau i j.succ).succ =
      if j = i then 0 else (tau j).succ.succ := by
  rw [hamiltonian_cut_insertion_succ]
  by_cases hji : j = i
  . simp only [ite_eq_left hji]
    have hOne : (0 : Fin (m + 1)).succ = (1 : Fin (m + 2)) := by
      apply Fin.ext
      simp
    rw [hOne, Equiv.swap_apply_right]
  . simp only [ite_eq_right hji]
    exact hamiltonian_swap_endpoint_tail (tau j)

theorem hamiltonian_cut_outer_one_orbit {m : Nat}
    (tau : Equiv.Perm (Fin m)) (i : Fin m)
    (hTau : (hamiltonianPermutationOrbits tau).card = 1) :
    (hamiltonianPermutationOrbits
      (Equiv.Perm.decomposeFin.symm ((1 : Fin (m + 2)), hamiltonianCutInsertion tau i))).card =
        1 := by
  apply hamiltonian_one_orbit_insert_zero 1 _
    (hamiltonianCutInsertion tau i) (hamiltonian_cut_insertion_one_orbit tau i hTau)
  intro h
  have hOne : (1 : Fin (m + 2)) = (0 : Fin (m + 1)).succ := by
    apply Fin.ext
    simp
  rw [hOne] at h
  have hv := congrArg (fun y : Fin (m + 2) => y.val) h
  simp only [Fin.val_succ, Fin.val_zero] at hv
  omega

theorem hamiltonian_cut_weight_lower {m : Nat}
    (M : Matrix (Fin (m + 2)) (Fin (m + 2)) Real)
    (tau : Equiv.Perm (Fin m)) (i : Fin m) (kappa : Real)
    (hNonneg : forall x y, 0 <= M x y)
    (hClosing : kappa * M (tau i).succ.succ i.succ.succ <=
      M (tau i).succ.succ 1 * M 0 i.succ.succ) :
    kappa * Finset.univ.prod (fun j : Fin m => M (tau j).succ.succ j.succ.succ) <=
      Finset.univ.prod (fun j : Fin (m + 1) =>
        M (Equiv.swap 0 1 (hamiltonianCutInsertion tau i j).succ) j.succ) := by
  let f := fun j : Fin m => M (tau j).succ.succ j.succ.succ
  let g := fun j : Fin m =>
    M (Equiv.swap 0 1 (hamiltonianCutInsertion tau i j.succ).succ) j.succ.succ
  let rest := (Finset.univ.erase i).prod f
  have hBase : Finset.univ.prod f = f i * rest := by
    exact (Finset.mul_prod_erase (Finset.univ : Finset (Fin m)) f (Finset.mem_univ i)).symm
  have hGi : g i = M 0 i.succ.succ := by
    dsimp only [g]
    rw [hamiltonian_cut_insertion_tail]
    simp only [ite_true]
  have hRest : (Finset.univ.erase i).prod g = rest := by
    apply Finset.prod_congr rfl
    intro j hj
    have hji : Not (j = i) := (Finset.mem_erase.mp hj).1
    dsimp only [g, f]
    rw [hamiltonian_cut_insertion_tail, ite_eq_right hji]
  have hGProd : Finset.univ.prod g = M 0 i.succ.succ * rest := by
    rw [<- Finset.mul_prod_erase (Finset.univ : Finset (Fin m)) g (Finset.mem_univ i),
      hGi, hRest]
  have hRest0 : 0 <= rest :=
    Finset.prod_nonneg (fun j hj => hNonneg _ _)
  have hProduct : Finset.univ.prod (fun j : Fin (m + 1) =>
      M (Equiv.swap 0 1 (hamiltonianCutInsertion tau i j).succ) j.succ) =
        M (tau i).succ.succ 1 * (M 0 i.succ.succ * rest) := by
    rw [Fin.prod_univ_succ, hamiltonian_cut_insertion_zero,
      hamiltonian_swap_endpoint_tail]
    change M (tau i).succ.succ 1 * Finset.univ.prod g = _
    rw [hGProd]
  change kappa * Finset.univ.prod f <= _
  rw [hBase, hProduct]
  have h := mul_le_mul_of_nonneg_right hClosing hRest0
  dsimp only [f] at *
  nlinarith only [h]

theorem hamiltonian_marked_cycle_path_transfer {m : Nat}
    (M : Matrix (Fin (m + 2)) (Fin (m + 2)) Real)
    (E : Fin m -> Fin m -> Prop) [DecidableRel E] (kappa : Real)
    (hNonneg : forall x y, 0 <= M x y)
    (hClosing : forall i j, E i j ->
      kappa * M i.succ.succ j.succ.succ <= M i.succ.succ 1 * M 0 j.succ.succ) :
    kappa * hamiltonianMarkedCycleSum
        (M.submatrix (fun i : Fin m => i.succ.succ) (fun j : Fin m => j.succ.succ)) E <=
      hamiltonianPrescribedPathSum M 0 1 := by
  let Q := M.submatrix (fun i : Fin m => i.succ.succ) (fun j : Fin m => j.succ.succ)
  let good : Finset (Equiv.Perm (Fin m)) := Finset.univ.filter
    (fun tau => (hamiltonianPermutationOrbits tau).card = 1 /\ exists i, E (tau i) i)
  have hData (tau : good) :
      (hamiltonianPermutationOrbits tau.val).card = 1 /\ exists i, E (tau.val i) i :=
    (Finset.mem_filter.mp tau.property).2
  let cut := fun tau : good => (hData tau).2.choose
  have hCut (tau : good) : E (tau.val (cut tau)) (cut tau) := (hData tau).2.choose_spec
  let lift := fun tau : good => hamiltonianCutInsertion tau.val (cut tau)
  have hInj : Function.Injective lift := by
    intro tau sigma h
    exact Subtype.ext (hamiltonian_cut_insertion_injective_base
      tau.val sigma.val (cut tau) (cut sigma) h)
  let F := fun sigma : Equiv.Perm (Fin (m + 1)) =>
    if (hamiltonianPermutationOrbits
      (Equiv.Perm.decomposeFin.symm ((1 : Fin (m + 2)), sigma))).card = 1 then
      Finset.univ.prod (fun j : Fin (m + 1) =>
        M (Equiv.swap 0 1 (sigma j).succ) j.succ) else 0
  have hF0 (sigma : Equiv.Perm (Fin (m + 1))) : 0 <= F sigma := by
    dsimp only [F]
    split_ifs
    . exact Finset.prod_nonneg (fun j hj => hNonneg _ _)
    . exact le_refl 0
  have hPoint (tau : good) :
      kappa * Finset.univ.prod (fun j : Fin m => Q (tau.val j) j) <= F (lift tau) := by
    have hOrbit := hamiltonian_cut_outer_one_orbit tau.val (cut tau) (hData tau).1
    dsimp only [F, lift]
    rw [ite_eq_left hOrbit]
    exact hamiltonian_cut_weight_lower M tau.val (cut tau) kappa hNonneg
      (hClosing _ _ (hCut tau))
  have hGood : hamiltonianMarkedCycleSum Q E =
      good.sum (fun tau => Finset.univ.prod (fun j : Fin m => Q (tau j) j)) := by
    simp only [hamiltonianMarkedCycleSum, good, Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro tau ht
    by_cases h : (hamiltonianPermutationOrbits tau).card = 1 /\ exists i, E (tau i) i
    . simp only [ite_eq_left h]
    . simp only [ite_eq_right h]
  have hImage : (Finset.univ.image lift).sum F =
      Finset.univ.sum (fun tau : good => F (lift tau)) := by
    exact Finset.sum_image (fun tau ht sigma hs h => hInj h)
  change kappa * hamiltonianMarkedCycleSum Q E <= _
  calc
    _ = good.sum (fun tau => kappa *
        Finset.univ.prod (fun j : Fin m => Q (tau j) j)) := by
      rw [hGood, Finset.mul_sum]
    _ = Finset.univ.sum (fun tau : good => kappa *
        Finset.univ.prod (fun j : Fin m => Q (tau.val j) j)) :=
      (hamiltonian_sum_on_finset good _).symm
    _ <= Finset.univ.sum (fun tau : good => F (lift tau)) :=
      Finset.sum_le_sum (fun tau ht => hPoint tau)
    _ = (Finset.univ.image lift).sum F := hImage.symm
    _ <= Finset.univ.sum F :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
        (fun sigma hs hn => hF0 sigma)
    _ = hamiltonianPrescribedPathSum M 0 1 := by
      exact (hamiltonian_prescribed_path_contracted_expansion M 1).symm

end PrimeFactorOscillations

/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.HamiltonianPrescribedPathMinor

/-! # One-orbit insertion and the prescribed-path lower consumer

The nontrivial closing edge is contracted without dropping any path
weight. A full one-orbit minor permutation lifts to a full one-orbit
permutation on the original vertices. Its weighted cycle sum is thus
an actual lower bound for the prescribed path sum.
-/

set_option autoImplicit false
set_option Elab.async false

noncomputable section

namespace PrimeFactorOscillations

variable {Iota : Type*} [Fintype Iota] [DecidableEq Iota]

theorem hamiltonian_single_orbit_same_cycle (f : Equiv.Perm Iota)
    (h : (hamiltonianPermutationOrbits f).card = 1) (x y : Iota) :
    f.SameCycle x y := by
  have hExists := Finset.card_eq_one.mp h
  let C := hExists.choose
  have hSet : hamiltonianPermutationOrbits f = {C} := hExists.choose_spec
  have hX := hamiltonianPermutationOrbit_mem f x
  have hY := hamiltonianPermutationOrbit_mem f y
  rw [hSet, Finset.mem_singleton] at hX hY
  exact (hamiltonianPermutationOrbit_eq_iff f x y).mp (hX.trans hY.symm)

theorem hamiltonian_single_orbit_of_full_orbit (f : Equiv.Perm Iota) (a : Iota)
    (hAll : forall x, f.SameCycle a x) :
    (hamiltonianPermutationOrbits f).card = 1 := by
  have hPoint (x : Iota) :
      hamiltonianPermutationOrbit f x = hamiltonianPermutationOrbit f a :=
    (hamiltonianPermutationOrbit_eq_iff f x a).mpr (hAll x).symm
  have hSet : hamiltonianPermutationOrbits f = {hamiltonianPermutationOrbit f a} := by
    apply Finset.ext
    intro A
    apply Iff.intro
    next =>
      intro hA
      have hRep := Finset.mem_image.mp hA
      let x := hRep.choose
      have hEq : hamiltonianPermutationOrbit f x = A := hRep.choose_spec.2
      exact Finset.mem_singleton.mpr (hEq.symm.trans (hPoint x))
    next =>
      intro hA
      rw [Finset.mem_singleton] at hA
      rw [hA]
      exact hamiltonianPermutationOrbit_mem f a
  rw [hSet, Finset.card_singleton]

theorem hamiltonian_one_orbit_insert_zero {n : Nat}
    (b : Fin (n + 1)) (hb : Not (b = 0)) (tau : Equiv.Perm (Fin n))
    (hTau : (hamiltonianPermutationOrbits tau).card = 1) :
    (hamiltonianPermutationOrbits (Equiv.Perm.decomposeFin.symm (b, tau))).card = 1 := by
  let g : Equiv.Perm (Fin (n + 1)) := Equiv.Perm.decomposeFin.symm (b, tau)
  let S := hamiltonianPermutationOrbit g 0
  have hZero : g 0 = b := Equiv.Perm.decomposeFin_symm_apply_zero b tau
  have hSucc (i : Fin n) : g i.succ = Equiv.swap 0 b (tau i).succ := by
    simp only [g, Equiv.Perm.decomposeFin_symm_apply_succ]
  have hS : hamiltonianPermutationInvariant g S :=
    hamiltonianPermutationOrbit_invariant g 0
  have hZeroIn : Membership.mem S (0 : Fin (n + 1)) :=
    (mem_hamiltonianPermutationOrbit g 0 0).mpr (Equiv.Perm.SameCycle.refl g 0)
  have hColor : Membership.mem S b <-> Membership.mem S (0 : Fin (n + 1)) := by
    have h := hS 0
    rw [hZero] at h
    exact h
  have hSwap (x : Fin (n + 1)) :
      Membership.mem S (Equiv.swap 0 b x) <-> Membership.mem S x := by
    by_cases hx : x = 0
    case pos =>
      subst x
      simpa only [Equiv.swap_apply_left] using hColor
    case neg =>
      by_cases hxb : x = b
      case pos =>
        subst x
        simpa only [Equiv.swap_apply_right] using hColor.symm
      case neg =>
        simp only [Equiv.swap_apply_of_ne_of_ne hx hxb]
  let R : Finset (Fin n) := Finset.univ.filter (fun i => Membership.mem S i.succ)
  have hR : hamiltonianPermutationInvariant tau R := by
    intro i
    change Membership.mem R (tau i) <-> Membership.mem R i
    simp only [R, Finset.mem_filter, Finset.mem_univ, true_and]
    have h := hS i.succ
    rw [hSucc] at h
    exact (hSwap (tau i).succ).symm.trans h
  have hBVal : 0 < b.val := by
    by_contra h
    have hVal : b.val = 0 := by omega
    have hEq : b = 0 := Fin.ext hVal
    exact hb hEq
  let j : Fin n := Fin.mk (b.val - 1) (by omega)
  have hJSucc : j.succ = b := by
    apply Fin.ext
    simp only [Fin.val_succ, j]
    omega
  have hJ : Membership.mem R j := by
    simp only [R, Finset.mem_filter, Finset.mem_univ, true_and]
    rw [hJSucc]
    exact hColor.mpr hZeroIn
  have hEvery (i : Fin n) : Membership.mem R i :=
    (hamiltonianInvariant_sameCycle tau R hR j i
      (hamiltonian_single_orbit_same_cycle tau hTau j i)).mp hJ
  have hAll (x : Fin (n + 1)) : Membership.mem S x := by
    refine Fin.cases hZeroIn ?_ x
    intro i
    exact (Finset.mem_filter.mp (hEvery i)).2
  apply hamiltonian_single_orbit_of_full_orbit g 0
  intro x
  exact (mem_hamiltonianPermutationOrbit g 0 x).mp (hAll x)

theorem hamiltonian_prescribed_path_contracted_expansion {R : Type*} [CommSemiring R]
    {n : Nat} (M : Matrix (Fin (n + 1)) (Fin (n + 1)) R) (b : Fin (n + 1)) :
    hamiltonianPrescribedPathSum M 0 b =
      Finset.univ.sum (fun tau : Equiv.Perm (Fin n) =>
        if (hamiltonianPermutationOrbits (Equiv.Perm.decomposeFin.symm (b, tau))).card = 1 then
          Finset.univ.prod (fun i : Fin n =>
            M (Equiv.swap 0 b (tau i).succ) i.succ) else 0) := by
  let e : Equiv (Prod (Fin (n + 1)) (Equiv.Perm (Fin n)))
      (Equiv.Perm (Fin (n + 1))) := Equiv.Perm.decomposeFin.symm
  let F := fun f : Equiv.Perm (Fin (n + 1)) =>
    if (hamiltonianPermutationOrbits f).card = 1 /\ f 0 = b then
      Finset.univ.prod (fun i : Fin n => M (f i.succ) i.succ) else 0
  rw [hamiltonian_prescribed_path_fin_expansion]
  change Finset.univ.sum F = _
  rw [<- Equiv.sum_comp e F, Fintype.sum_prod_type]
  have hPoint (j : Fin (n + 1)) :
      Finset.univ.sum (fun tau : Equiv.Perm (Fin n) => F (e (j, tau))) =
        if j = b then
          Finset.univ.sum (fun tau : Equiv.Perm (Fin n) =>
            if (hamiltonianPermutationOrbits (Equiv.Perm.decomposeFin.symm (b, tau))).card = 1 then
              Finset.univ.prod (fun i : Fin n =>
                M (Equiv.swap 0 b (tau i).succ) i.succ) else 0) else 0 := by
    by_cases hJ : j = b
    case pos =>
      subst j
      simp only [F, e, Equiv.Perm.decomposeFin_symm_apply_zero,
        Equiv.Perm.decomposeFin_symm_apply_succ, and_true, ite_true]
    case neg =>
      simp only [F, e, Equiv.Perm.decomposeFin_symm_apply_zero,
        hJ, and_false, ite_false, Finset.sum_const_zero]
  simp_rw [hPoint]
  simp

theorem hamiltonian_prescribed_path_cycle_minor_lower {n : Nat}
    (M : Matrix (Fin (n + 1)) (Fin (n + 1)) Real)
    (b : Fin (n + 1)) (hb : Not (b = 0))
    (hNonneg : forall i j, 0 <= M i j) :
    hamiltonianCycleSum
        (M.submatrix (fun i : Fin n => Equiv.swap 0 b i.succ) Fin.succ) <=
      hamiltonianPrescribedPathSum M 0 b := by
  rw [hamiltonian_prescribed_path_contracted_expansion]
  unfold hamiltonianCycleSum
  apply Finset.sum_le_sum
  intro tau ht
  by_cases hTau : (hamiltonianPermutationOrbits tau).card = 1
  case pos =>
    have hLift := hamiltonian_one_orbit_insert_zero b hb tau hTau
    simp only [hTau, hLift, ite_true, Matrix.submatrix_apply]
    exact le_refl _
  case neg =>
    rw [ite_eq_right hTau]
    split_ifs
    next => exact Finset.prod_nonneg (fun i hi => hNonneg _ _)
    next => exact le_refl 0

end PrimeFactorOscillations

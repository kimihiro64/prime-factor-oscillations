/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.HamiltonianMarkedPathTransfer

/-! # Exact endpoint labels and weighted cutting on arbitrary finite supports

The full vertex equivalence sends zero and one to the prescribed
endpoints. Its tail is an equivalence onto their actual complement.
Marked cycle mass and prescribed path mass are both transported,
so the weighted cutting inequality uses precisely the same support.
-/

set_option autoImplicit false
set_option Elab.async false

open scoped Classical

noncomputable section

namespace PrimeFactorOscillations

variable {Iota : Type*} [Fintype Iota] [DecidableEq Iota]

omit [DecidableEq Iota] in
theorem hamiltonian_two_endpoint_labels (a b : Iota) (hab : Not (a = b))
    (m : Nat) (hSize : Fintype.card Iota = m + 2) :
    exists e : Equiv (Fin (m + 2)) Iota, e 0 = a /\ e 1 = b := by
  let e0 : Equiv (Fin (m + 2)) Iota :=
    Fintype.equivOfCardEq (by simpa only [Fintype.card_fin] using hSize.symm)
  let u := e0.symm a
  let v := e0.symm b
  let s := Equiv.swap (0 : Fin (m + 2)) u
  let q := s.symm v
  have hOne : (1 : Fin (m + 2)) = (0 : Fin (m + 1)).succ := by
    apply Fin.ext
    simp
  have h10 : Not ((1 : Fin (m + 2)) = 0) := by
    intro h
    rw [hOne] at h
    have hv := congrArg (fun x : Fin (m + 2) => x.val) h
    simp only [Fin.val_succ, Fin.val_zero] at hv
    omega
  have hq : Not (q = 0) := by
    intro h
    have he := congrArg s h
    change s (s.symm v) = s 0 at he
    rw [s.apply_symm_apply] at he
    change v = Equiv.swap 0 u 0 at he
    rw [Equiv.swap_apply_left] at he
    have hba : b = a := by
      have hv := congrArg e0 he
      change e0 (e0.symm b) = e0 (e0.symm a) at hv
      simpa only [e0.apply_symm_apply] using hv
    exact hab hba.symm
  let e := ((Equiv.swap (1 : Fin (m + 2)) q).trans s).trans e0
  refine Exists.intro e (And.intro ?_ ?_)
  . change e0 (s (Equiv.swap 1 q 0)) = a
    rw [Equiv.swap_apply_of_ne_of_ne (Ne.symm h10) (Ne.symm hq)]
    change e0 (Equiv.swap 0 u 0) = a
    rw [Equiv.swap_apply_left]
    exact e0.apply_symm_apply a
  . change e0 (s (Equiv.swap 1 q 1)) = b
    rw [Equiv.swap_apply_left]
    change e0 (s (s.symm v)) = b
    rw [s.apply_symm_apply]
    exact e0.apply_symm_apply b

def hamiltonianEndpointTailEquiv {m : Nat} (e : Equiv (Fin (m + 2)) Iota)
    (a b : Iota) (ha : e 0 = a) (hb : e 1 = b) :
    Equiv (Fin m) (Compl.compl ({a, b} : Finset Iota) : Finset Iota) := by
  have hOne : (1 : Fin (m + 2)) = (0 : Fin (m + 1)).succ := by
    apply Fin.ext
    simp
  have hTail0 (i : Fin m) : Not (i.succ.succ = (0 : Fin (m + 2))) := by
    intro h
    have hv := congrArg (fun x : Fin (m + 2) => x.val) h
    simp only [Fin.val_succ, Fin.val_zero] at hv
    omega
  have hTail1 (i : Fin m) : Not (i.succ.succ = (1 : Fin (m + 2))) := by
    intro h
    rw [hOne] at h
    have hv := congrArg (fun x : Fin (m + 2) => x.val) h
    simp only [Fin.val_succ, Fin.val_zero] at hv
    omega
  let f := fun i : Fin m =>
    (Subtype.mk (e i.succ.succ) (show Membership.mem
      (Compl.compl ({a, b} : Finset Iota) : Finset Iota) (e i.succ.succ) from by
      apply Finset.mem_compl.mpr
      intro h
      have hCases := Finset.mem_insert.mp h
      cases hCases with
      | inl hA => exact hTail0 i (e.injective (hA.trans ha.symm))
      | inr hB =>
          have hEq := Finset.mem_singleton.mp hB
          exact hTail1 i (e.injective (hEq.trans hb.symm))))
  have hInj : Function.Injective f := by
    intro i j h
    have hVal := congrArg Subtype.val h
    have hBoth := e.injective hVal
    have hNat := congrArg (fun x : Fin (m + 2) => x.val) hBoth
    apply Fin.ext
    simp only [Fin.val_succ] at hNat
    omega
  have hSurj : Function.Surjective f := by
    intro j
    have hJA : Not (j.val = a) := by
      intro h
      exact (Finset.mem_compl.mp j.property) (Finset.mem_insert.mpr (Or.inl h))
    have hJB : Not (j.val = b) := by
      intro h
      exact (Finset.mem_compl.mp j.property)
        (Finset.mem_insert.mpr (Or.inr (Finset.mem_singleton.mpr h)))
    let x := e.symm j.val
    have hx0 : Not (x = 0) := by
      intro h
      apply hJA
      calc
        _ = e x := (e.apply_symm_apply j.val).symm
        _ = e 0 := congrArg e h
        _ = a := ha
    have hx1 : Not (x = 1) := by
      intro h
      apply hJB
      calc
        _ = e x := (e.apply_symm_apply j.val).symm
        _ = e 1 := congrArg e h
        _ = b := hb
    have hxVal0 : Not (x.val = 0) := fun h => hx0 (Fin.ext h)
    have hxVal1 : Not (x.val = 1) := by
      intro h
      apply hx1
      apply Fin.ext
      rw [hOne]
      simpa only [Fin.val_succ, Fin.val_zero] using h
    have hx2 : 2 <= x.val := by omega
    let i : Fin m := Fin.mk (x.val - 2) (by have h := x.isLt; omega)
    have hi : i.succ.succ = x := by
      apply Fin.ext
      change (x.val - 2) + 1 + 1 = x.val
      omega
    refine Exists.intro i ?_
    apply Subtype.ext
    change e i.succ.succ = j.val
    rw [hi]
    exact e.apply_symm_apply j.val
  exact Equiv.ofBijective f (And.intro hInj hSurj)

theorem hamiltonian_endpoint_tail_val {m : Nat} (e : Equiv (Fin (m + 2)) Iota)
    (a b : Iota) (ha : e 0 = a) (hb : e 1 = b) (i : Fin m) :
    (hamiltonianEndpointTailEquiv e a b ha hb i).val = e i.succ.succ := by
  rfl

theorem hamiltonian_marked_cycle_reindex
    {Kappa : Type*} [Fintype Kappa] [DecidableEq Kappa]
    (e : Equiv Kappa Iota) (M : Matrix Iota Iota Real)
    (E : Iota -> Iota -> Prop) [DecidableRel E] :
    hamiltonianMarkedCycleSum (M.submatrix e e) (fun i j => E (e i) (e j)) =
      hamiltonianMarkedCycleSum M E := by
  have hAvoid : hamiltonianAvoidingKernel (M.submatrix e e) (fun i j => E (e i) (e j)) =
      (hamiltonianAvoidingKernel M E).submatrix e e := by
    ext i j
    by_cases h : E (e i) (e j)
    . simp only [hamiltonianAvoidingKernel, Matrix.submatrix_apply, ite_eq_left h]
    . simp only [hamiltonianAvoidingKernel, Matrix.submatrix_apply, ite_eq_right h]
  calc
    _ = hamiltonianCycleSum (M.submatrix e e) -
        hamiltonianCycleSum
          (hamiltonianAvoidingKernel (M.submatrix e e) (fun i j => E (e i) (e j))) :=
      hamiltonian_marked_cycle_exact_complement _ _
    _ = hamiltonianCycleSum M - hamiltonianCycleSum (hamiltonianAvoidingKernel M E) := by
      rw [hAvoid, hamiltonian_cycle_sum_reindex e, hamiltonian_cycle_sum_reindex e]
    _ = _ := (hamiltonian_marked_cycle_exact_complement M E).symm

theorem hamiltonian_finite_endpoint_marked_path_transfer
    (M : Matrix Iota Iota Real) (a b : Iota) (hab : Not (a = b))
    (E : (Compl.compl ({a, b} : Finset Iota) : Finset Iota) ->
      (Compl.compl ({a, b} : Finset Iota) : Finset Iota) -> Prop) [DecidableRel E]
    (kappa : Real) (hNonneg : forall i j, 0 <= M i j)
    (hClosing : forall i j, E i j ->
      kappa * M i.val j.val <= M i.val b * M a j.val) :
    let J : Finset Iota := Compl.compl ({a, b} : Finset Iota)
    kappa * hamiltonianMarkedCycleSum
        (M.submatrix (fun i : J => i.val) (fun i : J => i.val)) E <=
      hamiltonianPrescribedPathSum M a b := by
  let J : Finset Iota := Compl.compl ({a, b} : Finset Iota)
  let m := Fintype.card Iota - 2
  have hPair : ({a, b} : Finset Iota).card = 2 := by simp [hab]
  have hTwo : 2 <= Fintype.card Iota := by
    rw [<- hPair]
    exact Finset.card_le_univ _
  have hSize : Fintype.card Iota = m + 2 := by dsimp only [m]; omega
  have hLabels := hamiltonian_two_endpoint_labels a b hab m hSize
  let e := hLabels.choose
  have he := hLabels.choose_spec
  let tail := hamiltonianEndpointTailEquiv e a b he.1 he.2
  let L := M.submatrix e e
  let Q := M.submatrix (fun i : J => i.val) (fun i : J => i.val)
  let EFin := fun i j : Fin m => E (tail i) (tail j)
  have hInterior :
      L.submatrix (fun i : Fin m => i.succ.succ) (fun i : Fin m => i.succ.succ) =
        Q.submatrix tail tail := by
    ext i j
    change M (e i.succ.succ) (e j.succ.succ) = M (tail i).val (tail j).val
    rw [hamiltonian_endpoint_tail_val, hamiltonian_endpoint_tail_val]
  have hCloseFin (i j : Fin m) (h : EFin i j) :
      kappa * L i.succ.succ j.succ.succ <= L i.succ.succ 1 * L 0 j.succ.succ := by
    have hActual := hClosing (tail i) (tail j) h
    change kappa * M (e i.succ.succ) (e j.succ.succ) <=
      M (e i.succ.succ) (e 1) * M (e 0) (e j.succ.succ)
    rw [he.1, he.2]
    simpa only [tail, hamiltonian_endpoint_tail_val] using hActual
  have hTransfer := hamiltonian_marked_cycle_path_transfer L EFin kappa
    (fun i j => hNonneg (e i) (e j)) hCloseFin
  change kappa * hamiltonianMarkedCycleSum
      (L.submatrix (fun i : Fin m => i.succ.succ) (fun i : Fin m => i.succ.succ))
      (fun i j => E (tail i) (tail j)) <= hamiltonianPrescribedPathSum L 0 1 at hTransfer
  rw [hInterior, hamiltonian_marked_cycle_reindex tail Q E] at hTransfer
  rw [hamiltonian_prescribed_path_reindex e M 0 1, he.1, he.2] at hTransfer
  exact hTransfer

end PrimeFactorOscillations

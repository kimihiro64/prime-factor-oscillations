/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.HamiltonianEndpointPathTransfer

/-! # Full signed native coprime endpoint-path lower consumer

The actual double-deleted support and its marked set are transported
together. The positive base-cycle mass and complete avoidance
allowance remain coupled through the exact factor one over totient.
-/

set_option autoImplicit false
set_option Elab.async false

open scoped Classical

noncomputable section

namespace PrimeFactorOscillations

variable {n : Nat} [NeZero n]

def hamiltonianCoprimeInteriorComplementEquiv (a b : ZMod n) :
    Equiv (Compl.compl ({a, b} : Finset (ZMod n)) : Finset (ZMod n))
      (hamiltonianCoprimeInterior a b) where
  toFun := fun j => Subtype.mk j.val (by
    have hNot := Finset.mem_compl.mp j.property
    have hA : Not (j.val = a) := fun h =>
      hNot (Finset.mem_insert.mpr (Or.inl h))
    have hB : Not (j.val = b) := fun h =>
      hNot (Finset.mem_insert.mpr (Or.inr (Finset.mem_singleton.mpr h)))
    exact Finset.mem_erase.mpr (And.intro hB
      (Finset.mem_erase.mpr (And.intro hA (Finset.mem_univ _)))))
  invFun := fun j => Subtype.mk j.val (by
    have hB := (Finset.mem_erase.mp j.property).1
    have hA := (Finset.mem_erase.mp (Finset.mem_erase.mp j.property).2).1
    apply Finset.mem_compl.mpr
    intro h
    cases Finset.mem_insert.mp h with
    | inl hA' => exact hA hA'
    | inr hB' => exact hB (Finset.mem_singleton.mp hB'))
  left_inv := by intro j; apply Subtype.ext; rfl
  right_inv := by intro j; apply Subtype.ext; rfl

theorem hamiltonian_coprime_interior_complement_val (a b : ZMod n)
    (i : (Compl.compl ({a, b} : Finset (ZMod n)) : Finset (ZMod n))) :
    (hamiltonianCoprimeInteriorComplementEquiv a b i).val = i.val := by
  rfl

theorem hamiltonian_coprime_marked_cycle_path_transfer
    (a b : ZMod n) (hab : Not (a = b)) :
    (1 / (n.totient : Real)) *
        hamiltonianMarkedCycleSum (hamiltonianCoprimeInteriorKernel a b)
          (fun i j => hamiltonianCoprimeClosingMark a b i.val j.val) <=
      hamiltonianPrescribedPathSum (hamiltonianCoprimeKernel (n := n)) a b := by
  let J : Finset (ZMod n) := Compl.compl ({a, b} : Finset (ZMod n))
  let e := hamiltonianCoprimeInteriorComplementEquiv a b
  let M := (hamiltonianCoprimeKernel (n := n)).submatrix
    (fun i : J => i.val) (fun i : J => i.val)
  let E := fun i j : J => hamiltonianCoprimeClosingMark a b i.val j.val
  have hClosing (i j : J) (h : E i j) :
      (1 / (n.totient : Real)) * hamiltonianCoprimeKernel i.val j.val <=
        hamiltonianCoprimeKernel i.val b * hamiltonianCoprimeKernel a j.val := by
    change hamiltonianCoprimeRelation a j.val /\ hamiltonianCoprimeRelation i.val b at h
    rw [hamiltonian_coprime_kernel_indicator i.val b,
      hamiltonian_coprime_kernel_indicator a j.val, ite_eq_left h.2, ite_eq_left h.1]
    exact mul_le_mul_of_nonneg_left (hamiltonian_coprime_kernel_entry_cap i.val j.val)
      (div_nonneg (by norm_num) (Nat.cast_nonneg _))
  have hActual := hamiltonian_finite_endpoint_marked_path_transfer
    (hamiltonianCoprimeKernel (n := n)) a b hab E (1 / (n.totient : Real))
    hamiltonian_coprime_kernel_nonnegative hClosing
  have hReindex := hamiltonian_marked_cycle_reindex e (hamiltonianCoprimeInteriorKernel a b)
    (fun i j => hamiltonianCoprimeClosingMark a b i.val j.val)
  change hamiltonianMarkedCycleSum M E =
    hamiltonianMarkedCycleSum (hamiltonianCoprimeInteriorKernel a b)
      (fun i j => hamiltonianCoprimeClosingMark a b i.val j.val) at hReindex
  rw [<- hReindex]
  exact hActual

theorem hamiltonian_coprime_path_full_signed_lower [Nontrivial (ZMod n)]
    (a b : ZMod n) (hab : Not (a = b))
    (hParity : Odd n \/ Odd (-(a - b)).val) (hd4 : 4 <= (n.totient : Real)) :
    (1 / (n.totient : Real)) *
        (hamiltonianCycleSum (hamiltonianCoprimeInteriorKernel a b) -
          Real.exp (-((n - 2 : Nat) : Real) -
            ((n.totient : Real) ^ 2 / (2 * (n : Real)) - 2) / 2 +
              64 * ((n : Real) / (n.totient : Real)) * Real.log (2 * (n : Real)))) <=
      hamiltonianPrescribedPathSum (hamiltonianCoprimeKernel (n := n)) a b := by
  let M := hamiltonianCoprimeInteriorKernel a b
  let E := fun i j : hamiltonianCoprimeInterior a b =>
    hamiltonianCoprimeClosingMark a b i.val j.val
  have hAvoid := hamiltonian_coprime_interior_avoidance_upper a b hab hParity hd4
  have hMass : hamiltonianCycleSum M -
      Real.exp (-((n - 2 : Nat) : Real) -
        ((n.totient : Real) ^ 2 / (2 * (n : Real)) - 2) / 2 +
          64 * ((n : Real) / (n.totient : Real)) * Real.log (2 * (n : Real))) <=
        hamiltonianMarkedCycleSum M E := by
    rw [hamiltonian_marked_cycle_exact_complement]
    linarith only [hAvoid]
  have hWeight : 0 <= 1 / (n.totient : Real) :=
    div_nonneg (by norm_num) (Nat.cast_nonneg _)
  exact (mul_le_mul_of_nonneg_left hMass hWeight).trans
    (hamiltonian_coprime_marked_cycle_path_transfer a b hab)

end PrimeFactorOscillations

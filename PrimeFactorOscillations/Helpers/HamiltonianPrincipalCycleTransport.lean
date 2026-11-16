/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.HamiltonianCoprimePathSigned
import PrimeFactorOscillations.Helpers.HamiltonianCycleTransport

/-! # Exact cycle transport on principal deleted supports -/

set_option autoImplicit false
set_option Elab.async false

open scoped Classical

noncomputable section

namespace PrimeFactorOscillations

variable {I J R : Type*}
variable [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]

def hamiltonianPrincipalCycleSum [CommSemiring R]
    (M : Matrix I I R) (D : Finset I) : R :=
  hamiltonianCycleSum
    (M.submatrix (fun i : (Compl.compl D : Finset I) => i.val)
      (fun i : (Compl.compl D : Finset I) => i.val))

def hamiltonianPrincipalComplementEquiv (e : Equiv I J) (D : Finset I) :
    Equiv (Compl.compl D : Finset I)
      (Compl.compl (D.map e.toEmbedding) : Finset J) where
  toFun := fun i => Subtype.mk (e i.val) (by
    apply Finset.mem_compl.mpr
    intro h
    let w := Finset.mem_map.mp h
    have hx : Membership.mem D w.choose := w.choose_spec.1
    have he : w.choose = i.val := e.injective w.choose_spec.2
    exact (Finset.mem_compl.mp i.property) (he.subst hx))
  invFun := fun j => Subtype.mk (e.symm j.val) (by
    apply Finset.mem_compl.mpr
    intro h
    apply (Finset.mem_compl.mp j.property)
    exact Finset.mem_map.mpr
      (Exists.intro (e.symm j.val) (And.intro h (e.apply_symm_apply j.val))))
  left_inv := by intro i; apply Subtype.ext; exact e.symm_apply_apply i.val
  right_inv := by intro j; apply Subtype.ext; exact e.apply_symm_apply j.val

theorem hamiltonian_principal_cycle_reindex [CommSemiring R]
    (e : Equiv I J) (M : Matrix J J R) (D : Finset I) :
    hamiltonianPrincipalCycleSum (M.submatrix e e) D =
      hamiltonianPrincipalCycleSum M (D.map e.toEmbedding) := by
  exact hamiltonian_cycle_sum_reindex (hamiltonianPrincipalComplementEquiv e D)
    (M.submatrix
      (fun j : (Compl.compl (D.map e.toEmbedding) : Finset J) => j.val)
      (fun j : (Compl.compl (D.map e.toEmbedding) : Finset J) => j.val))

theorem hamiltonian_coprime_interior_cycle_principal
    {n : Nat} [NeZero n] (a b : ZMod n) :
    hamiltonianCycleSum (hamiltonianCoprimeInteriorKernel a b) =
      hamiltonianPrincipalCycleSum (hamiltonianCoprimeKernel (n := n)) {a, b} := by
  have h := hamiltonian_cycle_sum_reindex
    (hamiltonianCoprimeInteriorComplementEquiv a b)
    (hamiltonianCoprimeInteriorKernel a b)
  exact h.symm

end PrimeFactorOscillations

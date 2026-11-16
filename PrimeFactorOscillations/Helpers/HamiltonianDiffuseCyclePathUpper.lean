/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.HamiltonianDiffusePermanentBound
import PrimeFactorOscillations.Helpers.HamiltonianPrescribedPathMinor

/-! # Actual cycle and uniform endpoint-path diffuse upper bounds

The exact existing cycle restriction and endpoint minor are consumed.
Every original edge weight is retained; the prescribed closing edge
has weight one and never enters the minor cap or its row budget.
-/

set_option autoImplicit false
set_option Elab.async false

noncomputable section

namespace PrimeFactorOscillations

theorem hamiltonian_permanent_row_orientation
    {I : Type*} [Fintype I] [DecidableEq I] (P : Matrix I I Real) :
    finitePermutationSum P =
      Finset.univ.sum (fun sigma : Equiv.Perm I => Finset.univ.prod (fun i => P i (sigma i))) := by
  rw [<- finitePermutationSum_transpose P]
  rfl

theorem hamiltonian_diffuse_cycle_entropy_upper
    (n : Nat) (P : Matrix (Fin (n + 2)) (Fin (n + 2)) Real) (c : Real)
    (hc : 0 < c) (hc1 : c <= 1)
    (hNonneg : forall i j, 0 <= P i j)
    (hRow : forall i, Finset.univ.sum (fun j => P i j) <= 1)
    (hCap : forall i j, P i j <= c) :
    hamiltonianCycleSum P <=
      Real.exp (-(n + 2 : Real) + 1 + (n + 2 : Real) * (2 * c - c * Real.log c)) := by
  have h := hamiltonian_cycle_sum_le_permanent P hNonneg
  rw [hamiltonian_permanent_row_orientation] at h
  exact h.trans (hamiltonian_diffuse_permanent_entropy_upper n P c hc hc1 hNonneg hRow hCap)

theorem hamiltonian_diffuse_prescribed_path_zero_upper
    (n : Nat) (P : Matrix (Fin (n + 3)) (Fin (n + 3)) Real)
    (b : Fin (n + 3)) (c : Real) (hc : 0 < c) (hc1 : c <= 1)
    (hNonneg : forall i j, 0 <= P i j)
    (hRow : forall i, Finset.univ.sum (fun j => P i j) <= 1)
    (hCap : forall i j, P i j <= c) :
    hamiltonianPrescribedPathSum P 0 b <=
      Real.exp (-(n + 2 : Real) + 1 + (n + 2 : Real) * (2 * c - c * Real.log c)) := by
  let K := P.submatrix (fun i : Fin (n + 2) => Equiv.swap 0 b i.succ) Fin.succ
  have hKNonneg (i j : Fin (n + 2)) : 0 <= K i j := hNonneg _ _
  have hKCap (i j : Fin (n + 2)) : K i j <= c := hCap _ _
  have hKRow (i : Fin (n + 2)) : Finset.univ.sum (fun j => K i j) <= 1 := by
    have h := hRow (Equiv.swap 0 b i.succ)
    rw [Fin.sum_univ_succ] at h
    have hRemoved := hNonneg (Equiv.swap 0 b i.succ) 0
    change Finset.univ.sum (fun j : Fin (n + 2) =>
      P (Equiv.swap 0 b i.succ) j.succ) <= 1
    linarith only [h, hRemoved]
  have hMinor := hamiltonian_prescribed_path_le_minor P b hNonneg
  change hamiltonianPrescribedPathSum P 0 b <= finitePermutationSum K at hMinor
  rw [hamiltonian_permanent_row_orientation] at hMinor
  exact hMinor.trans
    (hamiltonian_diffuse_permanent_entropy_upper n K c hc hc1 hKNonneg hKRow hKCap)

theorem hamiltonian_diffuse_prescribed_path_uniform_upper
    (n : Nat) (P : Matrix (Fin (n + 3)) (Fin (n + 3)) Real)
    (a b : Fin (n + 3)) (c : Real) (hc : 0 < c) (hc1 : c <= 1)
    (hNonneg : forall i j, 0 <= P i j)
    (hRow : forall i, Finset.univ.sum (fun j => P i j) <= 1)
    (hCap : forall i j, P i j <= c) :
    hamiltonianPrescribedPathSum P a b <=
      Real.exp (-(n + 2 : Real) + 1 + (n + 2 : Real) * (2 * c - c * Real.log c)) := by
  let e : Equiv.Perm (Fin (n + 3)) := Equiv.swap 0 a
  have hRowNew (i : Fin (n + 3)) : Finset.univ.sum (fun j => P.submatrix e e i j) <= 1 := by
    change Finset.univ.sum (fun j => P (e i) (e j)) <= 1
    rw [Equiv.sum_comp e]
    exact hRow (e i)
  have h := hamiltonian_diffuse_prescribed_path_zero_upper n (P.submatrix e e) (e.symm b)
    c hc hc1 (fun i j => hNonneg (e i) (e j)) hRowNew (fun i j => hCap (e i) (e j))
  rw [hamiltonian_prescribed_path_reindex] at h
  have hZero : e 0 = a := Equiv.swap_apply_left 0 a
  simpa only [hZero, Equiv.apply_symm_apply] using h

theorem hamiltonian_diffuse_prescribed_path_sqrt_upper
    (n : Nat) (P : Matrix (Fin (n + 3)) (Fin (n + 3)) Real)
    (a b : Fin (n + 3)) (c : Real) (hc : 0 < c) (hc1 : c <= 1)
    (hNonneg : forall i j, 0 <= P i j)
    (hRow : forall i, Finset.univ.sum (fun j => P i j) <= 1)
    (hCap : forall i j, P i j <= c) :
    hamiltonianPrescribedPathSum P a b <=
      Real.exp (-(n + 2 : Real) + 1 + 2 * (n + 2 : Real) * Real.sqrt c) := by
  have hEntropy := hamiltonian_cap_entropy_sqrt c hc
  have hScaled := mul_le_mul_of_nonneg_left hEntropy (by positivity : 0 <= (n + 2 : Real))
  have hExponent : -(n + 2 : Real) + 1 + (n + 2 : Real) * (2 * c - c * Real.log c) <=
      -(n + 2 : Real) + 1 + 2 * (n + 2 : Real) * Real.sqrt c := by
    nlinarith only [hScaled]
  exact (hamiltonian_diffuse_prescribed_path_uniform_upper n P a b c hc hc1 hNonneg hRow hCap).trans
    (Real.exp_le_exp.mpr hExponent)

end PrimeFactorOscillations

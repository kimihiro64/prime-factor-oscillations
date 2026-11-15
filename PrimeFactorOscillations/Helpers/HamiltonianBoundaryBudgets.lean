/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.HamiltonianBoundaryEquations

/-! # Boundary row and source budgets for nonlinear scaling

The full signed source difference is first identified exactly.
Absolute estimates apply only to the boundary correction and removed
source, not to the retained leading term K ell.
-/

set_option autoImplicit false
set_option Elab.async false

noncomputable section

namespace PrimeFactorOscillations

variable {Iota : Type*} [Fintype Iota] [DecidableEq Iota]

theorem hamiltonian_retained_sum_le (f : Iota -> Real) (D : Finset Iota)
    (hf : forall i, 0 <= f i) :
    Finset.sum Finset.univ (fun i : (Compl.compl D : Finset Iota) => f i.val) <=
      Finset.sum Finset.univ f := by
  have hSplit := hamiltonian_sum_support_partition f D
  have hNonneg : 0 <= Finset.sum Finset.univ (fun d : D => f d.val) :=
    Finset.sum_nonneg (fun d _ => hf d.val)
  linarith only [hSplit, hNonneg]

theorem hamiltonianBoundaryKernel_row_bound
    (K : Matrix Iota Iota Real) (D : Finset Iota) (e b : Real)
    (hRow : forall i, Finset.sum Finset.univ (fun j => abs (K i j)) <= b)
    (hError : forall i j : (Compl.compl D : Finset Iota),
      abs (hamiltonianBoundaryKernel K D i j - K i.val j.val) <= e)
    (i : (Compl.compl D : Finset Iota)) :
    Finset.sum Finset.univ (fun j => abs (hamiltonianBoundaryKernel K D i j)) <=
      b + ((Compl.compl D : Finset Iota).card : Real) * e := by
  have hEach (j : (Compl.compl D : Finset Iota)) :
      abs (hamiltonianBoundaryKernel K D i j) <= abs (K i.val j.val) + e := by
    have h := abs_add_le (hamiltonianBoundaryKernel K D i j - K i.val j.val) (K i.val j.val)
    have hAbs : abs (hamiltonianBoundaryKernel K D i j) <=
        abs (hamiltonianBoundaryKernel K D i j - K i.val j.val) + abs (K i.val j.val) := by
      simpa only [sub_add_cancel] using h
    linarith only [hAbs, hError i j]
  have hRet : Finset.sum Finset.univ
      (fun j : (Compl.compl D : Finset Iota) => abs (K i.val j.val)) <= b :=
    le_trans (hamiltonian_retained_sum_le (fun j => abs (K i.val j)) D
      (fun _ => abs_nonneg _)) (hRow i.val)
  calc
    _ <= Finset.sum Finset.univ
        (fun j : (Compl.compl D : Finset Iota) => abs (K i.val j.val) + e) :=
      Finset.sum_le_sum (fun j _ => hEach j)
    _ = Finset.sum Finset.univ
        (fun j : (Compl.compl D : Finset Iota) => abs (K i.val j.val)) +
          ((Compl.compl D : Finset Iota).card : Real) * e := by
      rw [Finset.sum_add_distrib]
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_coe, nsmul_eq_mul]
    _ <= _ := add_le_add hRet (le_refl _)

theorem hamiltonianBoundaryKernel_source_error
    (K : Matrix Iota Iota Real) (D : Finset Iota) (x : Iota -> Real)
    (e c mass deletedMass : Real) (he : 0 <= e) (hc : 0 <= c)
    (hError : forall i j : (Compl.compl D : Finset Iota),
      abs (hamiltonianBoundaryKernel K D i j - K i.val j.val) <= e)
    (hCross : forall (i : (Compl.compl D : Finset Iota)) (d : D),
      abs (K i.val d.val) <= c)
    (hMass : Finset.sum Finset.univ (fun j => abs (x j)) <= mass)
    (hDeleted : Finset.sum Finset.univ (fun d : D => abs (x d.val)) <= deletedMass)
    (i : (Compl.compl D : Finset Iota)) :
    abs ((hamiltonianBoundaryKernel K D).mulVec (fun j => x j.val) i -
      K.mulVec x i.val) <= e * mass + c * deletedMass := by
  let R : Finset Iota := Compl.compl D
  let G := hamiltonianBoundaryKernel K D
  have hOriginal : K.mulVec x i.val =
      Finset.sum Finset.univ (fun d : D => K i.val d.val * x d.val) +
        Finset.sum Finset.univ (fun j : R => K i.val j.val * x j.val) :=
    hamiltonian_sum_support_partition (fun k => K i.val k * x k) D
  have hExact : G.mulVec (fun j => x j.val) i - K.mulVec x i.val =
      Finset.sum Finset.univ (fun j : R => (G i j - K i.val j.val) * x j.val) -
        Finset.sum Finset.univ (fun d : D => K i.val d.val * x d.val) := by
    change Finset.sum Finset.univ (fun j : R => G i j * x j.val) -
      K.mulVec x i.val = _
    rw [hOriginal]
    simp only [sub_mul, Finset.sum_sub_distrib]
    ring
  have hRetMass : Finset.sum Finset.univ (fun j : R => abs (x j.val)) <= mass :=
    le_trans (hamiltonian_retained_sum_le (fun k => abs (x k)) D
      (fun _ => abs_nonneg _)) hMass
  have hRet : abs (Finset.sum Finset.univ
      (fun j : R => (G i j - K i.val j.val) * x j.val)) <= e * mass := by
    calc
      _ <= Finset.sum Finset.univ
          (fun j : R => abs ((G i j - K i.val j.val) * x j.val)) :=
        Finset.abs_sum_le_sum_abs _ _
      _ = Finset.sum Finset.univ
          (fun j : R => abs (G i j - K i.val j.val) * abs (x j.val)) := by
        simp only [abs_mul]
      _ <= Finset.sum Finset.univ (fun j : R => e * abs (x j.val)) :=
        Finset.sum_le_sum (fun j _ => mul_le_mul_of_nonneg_right
          (hError i j) (abs_nonneg _))
      _ = e * Finset.sum Finset.univ (fun j : R => abs (x j.val)) := by
        rw [Finset.mul_sum]
      _ <= e * mass := mul_le_mul_of_nonneg_left hRetMass he
  have hDel : abs (Finset.sum Finset.univ
      (fun d : D => K i.val d.val * x d.val)) <= c * deletedMass := by
    calc
      _ <= Finset.sum Finset.univ (fun d : D => abs (K i.val d.val * x d.val)) :=
        Finset.abs_sum_le_sum_abs _ _
      _ = Finset.sum Finset.univ (fun d : D => abs (K i.val d.val) * abs (x d.val)) := by
        simp only [abs_mul]
      _ <= Finset.sum Finset.univ (fun d : D => c * abs (x d.val)) :=
        Finset.sum_le_sum (fun d _ => mul_le_mul_of_nonneg_right
          (hCross i d) (abs_nonneg _))
      _ = c * Finset.sum Finset.univ (fun d : D => abs (x d.val)) := by
        rw [Finset.mul_sum]
      _ <= _ := mul_le_mul_of_nonneg_left hDeleted hc
  rw [hExact]
  have hAbs := norm_sub_le
    (Finset.sum Finset.univ (fun j : R => (G i j - K i.val j.val) * x j.val))
    (Finset.sum Finset.univ (fun d : D => K i.val d.val * x d.val))
  rw [Real.norm_eq_abs, Real.norm_eq_abs, Real.norm_eq_abs] at hAbs
  exact le_trans hAbs (add_le_add hRet hDel)

end PrimeFactorOscillations

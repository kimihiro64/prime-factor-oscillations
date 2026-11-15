/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import Mathlib.Tactic.FieldSimp
import PrimeFactorOscillations.Helpers.HamiltonianDeletedBlockInverse

/-! # The actual boundary Schur correction and its two-power entry bound

Only the explicit boundary correction is estimated by absolute values.
The kernel is defined by the full signed Schur product.
-/

set_option autoImplicit false
set_option Elab.async false

open scoped Matrix.Norms.L2Operator

noncomputable section

namespace PrimeFactorOscillations

variable {Iota : Type*} [Fintype Iota] [DecidableEq Iota]

def hamiltonianBoundaryKernel (K : Matrix Iota Iota Real) (D : Finset Iota) :
    Matrix (Compl.compl D : Finset Iota) (Compl.compl D : Finset Iota) Real :=
  K.submatrix (fun i => i.val) (fun j => j.val) -
    K.submatrix (fun i => i.val) (fun j : D => j.val) *
      Ring.inverse (K.submatrix (fun i : D => i.val) (fun j : D => j.val)) *
        K.submatrix (fun i : D => i.val) (fun j => j.val)

theorem hamiltonianBoundaryKernel_entry_error (K : Matrix Iota Iota Real)
    (D : Finset Iota) (c : Real) (hc : 0 <= c)
    (hLeft : forall (i : (Compl.compl D : Finset Iota)) (d : D),
      abs (K i.val d.val) <= c)
    (hRight : forall (d : D) (j : (Compl.compl D : Finset Iota)),
      abs (K d.val j.val) <= c)
    (hInv : forall d : D, Finset.sum Finset.univ
      (fun e : D => abs (Ring.inverse (K.submatrix
        (fun k : D => k.val) (fun k : D => k.val)) d e)) <= 2)
    (i j : (Compl.compl D : Finset Iota)) :
    abs (hamiltonianBoundaryKernel K D i j - K i.val j.val) <=
      2 * (D.card : Real) * c ^ 2 := by
  let A : Matrix (Compl.compl D : Finset Iota) D Real :=
    K.submatrix (fun i => i.val) (fun d => d.val)
  let E := Ring.inverse (K.submatrix (fun d : D => d.val) (fun e : D => e.val))
  let B : Matrix D (Compl.compl D : Finset Iota) Real :=
    K.submatrix (fun d => d.val) (fun j => j.val)
  have hInner (d : D) : abs ((E * B) d j) <= 2 * c := by
    rw [Matrix.mul_apply]
    calc
      _ <= Finset.sum Finset.univ (fun e => abs (E d e * B e j)) :=
        Finset.abs_sum_le_sum_abs _ _
      _ = Finset.sum Finset.univ (fun e => abs (E d e) * abs (K e.val j.val)) := by
        simp only [abs_mul, B, Matrix.submatrix_apply]
      _ <= Finset.sum Finset.univ (fun e => abs (E d e) * c) :=
        Finset.sum_le_sum (fun e _ => mul_le_mul_of_nonneg_left
          (hRight e j) (abs_nonneg _))
      _ = Finset.sum Finset.univ (fun e => abs (E d e)) * c := by
        rw [Finset.sum_mul]
      _ <= 2 * c := mul_le_mul_of_nonneg_right (hInv d) hc
  have hOuter : abs ((A * E * B) i j) <= 2 * (D.card : Real) * c ^ 2 := by
    rw [Matrix.mul_assoc, Matrix.mul_apply]
    calc
      _ <= Finset.sum Finset.univ (fun d => abs (A i d * (E * B) d j)) :=
        Finset.abs_sum_le_sum_abs _ _
      _ = Finset.sum Finset.univ (fun d => abs (K i.val d.val) * abs ((E * B) d j)) := by
        simp only [abs_mul, A, Matrix.submatrix_apply]
      _ <= Finset.sum Finset.univ (fun _ : D => c * (2 * c)) :=
        Finset.sum_le_sum (fun d _ => mul_le_mul (hLeft i d) (hInner d)
          (abs_nonneg _) hc)
      _ = _ := by simp only [Finset.sum_const, Finset.card_univ,
        Fintype.card_coe, nsmul_eq_mul]; ring
  have hDiff : hamiltonianBoundaryKernel K D i j - K i.val j.val =
      -((A * E * B) i j) := by
    change K i.val j.val - (A * E * B) i j - K i.val j.val = _
    ring
  rw [hDiff, abs_neg]
  exact hOuter

variable [Nonempty Iota]

theorem stochastic_boundary_kernel_entry_error
    (T : Matrix Iota Iota Real) (D : Finset (Sum Iota Iota)) (q a rho : Real)
    (hq : (Fintype.card Iota : Real) * q = 1) (ha : 1 <= a)
    (hRow : forall i, Finset.sum Finset.univ (fun j => T i j) = 1)
    (hCol : forall j, Finset.sum Finset.univ (fun i => T i j) = 1)
    (hNonneg : forall i j, 0 <= T i j) (hUpper : forall i j, T i j <= a * q)
    (hNorm : norm (centeredKernel T q) <= rho) (hRho : rho < 1)
    (hSmall : (D.card : Real) * (4 * a * q) <= (1 - rho) / 2)
    (i j : (Compl.compl D : Finset (Sum Iota Iota))) :
    abs (hamiltonianBoundaryKernel (hamiltonianRepairKernel T q) D i j -
      hamiltonianRepairKernel T q i.val j.val) <=
      2 * (D.card : Real) * (4 * a * q / (1 - rho)) ^ 2 := by
  have hGap : 0 < 1 - rho := sub_pos.mpr hRho
  have hN : 0 < (Fintype.card Iota : Real) := Nat.cast_pos.mpr Fintype.card_pos
  have hq0 : 0 <= q := by nlinarith only [hq, hN]
  have ha0 : 0 <= a := le_trans (by norm_num) ha
  have hc : 0 <= 4 * a * q / (1 - rho) := by positivity
  have hOff (k l : Sum Iota Iota) (hne : Not (k = l)) :
      abs (hamiltonianRepairKernel T q k l) <= 4 * a * q / (1 - rho) := by
    have h := stochastic_repair_kernel_entry T q a rho hq ha
      hRow hCol hNonneg hUpper hNorm hRho k l
    simp only [Matrix.sub_apply, Matrix.one_apply, if_neg hne, sub_zero] at h
    have hDen : Not (1 - rho = 0) := ne_of_gt hGap
    have hClear : (1 - rho) * (4 * a * q / (1 - rho)) = 4 * a * q := by
      field_simp
    nlinarith only [h, hClear, hGap]
  have hLeft (k : (Compl.compl D : Finset (Sum Iota Iota))) (d : D) :
      abs (hamiltonianRepairKernel T q k.val d.val) <= 4 * a * q / (1 - rho) := by
    apply hOff
    intro heq
    have hkd : Membership.mem D k.val := by rw [heq]; exact d.property
    exact (Finset.mem_compl.mp k.property) hkd
  have hRight (d : D) (k : (Compl.compl D : Finset (Sum Iota Iota))) :
      abs (hamiltonianRepairKernel T q d.val k.val) <= 4 * a * q / (1 - rho) := by
    apply hOff
    intro heq
    have hkd : Membership.mem D k.val := by rw [<- heq]; exact d.property
    exact (Finset.mem_compl.mp k.property) hkd
  exact hamiltonianBoundaryKernel_entry_error _ D _ hc hLeft hRight
    ((stochastic_deleted_block_inverse T D q a rho hq ha
      hRow hCol hNonneg hUpper hNorm hRho hSmall).2) i j

end PrimeFactorOscillations

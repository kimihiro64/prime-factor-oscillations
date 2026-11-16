/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.HamiltonianCovarianceSignCube
import PrimeFactorOscillations.Helpers.HamiltonianScalarSignMoments

/-! # The actual cut-row defect with every diagonal term retained

The cross-cut kernel is exactly twice the original cross block.
Its row defect is one full signed row sum times the row's own sign;
that sign has absolute value one, without an independence assumption.
-/

set_option autoImplicit false
set_option Elab.async false

noncomputable section

namespace PrimeFactorOscillations

variable {I : Type*} [Fintype I] [DecidableEq I]

def hamiltonianCrossCutKernel (P : Matrix I I Real) (e : I -> Bool) : Matrix I I Real :=
  fun i j => if e i = e j then 0 else 2 * P i j

theorem hamiltonian_cross_cut_kernel_diagonal
    (P : Matrix I I Real) (e : I -> Bool) (i : I) :
    hamiltonianCrossCutKernel P e i i = 0 := by
  simp [hamiltonianCrossCutKernel]

theorem hamiltonian_cross_cut_kernel_entry
    (P : Matrix I I Real) (e : I -> Bool) (i j : I) :
    hamiltonianCrossCutKernel P e i j =
      (1 - hamiltonianSignValue (e i) * hamiltonianSignValue (e j)) * P i j := by
  cases hi : e i <;> cases hj : e j <;>
    norm_num [hamiltonianCrossCutKernel, hamiltonianSignValue, hi, hj]

theorem hamiltonian_cross_cut_kernel_submatrix
    (P : Matrix I I Real) (e : I -> Bool) :
    (hamiltonianCrossCutKernel P e).submatrix
      (fun i : hamiltonianSignCut e => i.val)
      (fun j : (Compl.compl (hamiltonianSignCut e) : Finset I) => j.val) =
    SMul.smul (2 : Real) (P.submatrix
      (fun i : hamiltonianSignCut e => i.val)
      (fun j : (Compl.compl (hamiltonianSignCut e) : Finset I) => j.val)) := by
  ext i j
  have hi := (hamiltonian_mem_sign_cut e i.val).mp i.property
  have hj : Not (Membership.mem (hamiltonianSignCut e) j.val) :=
    Finset.mem_compl.mp j.property
  have hNe : Not (e i.val = e j.val) := by
    intro h
    exact hj ((hamiltonian_mem_sign_cut e j.val).mpr (h.symm.trans hi))
  simp only [Matrix.submatrix_apply, hamiltonianCrossCutKernel, if_neg hNe]
  rfl

theorem hamiltonian_cross_cut_row_identity
    (P : Matrix I I Real) (e : I -> Bool) (i : I)
    (hRow : Finset.univ.sum (fun j => P i j) = 1) :
    Finset.univ.sum (fun j => hamiltonianCrossCutKernel P e i j) - 1 =
      -hamiltonianSignValue (e i) * hamiltonianScalarSignSum (fun j => P i j) e := by
  simp_rw [hamiltonian_cross_cut_kernel_entry]
  calc
    _ = Finset.univ.sum (fun j => P i j -
        hamiltonianSignValue (e i) * (hamiltonianSignValue (e j) * P i j)) - 1 := by
      congr 1
      apply Finset.sum_congr rfl
      intro j hj
      ring
    _ = Finset.univ.sum (fun j => P i j) -
        hamiltonianSignValue (e i) *
          Finset.univ.sum (fun j => hamiltonianSignValue (e j) * P i j) - 1 := by
      rw [Finset.sum_sub_distrib, <- Finset.mul_sum]
    _ = _ := by rw [hRow]; unfold hamiltonianScalarSignSum; ring

theorem hamiltonian_cross_cut_row_absolute_defect
    (P : Matrix I I Real) (e : I -> Bool) (i : I)
    (hRow : Finset.univ.sum (fun j => P i j) = 1) :
    abs (Finset.univ.sum (fun j => hamiltonianCrossCutKernel P e i j) - 1) =
      abs (hamiltonianScalarSignSum (fun j => P i j) e) := by
  have hSign : abs (hamiltonianSignValue (e i)) = 1 := by
    cases h : e i <;> norm_num [hamiltonianSignValue, h]
  rw [hamiltonian_cross_cut_row_identity P e i hRow, abs_mul, abs_neg, hSign, one_mul]

theorem hamiltonian_cross_cut_kernel_symmetric
    (P : Matrix I I Real) (e : I -> Bool) (hP : P.transpose = P) :
    (hamiltonianCrossCutKernel P e).transpose = hamiltonianCrossCutKernel P e := by
  ext i j
  have hEntry : P j i = P i j := congrArg (fun M : Matrix I I Real => M i j) hP
  by_cases h : e i = e j
  case pos =>
    change (if e j = e i then (0 : Real) else 2 * P j i) =
      (if e i = e j then 0 else 2 * P i j)
    rw [if_pos h.symm, if_pos h]
  case neg =>
    have hRev : Not (e j = e i) := fun hx => h hx.symm
    simp only [Matrix.transpose_apply, hamiltonianCrossCutKernel, if_neg h, if_neg hRev]
    rw [hEntry]

end PrimeFactorOscillations

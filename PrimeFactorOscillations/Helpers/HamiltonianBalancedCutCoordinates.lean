/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.HamiltonianCutRowIdentity
import PrimeFactorOscillations.Helpers.HamiltonianFactorNormalization
import PrimeFactorOscillations.Helpers.HamiltonianInjectiveMatrixRestriction

/-! # Actual balanced cross coordinates with full degree and centering transfer

Both coordinate equivalences enumerate the original complementary supports.
Every row and column is transferred exactly, including diagonal mass in the
original full-row identity. No new edges or independent cut are introduced.
-/

set_option autoImplicit false
set_option Elab.async false

open scoped Matrix.Norms.L2Operator

noncomputable section

namespace PrimeFactorOscillations

variable {I J : Type*} [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]

def hamiltonianBalancedCrossBlock (P : Matrix I I Real) (e : I -> Bool)
    (l : Equiv J (hamiltonianSignCut e))
    (r : Equiv J (Compl.compl (hamiltonianSignCut e) : Finset I)) : Matrix J J Real :=
  fun i j => 2 * P (l i).val (r j).val

theorem hamiltonian_balanced_cross_cut_entry
    (P : Matrix I I Real) (e : I -> Bool)
    (l : Equiv J (hamiltonianSignCut e))
    (r : Equiv J (Compl.compl (hamiltonianSignCut e) : Finset I)) (i j : J) :
    hamiltonianCrossCutKernel P e (l i).val (r j).val =
      hamiltonianBalancedCrossBlock P e l r i j := by
  have hi := (hamiltonian_mem_sign_cut e (l i).val).mp (l i).property
  have hj := Finset.mem_compl.mp (r j).property
  have hNe : Not (e (l i).val = e (r j).val) := by
    intro h
    exact hj ((hamiltonian_mem_sign_cut e (r j).val).mpr (h.symm.trans hi))
  exact if_neg hNe

theorem hamiltonian_balanced_cross_row_sum
    (P : Matrix I I Real) (e : I -> Bool)
    (l : Equiv J (hamiltonianSignCut e))
    (r : Equiv J (Compl.compl (hamiltonianSignCut e) : Finset I)) (i : J) :
    Finset.univ.sum (fun j => hamiltonianBalancedCrossBlock P e l r i j) =
      Finset.univ.sum (fun k => hamiltonianCrossCutKernel P e (l i).val k) := by
  classical
  have hPart : Finset.univ.sum (fun j => hamiltonianBalancedCrossBlock P e l r i j) =
      (Compl.compl (hamiltonianSignCut e) : Finset I).sum
        (fun k => hamiltonianCrossCutKernel P e (l i).val k) := by
    apply Finset.sum_bij (fun j _ => (r j).val)
    . intro j hj
      exact (r j).property
    . intro a ha b hb hEq
      exact r.injective (Subtype.ext hEq)
    . intro k hk
      refine Exists.intro (r.symm (Subtype.mk k hk)) (Exists.intro (Finset.mem_univ _) ?_)
      exact congrArg Subtype.val (r.apply_symm_apply (Subtype.mk k hk))
    . intro j hj
      exact (hamiltonian_balanced_cross_cut_entry P e l r i j).symm
  rw [hPart]
  apply Finset.sum_subset (Finset.subset_univ _)
  intro k hk hNot
  have hkCut : Membership.mem (hamiltonianSignCut e) k := by
    by_contra h
    exact hNot (Finset.mem_compl.mpr h)
  have hi := (hamiltonian_mem_sign_cut e (l i).val).mp (l i).property
  have hkTrue := (hamiltonian_mem_sign_cut e k).mp hkCut
  exact if_pos (hi.trans hkTrue.symm)

theorem hamiltonian_balanced_cross_column_sum
    (P : Matrix I I Real) (e : I -> Bool)
    (l : Equiv J (hamiltonianSignCut e))
    (r : Equiv J (Compl.compl (hamiltonianSignCut e) : Finset I))
    (hP : P.transpose = P) (j : J) :
    Finset.univ.sum (fun i => hamiltonianBalancedCrossBlock P e l r i j) =
      Finset.univ.sum (fun k => hamiltonianCrossCutKernel P e (r j).val k) := by
  classical
  have hSym := hamiltonian_cross_cut_kernel_symmetric P e hP
  have hEntry (i : J) : hamiltonianBalancedCrossBlock P e l r i j =
      hamiltonianCrossCutKernel P e (r j).val (l i).val := by
    rw [<- hamiltonian_balanced_cross_cut_entry P e l r i j]
    exact congrArg (fun M : Matrix I I Real => M (r j).val (l i).val) hSym
  have hPart : Finset.univ.sum (fun i => hamiltonianBalancedCrossBlock P e l r i j) =
      (hamiltonianSignCut e).sum (fun k => hamiltonianCrossCutKernel P e (r j).val k) := by
    apply Finset.sum_bij (fun i _ => (l i).val)
    . intro i hi
      exact (l i).property
    . intro a ha b hb hEq
      exact l.injective (Subtype.ext hEq)
    . intro k hk
      refine Exists.intro (l.symm (Subtype.mk k hk)) (Exists.intro (Finset.mem_univ _) ?_)
      exact congrArg Subtype.val (l.apply_symm_apply (Subtype.mk k hk))
    . intro i hi
      exact hEntry i
  rw [hPart]
  apply Finset.sum_subset (Finset.subset_univ _)
  intro k hk hNot
  have hjNot := Finset.mem_compl.mp (r j).property
  have hjFalse : e (r j).val = false := by
    cases h : e (r j).val
    . rfl
    . exact False.elim (hjNot ((hamiltonian_mem_sign_cut e (r j).val).mpr h))
  have hkFalse : e k = false := by
    cases h : e k
    . rfl
    . exact False.elim (hNot ((hamiltonian_mem_sign_cut e k).mpr h))
  exact if_pos (hjFalse.trans hkFalse.symm)

theorem hamiltonian_balanced_cross_degree_defects
    (P : Matrix I I Real) (e : I -> Bool)
    (l : Equiv J (hamiltonianSignCut e))
    (r : Equiv J (Compl.compl (hamiltonianSignCut e) : Finset I))
    (hP : P.transpose = P) (eps : Real)
    (hRows : forall k, abs (Finset.univ.sum
      (fun j => hamiltonianCrossCutKernel P e k j) - 1) <= eps) :
    And
      (forall i, abs (Finset.univ.sum
        (fun j => hamiltonianBalancedCrossBlock P e l r i j) - 1) <= eps)
      (forall j, abs (Finset.univ.sum
        (fun i => hamiltonianBalancedCrossBlock P e l r i j) - 1) <= eps) := by
  constructor
  . intro i
    rw [hamiltonian_balanced_cross_row_sum]
    exact hRows (l i).val
  . intro j
    rw [hamiltonian_balanced_cross_column_sum P e l r hP]
    exact hRows (r j).val

theorem hamiltonian_balanced_cross_centered_identity
    (P : Matrix I I Real) (e : I -> Bool)
    (l : Equiv J (hamiltonianSignCut e))
    (r : Equiv J (Compl.compl (hamiltonianSignCut e) : Finset I))
    (q : Real) :
    centeredKernel (hamiltonianBalancedCrossBlock P e l r) (2 * q) =
      SMul.smul (2 : Real)
        ((centeredKernel P q).submatrix (fun i => (l i).val) (fun j => (r j).val)) := by
  ext i j
  change 2 * P (l i).val (r j).val - 2 * q =
    2 * (P (l i).val (r j).val - q)
  ring

theorem hamiltonian_balanced_cross_centered_norm
    (P : Matrix I I Real) (e : I -> Bool)
    (l : Equiv J (hamiltonianSignCut e))
    (r : Equiv J (Compl.compl (hamiltonianSignCut e) : Finset I))
    (q : Real) :
    norm (centeredKernel (hamiltonianBalancedCrossBlock P e l r) (2 * q)) <=
      2 * norm ((centeredKernel P q).submatrix
        (fun i : hamiltonianSignCut e => i.val)
        (fun j : (Compl.compl (hamiltonianSignCut e) : Finset I) => j.val)) := by
  have h := hamiltonian_injective_submatrix_norm l r l.injective r.injective
    ((centeredKernel P q).submatrix
      (fun i : hamiltonianSignCut e => i.val)
      (fun j : (Compl.compl (hamiltonianSignCut e) : Finset I) => j.val))
  rw [hamiltonian_balanced_cross_centered_identity, hamiltonian_matrix_real_smul_norm]
  have hTwo : norm (2 : Real) = 2 := by norm_num
  rw [hTwo]
  exact mul_le_mul_of_nonneg_left h (by norm_num)

theorem hamiltonian_balanced_cross_entry_bounds
    (P : Matrix I I Real) (e : I -> Bool)
    (l : Equiv J (hamiltonianSignCut e))
    (r : Equiv J (Compl.compl (hamiltonianSignCut e) : Finset I))
    (alpha : Real) (hNonneg : forall i j, 0 <= P i j)
    (hCap : forall i j, P i j <= alpha) (i j : J) :
    And (0 <= hamiltonianBalancedCrossBlock P e l r i j)
      (hamiltonianBalancedCrossBlock P e l r i j <= 2 * alpha) := by
  exact And.intro (mul_nonneg (by norm_num) (hNonneg _ _))
    (mul_le_mul_of_nonneg_left (hCap _ _) (by norm_num))

theorem hamiltonian_balanced_reference_factor
    [Nonempty J] (hSize : Fintype.card I = 2 * Fintype.card J) :
    2 * (1 / (Fintype.card I : Real)) = 1 / (Fintype.card J : Real) := by
  have hn : Not ((Fintype.card J : Real) = 0) :=
    ne_of_gt (Nat.cast_pos.mpr Fintype.card_pos)
  have hSizeReal : (Fintype.card I : Real) = 2 * (Fintype.card J : Real) := by
    exact_mod_cast hSize
  rw [hSizeReal]
  field_simp [hn]
  <;> ring

def hamiltonianBalancedLeftCoordinates (e : I -> Bool) (m : Nat)
    (hCard : (hamiltonianSignCut e).card = m) : Equiv (Fin m) (hamiltonianSignCut e) :=
  Fintype.equivOfCardEq (by simpa only [Fintype.card_fin, Fintype.card_coe] using hCard.symm)

def hamiltonianBalancedRightCoordinates (e : I -> Bool) (m : Nat)
    (hCard : (hamiltonianSignCut e).card = m) (hSize : Fintype.card I = 2 * m) :
    Equiv (Fin m) (Compl.compl (hamiltonianSignCut e) : Finset I) :=
  Fintype.equivOfCardEq (by
    rw [Fintype.card_fin, Fintype.card_coe, Finset.card_compl, hCard, hSize]
    omega)

end PrimeFactorOscillations

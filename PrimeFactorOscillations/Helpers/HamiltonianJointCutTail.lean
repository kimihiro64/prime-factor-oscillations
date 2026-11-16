/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.HamiltonianConditionedComplementaryTail
import PrimeFactorOscillations.Helpers.HamiltonianCutRowTail

/-! # Joint spectral and all-row control on the same actual cut

The covariance and every weighted row use one common sign vector.
The exact union count, with no independence assumption, retains
enough polynomial room for both proved conditioning laws.
-/

set_option autoImplicit false
set_option Elab.async false

open scoped Matrix.Norms.L2Operator

noncomputable section

namespace PrimeFactorOscillations

variable {I : Type*} [Fintype I] [DecidableEq I]

def hamiltonianJointCutBadSigns
    (E P : Matrix I I Real) (alpha A : Real) : Finset (I -> Bool) :=
  Union.union (hamiltonianComplementaryCovarianceBadSigns E alpha (A + 1))
    (hamiltonianCutRowBadSigns P alpha A)

theorem hamiltonian_joint_cut_uniform_polynomial_tail
    (E P : Matrix I I Real) (hE : E.IsHermitian)
    (alpha A : Real) (hAlpha : 0 <= alpha) (hA : 0 < A)
    (hColumn : forall j, hamiltonianColumnEnergy E j <= alpha)
    (hENorm : norm E <= 1)
    (hNonneg : forall i j, 0 <= P i j) (hCap : forall i j, P i j <= alpha)
    (hRows : forall i, Finset.univ.sum (fun j => P i j) = 1)
    (hSize : 2 <= Fintype.card I) :
    ((hamiltonianJointCutBadSigns E P alpha A).card : Real) /
      (Fintype.card (I -> Bool) : Real) <=
        (Fintype.card I : Real) ^ (-(A + 3)) := by
  classical
  let n : Real := Fintype.card I
  let C : Real := Fintype.card (I -> Bool)
  let Bcov := hamiltonianComplementaryCovarianceBadSigns E alpha (A + 1)
  let Brow := hamiltonianCutRowBadSigns P alpha A
  have hn : 2 <= n := by dsimp only [n]; exact_mod_cast hSize
  have hnPos : 0 < n := by linarith only [hn]
  have hCov := hamiltonian_actual_covariance_uniform_polynomial_tail
    E hE alpha (A + 1) hAlpha (by linarith only [hA]) hColumn hENorm hSize
  have hExp : -((A + 1) + 3) = -(A + 4) := by ring
  rw [hExp] at hCov
  change (Bcov.card : Real) / C <= n ^ (-(A + 4)) at hCov
  have hRow := hamiltonian_all_cut_rows_polynomial_tail P alpha A hA hNonneg hCap hRows hSize
  change (Brow.card : Real) / C <= n ^ (-(A + 4)) at hRow
  have hNat : (Union.union Bcov Brow).card <= Bcov.card + Brow.card := by
    apply Finset.card_union_le
  have hCount : ((Union.union Bcov Brow).card : Real) <=
      (Bcov.card : Real) + (Brow.card : Real) := by exact_mod_cast hNat
  have hDiv := div_le_div_of_nonneg_right hCount (show 0 <= C from Nat.cast_nonneg _)
  rw [add_div] at hDiv
  have hMain : ((Union.union Bcov Brow).card : Real) / C <= 2 * n ^ (-(A + 4)) := by
    linarith only [hDiv, hCov, hRow]
  have hPower : n * n ^ (-(A + 4)) = n ^ (-(A + 3)) := by
    calc
      _ = n ^ (1 : Real) * n ^ (-(A + 4)) := by rw [Real.rpow_one]
      _ = n ^ ((1 : Real) + (-(A + 4))) := (Real.rpow_add hnPos _ _).symm
      _ = _ := by congr 1; ring
  exact hMain.trans
    ((mul_le_mul_of_nonneg_right hn (Real.rpow_nonneg hnPos.le _)).trans_eq hPower)

theorem hamiltonian_balanced_joint_cut_polynomial_tail
    (E P : Matrix I I Real) (hE : E.IsHermitian)
    (alpha A : Real) (hAlpha : 0 <= alpha) (hA : 0 < A)
    (hColumn : forall j, hamiltonianColumnEnergy E j <= alpha) (hENorm : norm E <= 1)
    (hNonneg : forall i j, 0 <= P i j) (hCap : forall i j, P i j <= alpha)
    (hRows : forall i, Finset.univ.sum (fun j => P i j) = 1)
    (m : Nat) (hm : 1 <= m) (hSize : Fintype.card I = 2 * m) :
    ((Inter.inter (hamiltonianJointCutBadSigns E P alpha A)
      (hamiltonianBalancedSigns (I := I) m)).card : Real) /
        ((hamiltonianBalancedSigns (I := I) m).card : Real) <=
          (Fintype.card I : Real) ^ (-A) := by
  have hRaw := hamiltonian_joint_cut_uniform_polynomial_tail E P hE alpha A hAlpha hA
    hColumn hENorm hNonneg hCap hRows (by omega)
  exact hamiltonian_balanced_tail_conditioning
    (hamiltonianJointCutBadSigns E P alpha A) A m hm hSize hRaw

theorem hamiltonian_prescribed_joint_cut_polynomial_tail
    (E P : Matrix I I Real) (hE : E.IsHermitian)
    (alpha A : Real) (hAlpha : 0 <= alpha) (hA : 0 < A)
    (hColumn : forall j, hamiltonianColumnEnergy E j <= alpha) (hENorm : norm E <= 1)
    (hNonneg : forall i j, 0 <= P i j) (hCap : forall i j, P i j <= alpha)
    (hRows : forall i, Finset.univ.sum (fun j => P i j) = 1)
    (a b : I) (hab : Not (a = b)) (m : Nat) (hm : 1 <= m)
    (hSize : Fintype.card I = 2 * m) :
    ((Inter.inter (hamiltonianJointCutBadSigns E P alpha A)
      (hamiltonianPrescribedBalancedSigns m a b)).card : Real) /
        ((hamiltonianPrescribedBalancedSigns m a b).card : Real) <=
          (Fintype.card I : Real) ^ (-A) := by
  have hRaw := hamiltonian_joint_cut_uniform_polynomial_tail E P hE alpha A hAlpha hA
    hColumn hENorm hNonneg hCap hRows (by omega)
  exact hamiltonian_prescribed_tail_conditioning
    (hamiltonianJointCutBadSigns E P alpha A) A a b hab m hm hSize hRaw

theorem hamiltonian_good_joint_cut_bounds
    (E P : Matrix I I Real) (alpha A : Real) (e : I -> Bool)
    (hRows : forall i, Finset.univ.sum (fun j => P i j) = 1)
    (hGood : Not (Membership.mem (hamiltonianJointCutBadSigns E P alpha A) e)) :
    And
      (norm (hamiltonianComplementaryCovariance E
          (hamiltonianCutProjection (hamiltonianSignCut e))) <=
        Real.sqrt (2 * (A + 6) * alpha * Real.log (2 * (Fintype.card I : Real))))
      (forall i, abs (Finset.univ.sum (fun j => hamiltonianCrossCutKernel P e i j) - 1) <=
        Real.sqrt (8 * (A + 6) * alpha * Real.log (2 * (Fintype.card I : Real)))) := by
  classical
  have hNoCov : Not (Membership.mem
      (hamiltonianComplementaryCovarianceBadSigns E alpha (A + 1)) e) := by
    intro he
    exact hGood (Finset.mem_union.mpr (Or.inl he))
  have hNoRow : Not (Membership.mem (hamiltonianCutRowBadSigns P alpha A) e) := by
    intro he
    exact hGood (Finset.mem_union.mpr (Or.inr he))
  have hCov : norm (hamiltonianComplementaryCovariance E
      (hamiltonianCutProjection (hamiltonianSignCut e))) <=
        Real.sqrt (2 * ((A + 1) + 5) * alpha * Real.log (2 * (Fintype.card I : Real))) := by
    by_contra hNot
    apply hNoCov
    exact Finset.mem_filter.mpr (And.intro (Finset.mem_univ _) (lt_of_not_ge hNot))
  have hShift : (A + 1) + 5 = A + 6 := by ring
  rw [hShift] at hCov
  exact And.intro hCov (hamiltonian_good_cut_all_row_defects P alpha A e hRows hNoRow)

theorem hamiltonian_good_joint_cut_gap_and_rows
    (E P : Matrix I I Real) (alpha A delta : Real) (e : I -> Bool)
    (hE : E.transpose = E) (hDelta : 0 < delta) (hDelta1 : delta <= 1)
    (hENorm : norm E <= 1 - delta)
    (hRows : forall i, Finset.univ.sum (fun j => P i j) = 1)
    (hThreshold : Real.sqrt (2 * (A + 6) * alpha * Real.log (2 * (Fintype.card I : Real))) <=
      delta / 128)
    (hGood : Not (Membership.mem (hamiltonianJointCutBadSigns E P alpha A) e)) :
    And
      (2 * norm (E.submatrix (fun i : hamiltonianSignCut e => i.val)
        (fun j : (Compl.compl (hamiltonianSignCut e) : Finset I) => j.val)) <= 1 - 3 * delta / 4)
      (forall i, abs (Finset.univ.sum (fun j => hamiltonianCrossCutKernel P e i j) - 1) <=
        Real.sqrt (8 * (A + 6) * alpha * Real.log (2 * (Fintype.card I : Real)))) := by
  have hBounds := hamiltonian_good_joint_cut_bounds E P alpha A e hRows hGood
  exact And.intro
    (hamiltonian_actual_complementary_cut_gap E (hamiltonianSignCut e) delta
      hE hDelta hDelta1 hENorm (hBounds.1.trans hThreshold)) hBounds.2

end PrimeFactorOscillations

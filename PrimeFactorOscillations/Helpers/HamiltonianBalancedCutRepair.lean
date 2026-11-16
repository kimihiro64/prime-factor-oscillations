/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.HamiltonianBalancedCutBudgets

/-! # Quantitative good-cut counts and actual positive scaling at full cap

One positive log-fifth allowance discharges every finite scaling loss.
The exact balanced and prescribed-endpoint laws count the same actual
good cuts; their witnesses repair the original complementary support.
-/

set_option autoImplicit false
set_option Elab.async false

open scoped Matrix.Norms.L2Operator

noncomputable section

namespace PrimeFactorOscillations

theorem hamiltonian_finite_good_event_count
    {Omega : Type*} [Fintype Omega] [DecidableEq Omega]
    (T B : Finset Omega) (x : Real)
    (hTail : ((Inter.inter B T).card : Real) / (T.card : Real) <= x) :
    (1 - x) * (T.card : Real) <= ((SDiff.sdiff T B).card : Real) := by
  classical
  by_cases hZero : T.card = 0
  . have hEmpty : T = EmptyCollection.emptyCollection := Finset.card_eq_zero.mp hZero
    subst T
    simp
  . have hPos : 0 < (T.card : Real) := Nat.cast_pos.mpr (by omega)
    have hScaled := mul_le_mul_of_nonneg_right hTail hPos.le
    have hCancel : (((Inter.inter B T).card : Real) / (T.card : Real)) * (T.card : Real) =
        ((Inter.inter B T).card : Real) := by field_simp [ne_of_gt hPos]
    rw [hCancel] at hScaled
    have hNat := Finset.card_sdiff_add_card_inter T B
    have hCard : ((SDiff.sdiff T B).card : Real) + ((Inter.inter T B).card : Real) =
        (T.card : Real) := by exact_mod_cast hNat
    have hInter : Inter.inter T B = Inter.inter B T := Finset.inter_comm T B
    rw [hInter] at hCard
    nlinarith only [hScaled, hCard]

variable {I J : Type*} [Fintype I] [DecidableEq I] [Nonempty I]
variable [Fintype J] [DecidableEq J] [Nonempty J]

theorem hamiltonian_actual_balanced_good_cut_count
    (P : Matrix I I Real) (q alpha A : Real)
    (hq : (Fintype.card I : Real) * q = 1)
    (hP : P.transpose = P) (hRows : forall i, Finset.univ.sum (fun j => P i j) = 1)
    (hNonneg : forall i j, 0 <= P i j) (hCap : forall i j, P i j <= alpha)
    (hAlpha : 0 <= alpha) (hA : 0 < A) (hNorm : norm (centeredKernel P q) <= 1)
    (m : Nat) (hm : 1 <= m) (hSize : Fintype.card I = 2 * m) :
    (1 - (Fintype.card I : Real) ^ (-A)) *
        ((hamiltonianBalancedSigns (I := I) m).card : Real) <=
      ((SDiff.sdiff (hamiltonianBalancedSigns (I := I) m)
        (hamiltonianJointCutBadSigns (centeredKernel P q) P alpha A)).card : Real) := by
  exact hamiltonian_finite_good_event_count _ _ _
    (hamiltonian_stochastic_balanced_joint_tail P q alpha A hq hP hRows
      hNonneg hCap hAlpha hA hNorm m hm hSize)

theorem hamiltonian_actual_prescribed_good_cut_count
    (P : Matrix I I Real) (q alpha A : Real)
    (hq : (Fintype.card I : Real) * q = 1)
    (hP : P.transpose = P) (hRows : forall i, Finset.univ.sum (fun j => P i j) = 1)
    (hNonneg : forall i j, 0 <= P i j) (hCap : forall i j, P i j <= alpha)
    (hAlpha : 0 <= alpha) (hA : 0 < A) (hNorm : norm (centeredKernel P q) <= 1)
    (a b : I) (hab : Not (a = b)) (m : Nat) (hm : 1 <= m) (hSize : Fintype.card I = 2 * m) :
    (1 - (Fintype.card I : Real) ^ (-A)) *
        ((hamiltonianPrescribedBalancedSigns m a b).card : Real) <=
      ((SDiff.sdiff (hamiltonianPrescribedBalancedSigns m a b)
        (hamiltonianJointCutBadSigns (centeredKernel P q) P alpha A)).card : Real) := by
  exact hamiltonian_finite_good_event_count _ _ _
    (hamiltonian_stochastic_prescribed_joint_tail P q alpha A hq hP hRows
      hNonneg hCap hAlpha hA hNorm a b hab m hm hSize)

theorem hamiltonian_small_cap_actual_cut_scaling
    (P : Matrix I I Real) (alpha A delta : Real) (e : I -> Bool)
    (l : Equiv J (hamiltonianSignCut e))
    (r : Equiv J (Compl.compl (hamiltonianSignCut e) : Finset I))
    (hP : P.transpose = P) (hRows : forall i, Finset.univ.sum (fun j => P i j) = 1)
    (hNonneg : forall i j, 0 <= P i j) (hCap : forall i j, P i j <= alpha)
    (hSize : Fintype.card I = 2 * Fintype.card J)
    (hDelta : 0 < delta) (hDelta1 : delta <= 1)
    (hNorm : norm (centeredKernel P (1 / (Fintype.card I : Real))) <= 1 - delta)
    (hAlpha : 0 <= alpha) (hAlpha1 : alpha <= 1) (hA : 0 < A)
    (hSize2 : 2 <= Fintype.card I)
    (hBudget : alpha * Real.log (2 * (Fintype.card I : Real)) ^ 5 <=
      hamiltonianBalancedCutBudget delta A)
    (hGood : Not (Membership.mem (hamiltonianJointCutBadSigns
      (centeredKernel P (1 / (Fintype.card I : Real))) P alpha A) e)) :
    let T := hamiltonianBalancedCrossBlock P e l r
    let eps := Real.sqrt (8 * (A + 6) * alpha * Real.log (2 * (Fintype.card I : Real)))
    let K := hamiltonianNormalizedScalingCost (delta / 2) *
      eps * Real.log (4 * ((Fintype.card I : Real) * alpha))
    exists z : Sum J J -> Real,
      norm z <= K /\
      (forall i, 0 < 1 + z i) /\
      (forall i j, 0 <= hamiltonianScaledCross T z i j) /\
      (forall i, Finset.univ.sum (fun j => hamiltonianScaledCross T z i j) = 1) /\
      (forall j, Finset.univ.sum (fun i => hamiltonianScaledCross T z i j) = 1) /\
      (forall i j, hamiltonianScaledCross T z i j = 0 <-> T i j = 0) /\
      (forall i j, hamiltonianScaledCross T z i j <= 4 * alpha) /\
      norm (hamiltonianScaledCross T z - T) <= K /\
      norm (centeredKernel (hamiltonianScaledCross T z)
        (1 / (Fintype.card J : Real))) <= 1 - delta / 2 := by
  have hMass := hamiltonian_stochastic_cap_mass P alpha hRows hCap
  have hBudgets := hamiltonian_balanced_cut_all_budgets
    (Fintype.card I : Real) alpha A delta (by exact_mod_cast hSize2)
    hAlpha hAlpha1 hMass hA hDelta hDelta1 hBudget
  exact hamiltonian_actual_good_cut_positive_scaling P alpha A delta e l r
    hP hRows hNonneg hCap hSize hDelta hDelta1 hNorm
    hBudgets.1 hBudgets.2.2.1 hBudgets.2.2.2.1 hBudgets.2.2.2.2 hGood

theorem hamiltonian_small_cap_actual_normalized_gap
    (P : Matrix I I Real) (alpha A delta : Real) (e : I -> Bool)
    (l : Equiv J (hamiltonianSignCut e))
    (r : Equiv J (Compl.compl (hamiltonianSignCut e) : Finset I))
    (hP : P.transpose = P) (hRows : forall i, Finset.univ.sum (fun j => P i j) = 1)
    (hCap : forall i j, P i j <= alpha)
    (hSize : Fintype.card I = 2 * Fintype.card J)
    (hDelta : 0 < delta) (hDelta1 : delta <= 1)
    (hNorm : norm (centeredKernel P (1 / (Fintype.card I : Real))) <= 1 - delta)
    (hAlpha : 0 <= alpha) (hAlpha1 : alpha <= 1) (hA : 0 < A)
    (hSize2 : 2 <= Fintype.card I)
    (hBudget : alpha * Real.log (2 * (Fintype.card I : Real)) ^ 5 <=
      hamiltonianBalancedCutBudget delta A)
    (hGood : Not (Membership.mem (hamiltonianJointCutBadSigns
      (centeredKernel P (1 / (Fintype.card I : Real))) P alpha A) e)) :
    let T := hamiltonianBalancedCrossBlock P e l r
    norm (hamiltonianActualDegreeNormalizedCross T -
      hamiltonianActualDegreeNormalizedMode T (1 / (Fintype.card J : Real))) <=
        1 - delta / 2 := by
  have hMass := hamiltonian_stochastic_cap_mass P alpha hRows hCap
  have hBudgets := hamiltonian_balanced_cut_all_budgets
    (Fintype.card I : Real) alpha A delta (by exact_mod_cast hSize2)
    hAlpha hAlpha1 hMass hA hDelta hDelta1 hBudget
  exact hamiltonian_actual_good_cross_normalized_gap P alpha A delta e l r
    hP hRows hSize hDelta hDelta1 hNorm hBudgets.1 hBudgets.2.1 hGood

end PrimeFactorOscillations

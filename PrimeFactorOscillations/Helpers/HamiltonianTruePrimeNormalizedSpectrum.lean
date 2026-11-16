/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.HamiltonianTruePrimeCrossBlock
import PrimeFactorOscillations.Helpers.HamiltonianWeightedExceptionalModes

/-! # The actual normalized true-prime operator has simple signed Perron modes -/

set_option autoImplicit false
set_option Elab.async false

open scoped Matrix.Norms.L2Operator

noncomputable section

namespace PrimeFactorOscillations.LPF

def hamiltonianTruePrimeNormalizedPhysicalMatrix (m : Nat) :
    Matrix (Fin (2 * m)) (Fin (2 * m)) Real :=
  fun i j => hamiltonianPrimeRealMatrix (2 * m) i j /
    (Real.sqrt (Finset.univ.sum (fun k => hamiltonianPrimeRealMatrix (2 * m) i k)) *
      Real.sqrt (Finset.univ.sum (fun k => hamiltonianPrimeRealMatrix (2 * m) j k)))

theorem hamiltonian_true_prime_physical_normalization_reindex (m : Nat) :
    (hamiltonianTruePrimeNormalizedPhysicalMatrix m).submatrix
      (hamiltonianParityEquiv m) (hamiltonianParityEquiv m) =
        bipartiteLift (hamiltonianActualDegreeNormalizedCross
          (hamiltonianTruePrimeCrossBlock m)) := by
  ext i j
  cases i with
  | inl i =>
    cases j with
    | inl j =>
      change hamiltonianPrimeRealMatrix (2 * m)
        (hamiltonianParityIndex m (Sum.inl i)) (hamiltonianParityIndex m (Sum.inl j)) /
        _ = 0
      rw [hamiltonian_prime_real_bipartite _ _ _ (by simp [hamiltonianParityIndex])]
      exact zero_div _
    | inr j =>
      change hamiltonianPrimeRealMatrix (2 * m)
        (hamiltonianParityIndex m (Sum.inl i)) (hamiltonianParityIndex m (Sum.inr j)) /
        (Real.sqrt (Finset.univ.sum (fun k => hamiltonianPrimeRealMatrix (2 * m)
          (hamiltonianParityIndex m (Sum.inl i)) k)) *
          Real.sqrt (Finset.univ.sum (fun k => hamiltonianPrimeRealMatrix (2 * m)
            (hamiltonianParityIndex m (Sum.inr j)) k))) =
        hamiltonianTruePrimeCrossBlock m i j /
          (Real.sqrt (hamiltonianCrossRowDegrees (hamiltonianTruePrimeCrossBlock m) i) *
            Real.sqrt (hamiltonianCrossColumnDegrees (hamiltonianTruePrimeCrossBlock m) j))
      rw [<- hamiltonian_true_prime_cross_row, <- hamiltonian_true_prime_cross_column]
      rfl
  | inr i =>
    cases j with
    | inl j =>
      change hamiltonianPrimeRealMatrix (2 * m)
        (hamiltonianParityIndex m (Sum.inr i)) (hamiltonianParityIndex m (Sum.inl j)) /
        (Real.sqrt (Finset.univ.sum (fun k => hamiltonianPrimeRealMatrix (2 * m)
          (hamiltonianParityIndex m (Sum.inr i)) k)) *
          Real.sqrt (Finset.univ.sum (fun k => hamiltonianPrimeRealMatrix (2 * m)
            (hamiltonianParityIndex m (Sum.inl j)) k))) =
        hamiltonianTruePrimeCrossBlock m j i /
          (Real.sqrt (hamiltonianCrossRowDegrees (hamiltonianTruePrimeCrossBlock m) j) *
            Real.sqrt (hamiltonianCrossColumnDegrees (hamiltonianTruePrimeCrossBlock m) i))
      rw [<- hamiltonian_true_prime_cross_column, <- hamiltonian_true_prime_cross_row]
      rw [hamiltonian_prime_real_symmetric]
      change hamiltonianTruePrimeCrossBlock m j i /
        (Real.sqrt (hamiltonianCrossColumnDegrees (hamiltonianTruePrimeCrossBlock m) i) *
          Real.sqrt (hamiltonianCrossRowDegrees (hamiltonianTruePrimeCrossBlock m) j)) =
        hamiltonianTruePrimeCrossBlock m j i /
        (Real.sqrt (hamiltonianCrossRowDegrees (hamiltonianTruePrimeCrossBlock m) j) *
          Real.sqrt (hamiltonianCrossColumnDegrees (hamiltonianTruePrimeCrossBlock m) i))
      rw [mul_comm
        (Real.sqrt (hamiltonianCrossColumnDegrees (hamiltonianTruePrimeCrossBlock m) i))
        (Real.sqrt (hamiltonianCrossRowDegrees (hamiltonianTruePrimeCrossBlock m) j))]
    | inr j =>
      change hamiltonianPrimeRealMatrix (2 * m)
        (hamiltonianParityIndex m (Sum.inr i)) (hamiltonianParityIndex m (Sum.inr j)) /
        _ = 0
      rw [hamiltonian_prime_real_bipartite _ _ _ (by simp [hamiltonianParityIndex])]
      exact zero_div _


theorem hamiltonian_true_prime_normalized_spectral_uniform
    (eta : Real) (hEta : 0 < eta) :
    exists M0 : Nat, 256 <= M0 /\
      forall (m : Nat) [NeZero m], M0 <= m ->
        (forall i : Fin m,
          0 < hamiltonianCrossRowDegrees (hamiltonianTruePrimeCrossBlock m) i) /\
        (forall j : Fin m,
          0 < hamiltonianCrossColumnDegrees (hamiltonianTruePrimeCrossBlock m) j) /\
        HamiltonianNormalizedSpectralPacket (hamiltonianTruePrimeCrossBlock m)
          ((1 / 2 : Real) + eta) := by
  let eps := min (eta / 34) (1 / 128)
  have he0 : 0 < eps := lt_min (div_pos hEta (by norm_num)) (by norm_num)
  have heEta : eps <= eta / 34 := min_le_left _ _
  have heSmall : eps <= 1 / 128 := min_le_right _ _
  have heHalf : eps <= 1 / 2 := by linarith only [heSmall]
  choose A hA hOperator using hamiltonian_true_prime_cross_operator_uniform eps he0
  choose B hB hDegree using hamiltonian_true_prime_cross_degree_uniform eps he0
  let M0 := max 256 (max A B)
  refine Exists.intro M0 (And.intro (le_max_left _ _) ?_)
  intro m instM hm
  have hmA : A <= m := (le_max_left A B).trans ((le_max_right 256 _).trans hm)
  have hmB : B <= m := (le_max_right A B).trans ((le_max_right 256 _).trans hm)
  have hD := hDegree m hmB
  have hO := hOperator m hmA
  have hrPos (i : Fin m) :
      0 < hamiltonianCrossRowDegrees (hamiltonianTruePrimeCrossBlock m) i := by
    have h := (abs_le.mp (hD.1 i)).1
    change 0 < Finset.univ.sum (fun j => hamiltonianTruePrimeCrossBlock m i j)
    linarith only [h, heSmall]
  have hcPos (j : Fin m) :
      0 < hamiltonianCrossColumnDegrees (hamiltonianTruePrimeCrossBlock m) j := by
    have h := (abs_le.mp (hD.2 j)).1
    change 0 < Finset.univ.sum (fun i => hamiltonianTruePrimeCrossBlock m i j)
    linarith only [h, heSmall]
  have hmNe : Not ((m : Real) = 0) := ne_of_gt (Nat.cast_pos.mpr (NeZero.pos m))
  have hq : (Fintype.card (Fin m) : Real) * (1 / (m : Real)) = 1 := by
    rw [Fintype.card_fin]
    field_simp [hmNe]
  have hRho0 : 0 <= (1 / 2 : Real) + eps := by linarith only [he0]
  have hRho1 : (1 / 2 : Real) + eps <= 1 := by linarith only [heSmall]
  have hMargin : (1 / 2 : Real) + eps + 16 * eps < 1 := by
    linarith only [heSmall]
  have hPacket := hamiltonian_actual_normalized_spectral_packet_from_raw
    (hamiltonianTruePrimeCrossBlock m) (1 / (m : Real)) eps ((1 / 2 : Real) + eps)
    hq he0.le heHalf hRho0 hRho1 hMargin hD.1 hD.2 hO
  refine And.intro hrPos (And.intro hcPos ?_)
  constructor
  . exact hPacket.plus_simple
  . exact hPacket.minus_simple
  . intro k hOne hMinus
    have h := hPacket.nontrivial k hOne hMinus
    have hUpper : (1 / 2 : Real) + eps + 16 * eps <= (1 / 2 : Real) + eta := by
      linarith only [heEta, hEta]
    exact h.trans hUpper

theorem hamiltonian_true_prime_normalized_signed_modes
    (m : Nat) [NeZero m]
    (hRow : forall i : Fin m,
      0 < hamiltonianCrossRowDegrees (hamiltonianTruePrimeCrossBlock m) i)
    (hCol : forall j : Fin m,
      0 < hamiltonianCrossColumnDegrees (hamiltonianTruePrimeCrossBlock m) j) :
    let T := hamiltonianTruePrimeCrossBlock m
    (forall i,
      (bipartiteLift (hamiltonianActualDegreeNormalizedCross T)).mulVec
        (hamiltonianWeightedPlus (hamiltonianRowRoot T) (hamiltonianColumnRoot T)) i =
          hamiltonianWeightedPlus (hamiltonianRowRoot T) (hamiltonianColumnRoot T) i) /\
    (forall i,
      (bipartiteLift (hamiltonianActualDegreeNormalizedCross T)).mulVec
        (hamiltonianWeightedMinus (hamiltonianRowRoot T) (hamiltonianColumnRoot T)) i =
          -(hamiltonianWeightedMinus (hamiltonianRowRoot T) (hamiltonianColumnRoot T) i)) /\
    (exists i,
      Not (hamiltonianWeightedPlus (hamiltonianRowRoot T) (hamiltonianColumnRoot T) i = 0)) /\
    (exists i,
      Not (hamiltonianWeightedMinus (hamiltonianRowRoot T) (hamiltonianColumnRoot T) i = 0)) := by
  intro T
  have hN := hamiltonian_degree_roots_equal_norms T hRow hCol
  have hR := ne_of_gt (hamiltonian_total_degree_positive T hRow)
  have hLeft := hamiltonian_actual_normalized_perron_left T hRow hCol
  have hRight := hamiltonian_actual_normalized_perron_right T hRow hCol
  have hActions :
      (forall i, (bipartiteLift (hamiltonianActualDegreeNormalizedCross T)).mulVec
        (hamiltonianWeightedPlus (hamiltonianRowRoot T) (hamiltonianColumnRoot T)) i =
          hamiltonianWeightedPlus (hamiltonianRowRoot T) (hamiltonianColumnRoot T) i) /\
      (forall i, (bipartiteLift (hamiltonianActualDegreeNormalizedCross T)).mulVec
        (hamiltonianWeightedMinus (hamiltonianRowRoot T) (hamiltonianColumnRoot T)) i =
          -(hamiltonianWeightedMinus (hamiltonianRowRoot T) (hamiltonianColumnRoot T) i)) := by
    constructor
    . intro i
      cases i with
      | inl i =>
        rw [hamiltonian_bipartite_mulVec_left]
        exact hLeft i
      | inr j =>
        rw [hamiltonian_bipartite_mulVec_right]
        exact hRight j
    . intro i
      cases i with
      | inl i =>
        rw [hamiltonian_bipartite_mulVec_left]
        simpa only [hamiltonianWeightedMinus, Sum.elim_inl, Sum.elim_inr,
          mul_neg, Finset.sum_neg_distrib] using congrArg Neg.neg (hLeft i)
      | inr j =>
        rw [hamiltonian_bipartite_mulVec_right]
        simpa only [hamiltonianWeightedMinus, Sum.elim_inl, Sum.elim_inr,
          neg_neg] using hRight j
  let i0 : Fin m := Fin.mk 0 (NeZero.pos m)
  have hNonzero : Not (hamiltonianRowRoot T i0 = 0) :=
    ne_of_gt (Real.sqrt_pos.mpr (hRow i0))
  exact And.intro hActions.1 (And.intro hActions.2
    (And.intro (Exists.intro (Sum.inl i0) hNonzero)
      (Exists.intro (Sum.inl i0) hNonzero)))

end PrimeFactorOscillations.LPF

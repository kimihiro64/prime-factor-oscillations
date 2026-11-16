/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.HamiltonianFactorNormalization

/-!
# Full-support stochastic mixtures with a vanishing perturbation

A sparse regular factor can retain every original edge in a stochastic
reference by a positive vanishing mixture with one full-support kernel.
-/

set_option autoImplicit false
set_option Elab.async false

open scoped Matrix.Norms.L2Operator

variable {Iota : Type*} [Fintype Iota] [DecidableEq Iota]

def hamiltonianSupportMixture (delta : Real) (A R : Matrix Iota Iota Real) :
    Matrix Iota Iota Real :=
  fun i j => (1 - delta) * A i j + delta * R i j

theorem hamiltonian_symmetric_stochastic_norm
    (M : Matrix Iota Iota Real)
    (hNonneg : forall i j, 0 <= M i j)
    (hSym : forall i j, M i j = M j i)
    (hRow : forall i, Finset.univ.sum (fun j => M i j) = 1) :
    norm M <= 1 := by
  apply PrimeFactorOscillations.hamiltonian_symmetric_row_budget M hSym 1 (by norm_num)
  intro i
  calc
    Finset.univ.sum (fun j => norm (M i j)) =
        Finset.univ.sum (fun j => M i j) :=
      Finset.sum_congr rfl (fun j _ => Real.norm_of_nonneg (hNonneg i j))
    _ <= 1 := (hRow i).le

theorem hamiltonian_full_support_mixture
    (U A R : Matrix Iota Iota Real) (delta : Real)
    (hDelta : 0 < delta) (hDeltaOne : delta <= 1)
    (hANonneg : forall i j, 0 <= A i j)
    (hRNonneg : forall i j, 0 <= R i j)
    (hASym : forall i j, A i j = A j i)
    (hRSym : forall i j, R i j = R j i)
    (hARow : forall i, Finset.univ.sum (fun j => A i j) = 1)
    (hRRow : forall i, Finset.univ.sum (fun j => R i j) = 1)
    (hASupport : forall i j, U i j = 0 -> A i j = 0)
    (hRSupport : forall i j, R i j = 0 <-> U i j = 0) :
    And (forall i j, 0 <= hamiltonianSupportMixture delta A R i j)
      (And (forall i j, hamiltonianSupportMixture delta A R i j =
          hamiltonianSupportMixture delta A R j i)
      (And (forall i, Finset.univ.sum (fun j => hamiltonianSupportMixture delta A R i j) = 1)
      (And (forall j, Finset.univ.sum (fun i => hamiltonianSupportMixture delta A R i j) = 1)
      (And (forall i j, hamiltonianSupportMixture delta A R i j = 0 <-> U i j = 0)
        (norm (hamiltonianSupportMixture delta A R - A) <= 2 * delta))))) := by
  have hLeft : 0 <= 1 - delta := sub_nonneg.mpr hDeltaOne
  have hNonneg : forall i j, 0 <= hamiltonianSupportMixture delta A R i j := by
    intro i j
    exact add_nonneg (mul_nonneg hLeft (hANonneg i j))
      (mul_nonneg (le_of_lt hDelta) (hRNonneg i j))
  have hSym : forall i j, hamiltonianSupportMixture delta A R i j =
      hamiltonianSupportMixture delta A R j i := by
    intro i j
    unfold hamiltonianSupportMixture
    rw [hASym i j, hRSym i j]
  have hRow : forall i, Finset.univ.sum (fun j => hamiltonianSupportMixture delta A R i j) = 1 := by
    intro i
    change Finset.univ.sum (fun j => (1 - delta) * A i j + delta * R i j) = 1
    rw [Finset.sum_add_distrib, <- Finset.mul_sum, <- Finset.mul_sum, hARow i, hRRow i]
    ring
  have hCol : forall j, Finset.univ.sum (fun i => hamiltonianSupportMixture delta A R i j) = 1 := by
    intro j
    calc
      _ = Finset.univ.sum (fun i => hamiltonianSupportMixture delta A R j i) :=
        Finset.sum_congr rfl (fun i _ => hSym i j)
      _ = 1 := hRow j
  have hSupport : forall i j,
      hamiltonianSupportMixture delta A R i j = 0 <-> U i j = 0 := by
    intro i j
    constructor
    . intro hp
      by_contra hu
      have hR : Not (R i j = 0) := fun h => hu ((hRSupport i j).mp h)
      have hRPos : 0 < R i j := by
        rcases lt_or_eq_of_le (hRNonneg i j) with h | h
        . exact h
        . exact False.elim (hR h.symm)
      have hPos : 0 < (1 - delta) * A i j + delta * R i j :=
        add_pos_of_nonneg_of_pos (mul_nonneg hLeft (hANonneg i j)) (mul_pos hDelta hRPos)
      exact (ne_of_gt hPos) hp
    . intro hu
      change (1 - delta) * A i j + delta * R i j = 0
      rw [hASupport i j hu, (hRSupport i j).mpr hu]
      ring
  have hA := hamiltonian_symmetric_stochastic_norm A hANonneg hASym hARow
  have hR := hamiltonian_symmetric_stochastic_norm R hRNonneg hRSym hRRow
  have hNorm : norm (hamiltonianSupportMixture delta A R - A) <= 2 * delta := by
    have hDiff : hamiltonianSupportMixture delta A R - A = SMul.smul delta (R - A) := by
      ext i j
      change (1 - delta) * A i j + delta * R i j - A i j = delta * (R i j - A i j)
      ring
    rw [hDiff, hamiltonian_matrix_real_smul_norm, Real.norm_of_nonneg (le_of_lt hDelta)]
    calc
      _ <= delta * (norm R + norm A) :=
        mul_le_mul_of_nonneg_left (norm_sub_le R A) (le_of_lt hDelta)
      _ <= delta * (1 + 1) := mul_le_mul_of_nonneg_left (add_le_add hR hA) (le_of_lt hDelta)
      _ = 2 * delta := by ring
  exact And.intro hNonneg (And.intro hSym (And.intro hRow (And.intro hCol (And.intro hSupport hNorm))))

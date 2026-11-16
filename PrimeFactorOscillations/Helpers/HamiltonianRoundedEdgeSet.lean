/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.HamiltonianRegularFactorOperator
import PrimeFactorOscillations.Helpers.HamiltonianRoundingReadout

/-! # Actual finite simple edge sets and neighborhood counts of the rounding -/

set_option autoImplicit false
set_option Elab.async false

open scoped Matrix.Norms.L2Operator

noncomputable section

namespace PrimeFactorOscillations

variable {Iota : Type*} [Fintype Iota] [DecidableEq Iota]

def hamiltonianRoundedEdges (H : Matrix Iota Iota Real) : Finset (Prod Iota Iota) := by
  classical
  exact Finset.univ.filter (fun e => H e.1 e.2 = 1)

theorem hamiltonian_rounded_edges_indicator
    (H : Matrix Iota Iota Real) (hBinary : forall i j, H i j = 0 \/ H i j = 1)
    (i j : Iota) :
    (if Membership.mem (hamiltonianRoundedEdges H) (i, j) then (1 : Real) else 0) =
      H i j := by
  classical
  cases hBinary i j with
  | inl h => simp [hamiltonianRoundedEdges, h]
  | inr h => simp [hamiltonianRoundedEdges, h]

theorem hamiltonian_rounded_edges_adjacency
    (H : Matrix Iota Iota Real) (hBinary : forall i j, H i j = 0 \/ H i j = 1) :
    hamiltonianFactorAdjacency (hamiltonianRoundedEdges H) = bipartiteLift H := by
  ext i j
  rcases i with i | i <;> rcases j with j | j
  . rfl
  . exact hamiltonian_rounded_edges_indicator H hBinary i j
  . exact hamiltonian_rounded_edges_indicator H hBinary j i
  . rfl

theorem hamiltonian_rounded_edges_degrees
    (H : Matrix Iota Iota Real) (d : Nat)
    (hBinary : forall i j, H i j = 0 \/ H i j = 1)
    (hRows : forall i, Finset.univ.sum (fun j => H i j) = (d : Real))
    (hCols : forall j, Finset.univ.sum (fun i => H i j) = (d : Real)) :
    (forall i, ((hamiltonianRoundedEdges H).filter (fun e => e.1 = i)).card = d) /\
      (forall j, ((hamiltonianRoundedEdges H).filter (fun e => e.2 = j)).card = d) := by
  classical
  constructor
  . intro i
    have h := hamiltonian_factor_left_row_count (hamiltonianRoundedEdges H) i
    simp only [hamiltonian_rounded_edges_indicator H hBinary] at h
    rw [hRows i] at h
    exact_mod_cast h.symm
  . intro j
    have h := hamiltonian_factor_right_row_count (hamiltonianRoundedEdges H) j
    simp only [hamiltonian_rounded_edges_indicator H hBinary] at h
    rw [hCols j] at h
    exact_mod_cast h.symm

theorem hamiltonian_factor_subset_neighbor_count
    (E : Finset (Prod Iota Iota)) (S : Finset (Sum Iota Iota)) (i : Sum Iota Iota) :
    S.sum (fun j => hamiltonianFactorAdjacency E i j) =
      ((S.filter (fun j => hamiltonianFactorAdjacency E i j = 1)).card : Real) := by
  classical
  have hIndicator (j : Sum Iota Iota) :
      (if hamiltonianFactorAdjacency E i j = 1 then (1 : Real) else 0) =
        hamiltonianFactorAdjacency E i j := by
    rcases i with i | i <;> rcases j with j | j <;>
      simp only [hamiltonianFactorAdjacency] <;>
      split_ifs <;> norm_num at *
  rw [Finset.card_eq_sum_ones, Nat.cast_sum]
  simp only [Nat.cast_one, Finset.sum_filter, hIndicator]

theorem hamiltonian_supported_simple_rounding [Nonempty Iota]
    (P : Matrix Iota Iota Real) (S1 S2 : Finset (Sum Iota Iota))
    (delta alpha : Real) (d : Nat) (hd : 1 <= d)
    (hd0 : 0 < delta) (hd1 : delta < 1) (ha : 0 <= alpha)
    (hP : forall i j, 0 <= P i j) (hCap : forall i j, P i j <= alpha)
    (hPRows : forall i, Finset.univ.sum (fun j => P i j) = 1)
    (hPCols : forall j, Finset.univ.sum (fun i => P i j) = 1)
    (hGap : norm (centeredKernel P (1 / (Fintype.card Iota : Real))) <= 1 - delta)
    (hSmall : ((d : Real) * alpha) * Real.log (4 * (Fintype.card Iota : Real)) ^ 2 <=
      hamiltonianForbiddenRepairSmall delta) :
    let err := 16 * Real.sqrt (Real.log (4 * (Fintype.card Iota : Real)) / (d : Real)) +
      hamiltonianRoundingDriftCost Iota delta alpha * (d : Real)
    exists E : Finset (Prod Iota Iota),
      (forall e, Membership.mem E e -> 0 < P e.1 e.2) /\
      (forall i, (E.filter (fun e => e.1 = i)).card = d) /\
      (forall j, (E.filter (fun e => e.2 = j)).card = d) /\
      norm (SMul.smul (1 / (d : Real)) (hamiltonianFactorAdjacency E) -
        bipartiteLift P) <= err /\
      (forall i, abs ((1 / (d : Real)) *
        ((S1.filter (fun j => hamiltonianFactorAdjacency E i j = 1)).card : Real) -
          S1.sum (fun j => bipartiteLift P i j)) <= err) /\
      (forall i, abs ((1 / (d : Real)) *
        ((S2.filter (fun j => hamiltonianFactorAdjacency E i j = 1)).card : Real) -
          S2.sum (fun j => bipartiteLift P i j)) <= err) := by
  classical
  intro err
  cases hamiltonian_supported_rounding_spectral_and_observables P S1 S2
      delta alpha d hd hd0 hd1 ha hP hCap hPRows hPCols hGap hSmall with
  | intro H hH =>
    let E := hamiltonianRoundedEdges H
    have hAdj : hamiltonianFactorAdjacency E = bipartiteLift H :=
      hamiltonian_rounded_edges_adjacency H hH.1
    have hDeg := hamiltonian_rounded_edges_degrees H d hH.1 hH.2.1 hH.2.2.1
    have hSupport (e : Prod Iota Iota) (he : Membership.mem E e) : 0 < P e.1 e.2 := by
      have hOne : H e.1 e.2 = 1 := (Finset.mem_filter.mp he).2
      have hNe : Not (P e.1 e.2 = 0) := by
        intro hZero
        have hz := hH.2.2.2.1 e.1 e.2 hZero
        linarith only [hOne, hz]
      exact lt_of_le_of_ne (hP e.1 e.2) (Ne.symm hNe)
    have hFirst (i : Sum Iota Iota) :
        abs ((1 / (d : Real)) *
          ((S1.filter (fun j => hamiltonianFactorAdjacency E i j = 1)).card : Real) -
            S1.sum (fun j => bipartiteLift P i j)) <= err := by
      rw [<- hamiltonian_factor_subset_neighbor_count, hAdj]
      exact hH.2.2.2.2.2.1 i
    have hSecond (i : Sum Iota Iota) :
        abs ((1 / (d : Real)) *
          ((S2.filter (fun j => hamiltonianFactorAdjacency E i j = 1)).card : Real) -
            S2.sum (fun j => bipartiteLift P i j)) <= err := by
      rw [<- hamiltonian_factor_subset_neighbor_count, hAdj]
      exact hH.2.2.2.2.2.2 i
    refine Exists.intro E (And.intro hSupport (And.intro hDeg.1
      (And.intro hDeg.2 (And.intro ?_ (And.intro hFirst hSecond)))))
    rw [hAdj]
    exact hH.2.2.2.2.1


theorem hamiltonian_rounding_dimension_only_constants
    (delta : Real) (hd0 : 0 < delta) (hd1 : delta < 1) :
    0 < hamiltonianForbiddenRepairSmall delta /\
      0 < max 16 (hamiltonianForbiddenObservableCost delta) := by
  exact And.intro (hamiltonian_forbidden_repair_constants_positive delta hd0 hd1).1
    (lt_of_lt_of_le (by norm_num : (0 : Real) < 16) (le_max_left _ _))

theorem hamiltonian_rounding_advertised_budget
    (delta alpha d : Real) (ha : 0 <= alpha) (hd : 1 <= d) [Nonempty Iota] :
    16 * Real.sqrt (Real.log (4 * (Fintype.card Iota : Real)) / d) +
        hamiltonianRoundingDriftCost Iota delta alpha * d <=
      max 16 (hamiltonianForbiddenObservableCost delta) *
        (d * alpha * Real.log (4 * (Fintype.card Iota : Real)) +
          Real.sqrt (Real.log (4 * (Fintype.card Iota : Real)) / d) +
          Real.log (4 * (Fintype.card Iota : Real)) / d) := by
  let L := Real.log (4 * (Fintype.card Iota : Real))
  let C := max 16 (hamiltonianForbiddenObservableCost delta)
  have hm : (1 : Real) <= (Fintype.card Iota : Real) := by
    exact_mod_cast (show 1 <= Fintype.card Iota from Fintype.card_pos)
  have hL : 0 <= L := (by norm_num : (0 : Real) <= 1).trans
    (hamiltonian_rounding_log_geometry _ hm).1
  have hd0 : 0 <= d := by linarith only [hd]
  have hC0 : 0 <= C := (by norm_num : (0 : Real) <= 16).trans (le_max_left _ _)
  have hX : 0 <= d * alpha * L := mul_nonneg (mul_nonneg hd0 ha) hL
  have hY : 0 <= Real.sqrt (L / d) := Real.sqrt_nonneg _
  have hZ : 0 <= C * (L / d) := mul_nonneg hC0 (div_nonneg hL hd0)
  have hDrift := mul_le_mul_of_nonneg_right
    (le_max_right 16 (hamiltonianForbiddenObservableCost delta)) hX
  have hMoment := mul_le_mul_of_nonneg_right
    (le_max_left 16 (hamiltonianForbiddenObservableCost delta)) hY
  calc
    _ = 16 * Real.sqrt (L / d) +
        hamiltonianForbiddenObservableCost delta * (d * alpha * L) := by
      dsimp [L, hamiltonianRoundingDriftCost]
      ring
    _ <= C * Real.sqrt (L / d) + C * (d * alpha * L) :=
      add_le_add hMoment hDrift
    _ <= C * (d * alpha * L + Real.sqrt (L / d) + L / d) := by
      nlinarith only [hZ]

theorem hamiltonian_simple_regular_spectral_rounding [Nonempty Iota]
    (P : Matrix Iota Iota Real) (S1 S2 : Finset (Sum Iota Iota))
    (delta alpha : Real) (d : Nat) (hd : 1 <= d)
    (hd0 : 0 < delta) (hd1 : delta < 1) (ha : 0 <= alpha)
    (hP : forall i j, 0 <= P i j) (hCap : forall i j, P i j <= alpha)
    (hPRows : forall i, Finset.univ.sum (fun j => P i j) = 1)
    (hPCols : forall j, Finset.univ.sum (fun i => P i j) = 1)
    (hGap : norm (centeredKernel P (1 / (Fintype.card Iota : Real))) <= 1 - delta)
    (hSmall : ((d : Real) * alpha) * Real.log (4 * (Fintype.card Iota : Real)) ^ 2 <=
      hamiltonianForbiddenRepairSmall delta) :
    let err := max 16 (hamiltonianForbiddenObservableCost delta) *
      ((d : Real) * alpha * Real.log (4 * (Fintype.card Iota : Real)) +
        Real.sqrt (Real.log (4 * (Fintype.card Iota : Real)) / (d : Real)) +
        Real.log (4 * (Fintype.card Iota : Real)) / (d : Real))
    exists E : Finset (Prod Iota Iota),
      (forall e, Membership.mem E e -> 0 < P e.1 e.2) /\
      (forall i, (E.filter (fun e => e.1 = i)).card = d) /\
      (forall j, (E.filter (fun e => e.2 = j)).card = d) /\
      norm (SMul.smul (1 / (d : Real)) (hamiltonianFactorAdjacency E) -
        bipartiteLift P) <= err /\
      (forall i, abs ((1 / (d : Real)) *
        ((S1.filter (fun j => hamiltonianFactorAdjacency E i j = 1)).card : Real) -
          S1.sum (fun j => bipartiteLift P i j)) <= err) /\
      (forall i, abs ((1 / (d : Real)) *
        ((S2.filter (fun j => hamiltonianFactorAdjacency E i j = 1)).card : Real) -
          S2.sum (fun j => bipartiteLift P i j)) <= err) := by
  intro err
  have hdReal : (1 : Real) <= (d : Real) := by exact_mod_cast hd
  have hBudget := hamiltonian_rounding_advertised_budget
    (Iota := Iota) delta alpha (d : Real) ha hdReal
  cases hamiltonian_supported_simple_rounding P S1 S2 delta alpha d hd
      hd0 hd1 ha hP hCap hPRows hPCols hGap hSmall with
  | intro E hE =>
    exact Exists.intro E (And.intro hE.1 (And.intro hE.2.1 (And.intro hE.2.2.1
      (And.intro (hE.2.2.2.1.trans hBudget)
        (And.intro (fun i => (hE.2.2.2.2.1 i).trans hBudget)
          (fun i => (hE.2.2.2.2.2 i).trans hBudget))))))

end PrimeFactorOscillations

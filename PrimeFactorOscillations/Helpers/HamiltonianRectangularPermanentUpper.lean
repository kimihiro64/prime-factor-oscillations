/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.HamiltonianBipartiteSupports
import PrimeFactorOscillations.Helpers.HamiltonianRowCapAllOrders

/-! # The row-cap bound on the actual independent-support minors

The maintained permanent uses a permutation of the row index.
Transposing the finite reindexing makes its row-sum hypothesis the
original column-sum hypothesis. Both deleted supports remain
independent. Empty and one-coordinate complements are included,
and the rank shift N-r is kept exact.
-/

set_option autoImplicit false
set_option Elab.async false

noncomputable section

namespace PrimeFactorOscillations

theorem hamiltonian_finite_permanent_row_cap_upper
    {J : Type*} [Fintype J] [DecidableEq J]
    (M : Matrix J J Real) (a X : Real)
    (ha : 1 <= a) (hX1 : 1 <= X) (hX : (Fintype.card J : Real) <= X)
    (hNonneg : forall i j, 0 <= M i j)
    (hCol : forall j, Finset.univ.sum (fun i => M i j) <= 1)
    (hCap : forall i j, M i j <= a / X) :
    finitePermutationSum M <=
      Real.exp (-(Fintype.card J : Real) + 16 * a * Real.log (2 * X)) := by
  let e : Equiv (Fin (Fintype.card J)) J := (Fintype.equivFin J).symm
  have hRow (i : Fin (Fintype.card J)) :
      Finset.univ.sum (fun j => (M.submatrix e e).transpose i j) <= 1 := by
    change Finset.univ.sum (fun j => M (e j) (e i)) <= 1
    rw [Equiv.sum_comp e (fun j => M j (e i))]
    exact hCol (e i)
  have h := hamiltonian_row_cap_permanent_all_orders (Fintype.card J)
    (M.submatrix e e).transpose a X ha hX1 hX
    (fun i j => hNonneg (e j) (e i)) hRow (fun i j => hCap (e j) (e i))
  change finitePermutationSum (M.submatrix e e) <= _ at h
  rw [finitePermutationSum_reindex e M] at h
  exact h

variable {Iota : Type*} [Fintype Iota] [DecidableEq Iota]

theorem hamiltonian_rectangular_minor_permanent_upper
    (T : Matrix Iota Iota Real) (S U : Finset Iota) (a X : Real)
    (ha : 1 <= a) (hX1 : 1 <= X) (hX : (Fintype.card Iota : Real) <= X)
    (hNonneg : forall i j, 0 <= T i j)
    (hCol : forall j, Finset.univ.sum (fun i => T i j) <= 1)
    (hCap : forall i j, T i j <= a / X) :
    rectangularMinorPermanent T S U <=
      Real.exp (-(U.card : Real) + 16 * a * Real.log (2 * X)) := by
  unfold rectangularMinorPermanent
  by_cases hCard : S.card = U.card
  case pos =>
    rw [dite_eq_left hCard]
    let e : Equiv U S := equalCardMinorEquiv S U hCard
    let M : Matrix U U Real := T.submatrix
      (fun i => (e i).val) (Subtype.val : U -> Iota)
    change finitePermutationSum M <= _
    have hColumn (j : U) : Finset.univ.sum (fun i => M i j) <= 1 := by
      change Finset.univ.sum (fun i : U => T (e i).val j.val) <= 1
      calc
        _ = Finset.univ.sum (fun i : S => T i.val j.val) :=
          Equiv.sum_comp e (fun i : S => T i.val j.val)
        _ = S.sum (fun i => T i j.val) := by
          simpa using! (Finset.sum_coe_sort S (fun i : Iota => T i j.val))
        _ <= Finset.univ.sum (fun i => T i j.val) :=
          Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ S)
            (fun i hi hNot => hNonneg i j.val)
        _ <= 1 := hCol j.val
    have hSize : (Fintype.card U : Real) <= X := by
      have hU : (U.card : Real) <= (Fintype.card Iota : Real) := by
        exact_mod_cast Finset.card_le_univ U
      simpa only [Fintype.card_coe] using le_trans hU hX
    have h := hamiltonian_finite_permanent_row_cap_upper M a X ha hX1 hSize
      (fun i j => hNonneg (e i).val j.val) hColumn
      (fun i j => hCap (e i).val j.val)
    simpa only [Fintype.card_coe] using h
  case neg =>
    rw [dite_eq_right hCard]
    exact le_of_lt (Real.exp_pos _)

variable [Nonempty Iota]

theorem stochastic_complementary_permanent_upper
    (T : Matrix Iota Iota Real) (S U : Finset Iota) (q a : Real)
    (hq : (Fintype.card Iota : Real) * q = 1) (ha : 1 <= a)
    (hNonneg : forall i j, 0 <= T i j)
    (hCol : forall j, Finset.univ.sum (fun i => T i j) = 1)
    (hCap : forall i j, T i j <= a * q) :
    rectangularMinorPermanent T (Compl.compl S) (Compl.compl U) <=
      Real.exp ((U.card : Real) - (Fintype.card Iota : Real) +
        16 * a * Real.log (2 * (Fintype.card Iota : Real))) := by
  let N : Real := Fintype.card Iota
  have hN : 0 < N := Nat.cast_pos.mpr Fintype.card_pos
  have hN1 : 1 <= N := by
    change (1 : Real) <= (Fintype.card Iota : Real)
    exact_mod_cast (Nat.succ_le_of_lt (show 0 < Fintype.card Iota from Fintype.card_pos))
  have hqValue : q = 1 / N := by
    calc
      _ = (N * q) / N := by field_simp [ne_of_gt hN] <;> ring
      _ = _ := by rw [hq]
  have hEntry (i j : Iota) : T i j <= a / N := by
    calc
      _ <= a * q := hCap i j
      _ = _ := by rw [hqValue]; ring
  have h := hamiltonian_rectangular_minor_permanent_upper T
    (Compl.compl S) (Compl.compl U) a N ha hN1 (le_refl _)
    hNonneg (fun j => le_of_eq (hCol j)) hEntry
  have hComplement : ((Compl.compl U).card : Real) = N - (U.card : Real) := by
    rw [Finset.card_compl, Nat.cast_sub (Finset.card_le_univ U)]
  calc
    _ <= Real.exp (-((Compl.compl U).card : Real) + 16 * a * Real.log (2 * N)) := h
    _ = _ := by
      rw [hComplement]
      congr 1
      ring

end PrimeFactorOscillations

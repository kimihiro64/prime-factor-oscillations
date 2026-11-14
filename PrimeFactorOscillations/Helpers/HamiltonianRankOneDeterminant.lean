/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Tactic.Ring

/-! # Exact rank-one determinant cancellation

Adding multiples of one common row vector to any collection of rows changes
the determinant affinely. The proof keeps all selected rows and uses exact
row-operation cancellation. No inverse or nonsingularity assumption is used.
This is the pole-cancellation input for signed occupancy moments.
-/

set_option autoImplicit false
set_option Elab.async false

noncomputable section

namespace PrimeFactorOscillations

variable {Iota R : Type*} [DecidableEq Iota] [Fintype Iota] [CommRing R]

def selectedRankOneRows (A : Matrix Iota Iota R) (S : Finset Iota)
    (c v : Iota -> R) : Matrix Iota Iota R :=
  fun i j => A i j + if Membership.mem S i then c i * v j else 0

omit [Fintype Iota] in
theorem selectedRankOneRows_empty (A : Matrix Iota Iota R) (c v : Iota -> R) :
    selectedRankOneRows A ({} : Finset Iota) c v = A := by
  ext i j
  change A i j + (if Membership.mem ({} : Finset Iota) i
    then c i * v j else 0) = A i j
  simp

theorem selectedRankOneRows_univ (A : Matrix Iota Iota R) (c v : Iota -> R) :
    selectedRankOneRows A Finset.univ c v = (fun i j => A i j + c i * v j) := by
  ext i j
  change A i j + (if Membership.mem (Finset.univ : Finset Iota) i
    then c i * v j else 0) = A i j + c i * v j
  simp

omit [Fintype Iota] in
theorem selectedRankOneRows_insert (A : Matrix Iota Iota R) (S : Finset Iota)
    (c v : Iota -> R) (a : Iota) (ha : Not (Membership.mem S a)) :
    selectedRankOneRows A (insert a S) c v =
      Matrix.updateRow (selectedRankOneRows A S c v) a
        (selectedRankOneRows A S c v a + HSMul.hSMul (c a) v) := by
  ext i j
  by_cases h : i = a
  case pos =>
    subst i
    rw [Matrix.updateRow_self]
    change A a j + (if Membership.mem (insert a S) a then c a * v j else 0) =
      (A a j + if Membership.mem S a then c a * v j else 0) + c a * v j
    simp [ha]
  case neg =>
    rw [Matrix.updateRow_ne h]
    change A i j + (if Membership.mem (insert a S) i then c i * v j else 0) =
      A i j + (if Membership.mem S i then c i * v j else 0)
    simp [h]

theorem selectedRankOneRows_replaced_det (A : Matrix Iota Iota R)
    (S : Finset Iota) (c v : Iota -> R) (i : Iota)
    (hi : Not (Membership.mem S i)) :
    Matrix.det (Matrix.updateRow (selectedRankOneRows A S c v) i v) =
      Matrix.det (Matrix.updateRow A i v) := by
  classical
  revert hi
  induction S using Finset.induction_on with
  | empty =>
      intro _
      rw [selectedRankOneRows_empty]
  | @insert a S ha ih =>
      intro hi
      have hia : Not (i = a) := by
        intro h
        apply hi
        rw [h]
        exact Finset.mem_insert_self a S
      have hai : Not (a = i) := fun h => hia h.symm
      have hiS : Not (Membership.mem S i) :=
        fun h => hi (Finset.mem_insert_of_mem h)
      let M := selectedRankOneRows A S c v
      rw [selectedRankOneRows_insert A S c v a ha]
      have hComm :
          Matrix.updateRow (Matrix.updateRow M a (M a + HSMul.hSMul (c a) v)) i v =
            Matrix.updateRow (Matrix.updateRow M i v) a
              ((Matrix.updateRow M i v) a +
                HSMul.hSMul (c a) ((Matrix.updateRow M i v) i)) := by
        ext j k
        by_cases hja : j = a
        case pos =>
          subst j
          simp only [Matrix.updateRow_self, Matrix.updateRow_ne hai]
        case neg =>
          by_cases hji : j = i
          case pos =>
            subst j
            simp only [Matrix.updateRow_self, Matrix.updateRow_ne hia]
          case neg =>
            simp only [Matrix.updateRow_ne hja, Matrix.updateRow_ne hji]
      rw [hComm, Matrix.det_updateRow_add_smul_self (Matrix.updateRow M i v) hai]
      exact ih hiS

theorem det_selectedRankOneRows (A : Matrix Iota Iota R) (S : Finset Iota)
    (c v : Iota -> R) :
    Matrix.det (selectedRankOneRows A S c v) =
      Matrix.det A + Finset.sum S
        (fun i => c i * Matrix.det (Matrix.updateRow A i v)) := by
  classical
  induction S using Finset.induction_on with
  | empty => rw [selectedRankOneRows_empty, Finset.sum_empty, add_zero]
  | @insert a S ha ih =>
      rw [selectedRankOneRows_insert A S c v a ha, Matrix.det_updateRow_add,
        Matrix.updateRow_eq_self, Matrix.det_updateRow_smul,
        selectedRankOneRows_replaced_det A S c v a ha, ih, Finset.sum_insert ha]
      ring

theorem det_rankOne_affine (A : Matrix Iota Iota R) (u v : Iota -> R) (t : R) :
    Matrix.det (fun i j => A i j + t * u i * v j) =
      Matrix.det A + t * Finset.sum Finset.univ
        (fun i => u i * Matrix.det (Matrix.updateRow A i v)) := by
  classical
  calc
    _ = Matrix.det A + Finset.sum Finset.univ
        (fun i => (t * u i) * Matrix.det (Matrix.updateRow A i v)) := by
      have h := det_selectedRankOneRows A Finset.univ (fun i => t * u i) v
      rw [selectedRankOneRows_univ] at h
      exact h
    _ = _ := by
      rw [Finset.mul_sum]
      congr 1
      apply Finset.sum_congr rfl
      intro i hi
      ring

end PrimeFactorOscillations

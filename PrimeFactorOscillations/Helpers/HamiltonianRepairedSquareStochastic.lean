/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.HamiltonianRepairedSquareKernel

/-! # Stochastic equations and entry bounds for the actual repaired kernel -/

set_option autoImplicit false
set_option Elab.async false

noncomputable section

namespace PrimeFactorOscillations

variable {Iota : Type*} [Fintype Iota] [DecidableEq Iota]

theorem hamiltonian_repaired_square_stochastic (T : Matrix Iota Iota Real)
    (S U : Finset Iota) (hCard : S.card = U.card)
    (z : forall _i : (Compl.compl (S.disjSum U) : Finset (Sum Iota Iota)), Real)
    (hPhysical : forall r : (Compl.compl (S.disjSum U) : Finset (Sum Iota Iota)),
      (1 + z r) * (hamiltonianRetainedKernel T S U).mulVec (1 + z) r = 1) :
    (forall i, Finset.univ.sum (fun j => hamiltonianRepairedSquareKernel T S U hCard z i j) = 1) /\
    (forall j, Finset.univ.sum (fun i => hamiltonianRepairedSquareKernel T S U hCard z i j) = 1) := by
  let R : Finset (Sum Iota Iota) := Compl.compl (S.disjSum U)
  let e := hamiltonianRepairedSquareEquiv S U hCard
  let V := Matrix.diagonal (1 + z) * hamiltonianRetainedKernel T S U * Matrix.diagonal (1 + z)
  have hRow (r : R) : Finset.univ.sum (fun j => V r j) = 1 := by
    calc
      _ = (1 + z r) * (hamiltonianRetainedKernel T S U).mulVec (1 + z) r := by
        simp only [V, Matrix.mul_diagonal, Matrix.diagonal_mul, Matrix.mulVec, dotProduct,
          Pi.add_apply, Pi.one_apply, Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro j hj
        ring
      _ = 1 := hPhysical r
  have hReindex := hamiltonian_repaired_scaled_bipartite_reindex T S U hCard z
  have hFull (i : Sum (Compl.compl U : Finset Iota) (Compl.compl U : Finset Iota)) :
      Finset.univ.sum (fun j =>
        bipartiteLift (hamiltonianRepairedSquareKernel T S U hCard z) i j) = 1 := by
    calc
      _ = Finset.univ.sum (fun j => V (e i) (e j)) := by
        apply Finset.sum_congr rfl
        intro j hj
        exact congrArg (fun M => M i j) hReindex.symm
      _ = Finset.univ.sum (fun r : R => V (e i) r) :=
        Fintype.sum_equiv e _ _ (fun _ => rfl)
      _ = 1 := hRow (e i)
  constructor
  next =>
    intro i
    simpa [bipartiteLift, Matrix.fromBlocks, Fintype.sum_sum_type] using hFull (Sum.inl i)
  next =>
    intro j
    simpa [bipartiteLift, Matrix.fromBlocks, Fintype.sum_sum_type, Matrix.transpose_apply] using hFull (Sum.inr j)

theorem hamiltonian_repaired_square_nonnegative (T : Matrix Iota Iota Real)
    (S U : Finset Iota) (hCard : S.card = U.card)
    (z : forall _i : (Compl.compl (S.disjSum U) : Finset (Sum Iota Iota)), Real)
    (hT : forall i j, 0 <= T i j) (hZ : forall r, 0 <= 1 + z r) :
    forall i j, 0 <= hamiltonianRepairedSquareKernel T S U hCard z i j := by
  intro i j
  exact mul_nonneg (mul_nonneg (hZ _) (hT _ _)) (hZ _)

theorem hamiltonian_repaired_square_entry_bound (T : Matrix Iota Iota Real)
    (S U : Finset Iota) (hCard : S.card = U.card)
    (z : forall _i : (Compl.compl (S.disjSum U) : Finset (Sum Iota Iota)), Real)
    (a q qNew : Real) (ha : 0 <= a) (hq : 0 <= q) (hShift : q <= qNew)
    (hT : forall i j, 0 <= T i j) (hUpper : forall i j, T i j <= a * q)
    (hZ : forall r, abs (z r) <= 1 / 50) :
    forall i j, hamiltonianRepairedSquareKernel T S U hCard z i j <= 2 * a * qNew := by
  intro i j
  let e := hamiltonianRepairedSquareEquiv S U hCard
  let left := 1 + z (e (Sum.inl i))
  let right := 1 + z (e (Sum.inr j))
  have hLeft : 0 <= left /\ left <= 51 / 50 := by
    have h := abs_le.mp (hZ (e (Sum.inl i)))
    dsimp only [left]
    constructor <;> linarith
  have hRight : 0 <= right /\ right <= 51 / 50 := by
    have h := abs_le.mp (hZ (e (Sum.inr j)))
    dsimp only [right]
    constructor <;> linarith
  have hAq : 0 <= a * q := mul_nonneg ha hq
  have hFirst : left * T (hamiltonianComplementRowEquiv S U hCard i).val j.val <= (51 / 50) * (a * q) :=
    mul_le_mul hLeft.2 (hUpper _ _) (hT _ _) (by norm_num)
  have hSecond := mul_le_mul hFirst hRight.2 hRight.1
    (mul_nonneg (by norm_num : (0 : Real) <= 51 / 50) hAq)
  change left * T (hamiltonianComplementRowEquiv S U hCard i).val j.val * right <= _
  have hCompare : (51 / 50 : Real) * (a * q) * (51 / 50) <= 2 * a * q := by
    nlinarith [hAq]
  exact hSecond.trans (hCompare.trans (mul_le_mul_of_nonneg_left hShift (mul_nonneg (by norm_num) ha)))

end PrimeFactorOscillations

/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.HamiltonianTraceSupportCompensation

/-! # Linear scaling support errors using stochastic mass

Zero extension retains the complete ambient signed trace. The removed
row/column correction is bounded by stochastic mass, keeping both
disjoint support domains and every removed-by-removed term.
-/

set_option autoImplicit false
set_option Elab.async false

noncomputable section

namespace PrimeFactorOscillations

variable {Iota : Type*} [Fintype Iota] [DecidableEq Iota]

def hamiltonianZeroExtend (D : Finset Iota)
    (z : forall _i : (Compl.compl D : Finset Iota), Real) : Iota -> Real :=
  fun i => if h : Membership.mem (Compl.compl D : Finset Iota) i
    then z (Subtype.mk i h) else 0

theorem hamiltonianZeroExtend_retained (D : Finset Iota)
    (z : forall _i : (Compl.compl D : Finset Iota), Real)
    (i : (Compl.compl D : Finset Iota)) :
    hamiltonianZeroExtend D z i.val = z i := by
  simp only [hamiltonianZeroExtend, dite_eq_left i.property]

theorem hamiltonianZeroExtend_removed (D : Finset Iota)
    (z : forall _i : (Compl.compl D : Finset Iota), Real) (d : D) :
    hamiltonianZeroExtend D z d.val = 0 := by
  have hNot : Not (Membership.mem (Compl.compl D : Finset Iota) d.val) :=
    fun h => (Finset.mem_compl.mp h) d.property
  simp only [hamiltonianZeroExtend, dite_eq_right hNot]

theorem hamiltonianZeroExtend_abs_bound (D : Finset Iota)
    (z : forall _i : (Compl.compl D : Finset Iota), Real)
    (b : Real) (hb : 0 <= b) (hZ : forall i, abs (z i) <= b) (i : Iota) :
    abs (hamiltonianZeroExtend D z i) <= b := by
  by_cases h : Membership.mem (Compl.compl D : Finset Iota) i
  case pos =>
    simp only [hamiltonianZeroExtend, dite_eq_left h]
    exact hZ (Subtype.mk i h)
  case neg =>
    simp only [hamiltonianZeroExtend, dite_eq_right h, abs_zero]
    exact hb

theorem hamiltonianZeroExtend_weighted_sum (D : Finset Iota)
    (z : forall _i : (Compl.compl D : Finset Iota), Real) (w : Iota -> Real) :
    Finset.sum Finset.univ (fun i => w i * hamiltonianZeroExtend D z i) =
      Finset.sum Finset.univ (fun i : (Compl.compl D : Finset Iota) => w i.val * z i) := by
  rw [hamiltonian_sum_support_partition
    (fun i => w i * hamiltonianZeroExtend D z i) D]
  simp only [hamiltonianZeroExtend_removed, hamiltonianZeroExtend_retained,
    mul_zero, Finset.sum_const_zero, zero_add]

theorem hamiltonianZeroExtend_linear_restriction
    (P : Matrix Iota Iota Real) (D : Finset Iota)
    (z : forall _i : (Compl.compl D : Finset Iota), Real) :
    (Matrix.diagonal (hamiltonianZeroExtend D z) * P +
        P * Matrix.diagonal (hamiltonianZeroExtend D z)).submatrix
      (fun i : (Compl.compl D : Finset Iota) => i.val)
      (fun i : (Compl.compl D : Finset Iota) => i.val) =
      Matrix.diagonal z * P.submatrix
          (fun i : (Compl.compl D : Finset Iota) => i.val)
          (fun i : (Compl.compl D : Finset Iota) => i.val) +
        P.submatrix (fun i : (Compl.compl D : Finset Iota) => i.val)
          (fun i : (Compl.compl D : Finset Iota) => i.val) * Matrix.diagonal z := by
  apply Matrix.ext
  intro i j
  simp only [Matrix.submatrix_apply, Matrix.add_apply,
    Matrix.diagonal_mul, Matrix.mul_diagonal, hamiltonianZeroExtend_retained]

theorem hamiltonian_linear_scaling_removed_trace_bound
    (A P : Matrix Iota Iota Real) (D : Finset Iota)
    (z : forall _i : (Compl.compl D : Finset Iota), Real) (c b : Real)
    (hc : 0 <= c) (hb : 0 <= b)
    (hA : forall i j, abs (A i j) <= c)
    (hNonneg : forall i j, 0 <= P i j)
    (hRow : forall i, Finset.sum Finset.univ (fun j => P i j) = 1)
    (hCol : forall j, Finset.sum Finset.univ (fun i => P i j) = 1)
    (hZ : forall i, abs (z i) <= b) :
    let R : Finset Iota := Compl.compl D
    let x := hamiltonianZeroExtend D z
    let X := Matrix.diagonal x * P + P * Matrix.diagonal x
    let AR := A.submatrix (fun i : R => i.val) (fun i : R => i.val)
    let PR := P.submatrix (fun i : R => i.val) (fun i : R => i.val)
    abs (Matrix.trace (A * X) -
      Matrix.trace (AR * (Matrix.diagonal z * PR + PR * Matrix.diagonal z))) <=
        2 * (D.card : Real) * c * b := by
  let R : Finset Iota := Compl.compl D
  let x := hamiltonianZeroExtend D z
  let X := Matrix.diagonal x * P + P * Matrix.diagonal x
  let AR := A.submatrix (fun i : R => i.val) (fun i : R => i.val)
  let PR := P.submatrix (fun i : R => i.val) (fun i : R => i.val)
  let u := Finset.sum Finset.univ (fun d : D =>
    Finset.sum Finset.univ (fun j : Iota => A d.val j * X j d.val))
  let v := Finset.sum Finset.univ (fun i : R =>
    Finset.sum Finset.univ (fun d : D => A i.val d.val * X d.val i.val))
  have hXBound (i : Iota) : abs (x i) <= b :=
    hamiltonianZeroExtend_abs_bound D z b hb hZ i
  have hXCol (d : D) (j : Iota) : X j d.val = x j * P j d.val := by
    simp only [X, Matrix.add_apply, Matrix.diagonal_mul, Matrix.mul_diagonal,
      x, hamiltonianZeroExtend_removed, mul_zero, add_zero]
  have hXRow (d : D) (i : R) : X d.val i.val = P d.val i.val * z i := by
    simp only [X, Matrix.add_apply, Matrix.diagonal_mul, Matrix.mul_diagonal,
      x, hamiltonianZeroExtend_removed, hamiltonianZeroExtend_retained, zero_mul, zero_add]
  have hFirstPair (d : D) (j : Iota) :
      abs (A d.val j * X j d.val) <= (c * b) * P j d.val := by
    rw [hXCol]
    simp only [abs_mul, abs_of_nonneg (hNonneg j d.val)]
    calc
      _ = (abs (A d.val j) * abs (x j)) * P j d.val := by ring
      _ <= _ := mul_le_mul_of_nonneg_right
        (mul_le_mul (hA d.val j) (hXBound j) (abs_nonneg _) hc) (hNonneg j d.val)
  have hFirst (d : D) : abs (Finset.sum Finset.univ
      (fun j : Iota => A d.val j * X j d.val)) <= c * b := by
    calc
      _ <= Finset.sum Finset.univ (fun j : Iota => abs (A d.val j * X j d.val)) :=
        Finset.abs_sum_le_sum_abs _ _
      _ <= Finset.sum Finset.univ (fun j : Iota => (c * b) * P j d.val) :=
        Finset.sum_le_sum (fun j _ => hFirstPair d j)
      _ = (c * b) * Finset.sum Finset.univ (fun j => P j d.val) := by rw [Finset.mul_sum]
      _ = _ := by rw [hCol d.val, mul_one]
  have hU : abs u <= (D.card : Real) * (c * b) := by
    calc
      _ <= Finset.sum Finset.univ (fun d : D =>
          abs (Finset.sum Finset.univ (fun j : Iota => A d.val j * X j d.val))) :=
        Finset.abs_sum_le_sum_abs _ _
      _ <= Finset.sum Finset.univ (fun _ : D => c * b) :=
        Finset.sum_le_sum (fun d _ => hFirst d)
      _ = _ := by simp only [Finset.sum_const, Finset.card_univ, Fintype.card_coe, nsmul_eq_mul]
  have hSecondPair (d : D) (i : R) :
      abs (A i.val d.val * X d.val i.val) <= (c * b) * P d.val i.val := by
    rw [hXRow]
    simp only [abs_mul, abs_of_nonneg (hNonneg d.val i.val)]
    calc
      _ = (abs (A i.val d.val) * abs (z i)) * P d.val i.val := by ring
      _ <= _ := mul_le_mul_of_nonneg_right
        (mul_le_mul (hA i.val d.val) (hZ i) (abs_nonneg _) hc) (hNonneg d.val i.val)
  have hRetainedRow (d : D) : Finset.sum Finset.univ (fun i : R => P d.val i.val) <= 1 :=
    le_trans (hamiltonian_retained_sum_le (fun i => P d.val i) D (fun i => hNonneg d.val i))
      (le_of_eq (hRow d.val))
  have hSecond (d : D) : abs (Finset.sum Finset.univ
      (fun i : R => A i.val d.val * X d.val i.val)) <= c * b := by
    calc
      _ <= Finset.sum Finset.univ (fun i : R => abs (A i.val d.val * X d.val i.val)) :=
        Finset.abs_sum_le_sum_abs _ _
      _ <= Finset.sum Finset.univ (fun i : R => (c * b) * P d.val i.val) :=
        Finset.sum_le_sum (fun i _ => hSecondPair d i)
      _ = (c * b) * Finset.sum Finset.univ (fun i : R => P d.val i.val) := by rw [Finset.mul_sum]
      _ <= (c * b) * 1 := mul_le_mul_of_nonneg_left (hRetainedRow d) (mul_nonneg hc hb)
      _ = _ := mul_one _
  have hV : abs v <= (D.card : Real) * (c * b) := by
    have hSwap : v = Finset.sum Finset.univ (fun d : D =>
        Finset.sum Finset.univ (fun i : R => A i.val d.val * X d.val i.val)) := by
      dsimp only [v]
      rw [Finset.sum_comm]
    rw [hSwap]
    calc
      _ <= Finset.sum Finset.univ (fun d : D =>
          abs (Finset.sum Finset.univ (fun i : R => A i.val d.val * X d.val i.val))) :=
        Finset.abs_sum_le_sum_abs _ _
      _ <= Finset.sum Finset.univ (fun _ : D => c * b) :=
        Finset.sum_le_sum (fun d _ => hSecond d)
      _ = _ := by simp only [Finset.sum_const, Finset.card_univ, Fintype.card_coe, nsmul_eq_mul]
  have hPartition := hamiltonian_trace_support_partition A X D
  rw [hamiltonianZeroExtend_linear_restriction P D z] at hPartition
  change Matrix.trace (A * X) =
    Matrix.trace (AR * (Matrix.diagonal z * PR + PR * Matrix.diagonal z)) + u + v at hPartition
  have hDiff : Matrix.trace (A * X) -
      Matrix.trace (AR * (Matrix.diagonal z * PR + PR * Matrix.diagonal z)) = u + v := by
    linarith only [hPartition]
  change abs (Matrix.trace (A * X) -
    Matrix.trace (AR * (Matrix.diagonal z * PR + PR * Matrix.diagonal z))) <= _
  rw [hDiff]
  have hTriangle := abs_add_le u v
  nlinarith only [hTriangle, hU, hV]

end PrimeFactorOscillations

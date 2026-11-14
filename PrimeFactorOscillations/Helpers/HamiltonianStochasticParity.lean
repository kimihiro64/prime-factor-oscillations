/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import Mathlib.Tactic.Abel
import PrimeFactorOscillations.Helpers.HamiltonianBipartiteDeterminant

/-! # The exact stochastic parity factor

Balance and a normalized constant projection give the factor (1 - t) in the
Gram determinant. The normalization is explicit over a general commutative
ring, so its polynomial lift does not require an analytic or spectral premise.
-/

set_option autoImplicit false
set_option Elab.async false

noncomputable section

namespace PrimeFactorOscillations

variable {Iota R : Type*} [DecidableEq Iota] [Fintype Iota] [CommRing R]

def averagingKernel (q : R) : Matrix Iota Iota R := fun _ _ => q

def centeredKernel (T : Matrix Iota Iota R) (q : R) : Matrix Iota Iota R :=
  T - averagingKernel q

omit [DecidableEq Iota] [Fintype Iota] [CommRing R] in
theorem averagingKernel_transpose (q : R) :
    (averagingKernel (Iota := Iota) q).transpose = averagingKernel q := rfl

omit [DecidableEq Iota] in
theorem averagingKernel_mul_of_columnSum (T : Matrix Iota Iota R) (q : R)
    (hcol : forall j, Finset.sum Finset.univ (fun i => T i j) = 1) :
    averagingKernel q * T = averagingKernel q := by
  ext i j
  simp only [Matrix.mul_apply, averagingKernel]
  rw [<- Finset.mul_sum, hcol j, mul_one]

omit [DecidableEq Iota] in
theorem mul_averagingKernel_of_rowSum (T : Matrix Iota Iota R) (q : R)
    (hrow : forall i, Finset.sum Finset.univ (fun j => T i j) = 1) :
    T * averagingKernel q = averagingKernel q := by
  ext i j
  simp only [Matrix.mul_apply, averagingKernel]
  rw [<- Finset.sum_mul, hrow i, one_mul]

omit [DecidableEq Iota] in
theorem averagingKernel_mul_self (q : R) (hq : (Fintype.card Iota : R) * q = 1) :
    averagingKernel (Iota := Iota) q * averagingKernel q = averagingKernel q := by
  apply averagingKernel_mul_of_columnSum
  intro j
  simpa only [averagingKernel, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    using hq

theorem det_one_sub_averagingKernel (q : R)
    (hq : (Fintype.card Iota : R) * q = 1) (t : R) :
    Matrix.det ((1 : Matrix Iota Iota R) - HSMul.hSMul t (averagingKernel q)) =
      1 - t := by
  classical
  have hOuter :
      (1 : Matrix Iota Iota R) - HSMul.hSMul t (averagingKernel q) =
        1 + Matrix.replicateCol PUnit.{1} (fun _ : Iota => -t * q) *
          Matrix.replicateRow PUnit.{1} (fun _ : Iota => (1 : R)) := by
    ext i j
    simp [Matrix.mul_apply, averagingKernel, Matrix.replicateCol,
      Matrix.replicateRow, smul_eq_mul, sub_eq_add_neg]
  rw [hOuter, @Matrix.det_one_add_replicateCol_mul_replicateRow
    Iota R _ _ _ PUnit.{1} _
    (fun _ : Iota => -t * q) (fun _ : Iota => (1 : R))]
  change 1 + Finset.sum Finset.univ (fun _ : Iota => (1 : R) * (-t * q)) = 1 - t
  simp only [one_mul, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  calc
    _ = 1 - t * ((Fintype.card Iota : R) * q) := by ring
    _ = 1 - t := by rw [hq, mul_one]

omit [DecidableEq Iota] in
theorem centeredKernel_gram_eq_sub (T : Matrix Iota Iota R) (q : R)
    (hq : (Fintype.card Iota : R) * q = 1)
    (hcol : forall j, Finset.sum Finset.univ (fun i => T i j) = 1) :
    (centeredKernel T q).transpose * centeredKernel T q =
      T.transpose * T - averagingKernel q := by
  have hTrans : forall i, Finset.sum Finset.univ (fun j => T.transpose i j) = 1 :=
    hcol
  unfold centeredKernel
  rw [Matrix.transpose_sub, averagingKernel_transpose, Matrix.sub_mul,
    Matrix.mul_sub, Matrix.mul_sub]
  rw [mul_averagingKernel_of_rowSum T.transpose q hTrans,
    averagingKernel_mul_of_columnSum T q hcol, averagingKernel_mul_self q hq]
  simp

omit [DecidableEq Iota] in
theorem averagingKernel_mul_centeredTranspose (T : Matrix Iota Iota R) (q : R)
    (hq : (Fintype.card Iota : R) * q = 1)
    (hrow : forall i, Finset.sum Finset.univ (fun j => T i j) = 1) :
    averagingKernel q * (centeredKernel T q).transpose = 0 := by
  have hTrans : forall j, Finset.sum Finset.univ (fun i => T.transpose i j) = 1 :=
    hrow
  unfold centeredKernel
  rw [Matrix.transpose_sub, averagingKernel_transpose, Matrix.mul_sub,
    averagingKernel_mul_of_columnSum T.transpose q hTrans,
    averagingKernel_mul_self q hq, sub_self]

theorem stochasticGram_parityFactor (T : Matrix Iota Iota R) (q : R)
    (hq : (Fintype.card Iota : R) * q = 1)
    (hrow : forall i, Finset.sum Finset.univ (fun j => T i j) = 1)
    (hcol : forall j, Finset.sum Finset.univ (fun i => T i j) = 1) (t : R) :
    Matrix.det (1 - HSMul.hSMul t (T.transpose * T)) =
      (1 - t) * Matrix.det (1 - HSMul.hSMul t
        ((centeredKernel T q).transpose * centeredKernel T q)) := by
  let Q := (centeredKernel T q).transpose * centeredKernel T q
  have hOrth : averagingKernel q * Q = 0 := by
    dsimp [Q]
    rw [<- Matrix.mul_assoc, averagingKernel_mul_centeredTranspose T q hq hrow,
      Matrix.zero_mul]
  have hGram : T.transpose * T = averagingKernel q + Q := by
    dsimp [Q]
    rw [centeredKernel_gram_eq_sub T q hq hcol, add_comm, sub_add_cancel]
  have hFactor :
      ((1 : Matrix Iota Iota R) - HSMul.hSMul t (averagingKernel q)) *
          ((1 : Matrix Iota Iota R) - HSMul.hSMul t Q) =
        (1 : Matrix Iota Iota R) - HSMul.hSMul t (averagingKernel q + Q) := by
    rw [Matrix.sub_mul, Matrix.one_mul, Matrix.mul_sub, Matrix.mul_one]
    simp only [Matrix.smul_mul, Matrix.mul_smul, hOrth, smul_zero, sub_zero]
    rw [smul_add]
    abel
  rw [hGram, <- hFactor, Matrix.det_mul, det_one_sub_averagingKernel q hq t]

end PrimeFactorOscillations

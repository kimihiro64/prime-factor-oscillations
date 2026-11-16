/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.HamiltonianTraceMomentMass

/-! # Actual Hermitian operator-norm readout from an even trace moment -/

set_option autoImplicit false
set_option Elab.async false

open scoped Matrix.Norms.L2Operator

noncomputable section

namespace PrimeFactorOscillations

variable {Iota : Type*} [Fintype Iota] [DecidableEq Iota]

theorem hamiltonian_hermitian_norm_le_eigen_norm
    (A : Matrix Iota Iota Real) (hA : A.IsHermitian) :
    norm A <= norm hA.eigenvalues := by
  let U := realGaussianEigenMatrix A hA
  let D := Matrix.diagonal hA.eigenvalues
  have hU : norm U <= 1 :=
    hamiltonian_real_orthogonal_norm_le_one U (realGaussianEigenMatrix_orthogonal A hA)
  have hTranspose : norm U.transpose = norm U := by
    change norm U.conjTranspose = norm U
    exact Matrix.l2_opNorm_conjTranspose U
  have hSpec : A = U * D * U.transpose :=
    realGaussianEigenMatrix_decomposition A hA
  calc
    _ = norm (U * D * U.transpose) := congrArg norm hSpec
    _ <= norm (U * D) * norm U.transpose := Matrix.l2_opNorm_mul _ _
    _ <= (norm U * norm D) * norm U.transpose :=
      mul_le_mul_of_nonneg_right (Matrix.l2_opNorm_mul _ _) (norm_nonneg _)
    _ <= (1 * norm D) * 1 :=
      mul_le_mul
        (mul_le_mul_of_nonneg_right hU (norm_nonneg _))
        (hTranspose.le.trans hU) (norm_nonneg _) (by positivity)
    _ = _ := by rw [one_mul, mul_one, Matrix.l2_opNorm_diagonal]

theorem hamiltonian_hermitian_norm_le_even_trace_root
    (A : Matrix Iota Iota Real) (hA : A.IsHermitian)
    (p : Nat) (hp : 2 <= p) (hEven : Even p) :
    norm A <= (Matrix.trace (A ^ p)) ^ (1 / (p : Real)) := by
  have hpPos : (0 : Real) < p := Nat.cast_pos.mpr (lt_of_lt_of_le (by decide : 0 < 2) hp)
  have hpNe : Not ((p : Real) = 0) := ne_of_gt hpPos
  have hq : 0 <= 1 / (p : Real) := (one_div_pos.mpr hpPos).le
  have hG : 0 <= Matrix.trace (A ^ p) :=
    hamiltonian_even_trace_power_nonnegative A hA p hEven
  have hRoot (i : Iota) :
      abs (hA.eigenvalues i) <= (Matrix.trace (A ^ p)) ^ (1 / (p : Real)) := by
    have hSingle : abs (hA.eigenvalues i) ^ p <=
        Finset.univ.sum (fun j => abs (hA.eigenvalues j) ^ p) :=
      Finset.single_le_sum (f := fun j : Iota => abs (hA.eigenvalues j) ^ p)
        (fun j _ => pow_nonneg (abs_nonneg (hA.eigenvalues j)) p) (Finset.mem_univ i)
    rw [<- hamiltonian_even_trace_power_absolute A hA p hEven] at hSingle
    have h := Real.rpow_le_rpow (pow_nonneg (abs_nonneg _) p) hSingle hq
    have hExp : (p : Real) * (1 / (p : Real)) = 1 := by field_simp
    rw [<- Real.rpow_natCast, <- Real.rpow_mul (abs_nonneg _),
      hExp, Real.rpow_one] at h
    exact h
  have hPi : norm hA.eigenvalues <= (Matrix.trace (A ^ p)) ^ (1 / (p : Real)) :=
    (pi_norm_le_iff_of_nonneg (Real.rpow_nonneg hG _)).mpr
      (fun i => by simpa only [Real.norm_eq_abs] using hRoot i)
  exact (hamiltonian_hermitian_norm_le_eigen_norm A hA).trans hPi

theorem hamiltonian_hermitian_norm_square_le_even_trace
    (A : Matrix Iota Iota Real) (hA : A.IsHermitian)
    (p : Nat) (hp : 2 <= p) (hEven : Even p) :
    norm A ^ 2 <= (Matrix.trace (A ^ p)) ^ (2 / (p : Real)) := by
  have h := hamiltonian_hermitian_norm_le_even_trace_root A hA p hp hEven
  have hG : 0 <= Matrix.trace (A ^ p) :=
    hamiltonian_even_trace_power_nonnegative A hA p hEven
  have hRoot : 0 <= (Matrix.trace (A ^ p)) ^ (1 / (p : Real)) :=
    Real.rpow_nonneg hG _
  have hSquare : norm A ^ 2 <= ((Matrix.trace (A ^ p)) ^ (1 / (p : Real))) ^ 2 := by
    nlinarith only [h, hRoot, norm_nonneg A]
  have hExp : (1 / (p : Real)) * 2 = 2 / (p : Real) := by ring
  have hId : ((Matrix.trace (A ^ p)) ^ (1 / (p : Real))) ^ 2 =
      (Matrix.trace (A ^ p)) ^ (2 / (p : Real)) := by
    rw [<- Real.rpow_two, <- Real.rpow_mul hG, hExp]
  exact hSquare.trans_eq hId

end PrimeFactorOscillations

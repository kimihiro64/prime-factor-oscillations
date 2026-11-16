/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import Mathlib.Tactic.NoncommRing
import PrimeFactorOscillations.Helpers.HamiltonianMixedTraceReadout
import PrimeFactorOscillations.Helpers.HamiltonianTraceMeanValueScalar

/-! # Signed matrix trace mean value

Both complete noncommutative trace polynomials use the same
independent eigenbasis overlap squares, including every pure term.
The scalar pairing therefore gives the moment inequality at every
order without separate estimates for its compensation terms.
-/

set_option autoImplicit false
set_option Elab.async false

noncomputable section

namespace PrimeFactorOscillations

variable {I : Type*} [Fintype I] [DecidableEq I]

theorem hamiltonian_trace_increment_power_expansion
    (X Y : Matrix I I Real) (q : Nat) :
    Matrix.trace ((X - Y) * (X ^ (q + 1) - Y ^ (q + 1))) =
      Matrix.trace (X ^ (q + 2)) + Matrix.trace (Y ^ (q + 2)) -
        Matrix.trace (X ^ (q + 1) * Y) -
        Matrix.trace (X * Y ^ (q + 1)) := by
  have hX : X * X ^ (q + 1) = X ^ (q + 2) := by
    simpa only [Nat.add_assoc] using (pow_succ' X (q + 1)).symm
  have hY : Y * Y ^ (q + 1) = Y ^ (q + 2) := by
    simpa only [Nat.add_assoc] using (pow_succ' Y (q + 1)).symm
  simp only [sub_mul, mul_sub, Matrix.trace_sub]
  rw [hX, hY, Matrix.trace_mul_comm Y (X ^ (q + 1))]
  ring

theorem hamiltonian_trace_squared_increment_expansion
    (X Y : Matrix I I Real) (q : Nat) :
    Matrix.trace ((X - Y) ^ 2 * (X ^ q + Y ^ q)) =
      Matrix.trace (X ^ (q + 2)) + Matrix.trace (Y ^ (q + 2)) +
        Matrix.trace (X ^ q * Y ^ 2) + Matrix.trace (X ^ 2 * Y ^ q) -
        2 * Matrix.trace (X ^ (q + 1) * Y) -
        2 * Matrix.trace (X * Y ^ (q + 1)) := by
  have hExpand : (X - Y) ^ 2 * (X ^ q + Y ^ q) =
      (X * X) * X ^ q + (X * X) * Y ^ q -
      (X * Y) * X ^ q - (X * Y) * Y ^ q -
      (Y * X) * X ^ q - (Y * X) * Y ^ q +
      (Y * Y) * X ^ q + (Y * Y) * Y ^ q := by
    noncomm_ring
  have hXX : (X * X) * X ^ q = X ^ (q + 2) := by
    rw [<- pow_two, <- pow_add]
    congr 1
    omega
  have hYY : (Y * Y) * Y ^ q = Y ^ (q + 2) := by
    rw [<- pow_two, <- pow_add]
    congr 1
    omega
  have hXYX : Matrix.trace ((X * Y) * X ^ q) =
      Matrix.trace (X ^ (q + 1) * Y) := by
    rw [Matrix.trace_mul_comm (X * Y) (X ^ q), <- Matrix.mul_assoc, <- pow_succ]
  have hXYY : (X * Y) * Y ^ q = X * Y ^ (q + 1) := by
    rw [Matrix.mul_assoc, <- pow_succ']
  have hYXX : Matrix.trace ((Y * X) * X ^ q) =
      Matrix.trace (X ^ (q + 1) * Y) := by
    rw [Matrix.mul_assoc, <- pow_succ', Matrix.trace_mul_comm]
  have hYXY : Matrix.trace ((Y * X) * Y ^ q) =
      Matrix.trace (X * Y ^ (q + 1)) := by
    rw [Matrix.trace_mul_comm (Y * X) (Y ^ q), <- Matrix.mul_assoc, <- pow_succ,
      Matrix.trace_mul_comm]
  have hYYX : Matrix.trace ((Y * Y) * X ^ q) =
      Matrix.trace (X ^ q * Y ^ 2) := by
    rw [<- pow_two, Matrix.trace_mul_comm]
  rw [hExpand]
  simp only [Matrix.trace_add, Matrix.trace_sub]
  rw [hXX, hYY, hXYX, hXYY, hYXX, hYXY, hYYX, <- pow_two]
  ring

theorem hamiltonian_trace_increment_power_readout
    (X Y : Matrix I I Real) (hX : X.IsHermitian) (hY : Y.IsHermitian) (q : Nat) :
    Matrix.trace ((X - Y) * (X ^ (q + 1) - Y ^ (q + 1))) =
      Finset.univ.sum (fun i => Finset.univ.sum (fun j =>
        (hX.eigenvalues i - hY.eigenvalues j) *
          (hX.eigenvalues i ^ (q + 1) - hY.eigenvalues j ^ (q + 1)) *
          (((realGaussianEigenMatrix X hX).transpose *
            realGaussianEigenMatrix Y hY) i j) ^ 2)) := by
  let x := hX.eigenvalues
  let y := hY.eigenvalues
  let w := fun i j => (((realGaussianEigenMatrix X hX).transpose *
    realGaussianEigenMatrix Y hY) i j) ^ 2
  have hRead (r s : Nat) : Matrix.trace (X ^ r * Y ^ s) =
      Finset.univ.sum (fun i => Finset.univ.sum (fun j => x i ^ r * y j ^ s * w i j)) :=
    hamiltonian_hermitian_mixed_power_trace X Y hX hY r s
  have hPureX (p : Nat) : Matrix.trace (X ^ p) =
      Finset.univ.sum (fun i => Finset.univ.sum (fun j => x i ^ p * w i j)) := by
    simpa only [pow_zero, Matrix.mul_one, mul_one] using hRead p 0
  have hPureY (p : Nat) : Matrix.trace (Y ^ p) =
      Finset.univ.sum (fun i => Finset.univ.sum (fun j => y j ^ p * w i j)) := by
    simpa only [pow_zero, Matrix.one_mul, one_mul] using hRead 0 p
  change _ = Finset.univ.sum (fun i => Finset.univ.sum (fun j =>
    (x i - y j) * (x i ^ (q + 1) - y j ^ (q + 1)) * w i j))
  rw [hamiltonian_trace_increment_power_expansion]
  have hCrossLeft : Matrix.trace (X ^ (q + 1) * Y) =
      Finset.univ.sum (fun i => Finset.univ.sum (fun j => x i ^ (q + 1) * y j * w i j)) := by
    simpa only [pow_one] using hRead (q + 1) 1
  have hCross : Matrix.trace (X * Y ^ (q + 1)) =
      Finset.univ.sum (fun i => Finset.univ.sum (fun j => x i * y j ^ (q + 1) * w i j)) := by
    simpa only [pow_one] using hRead 1 (q + 1)
  rw [hPureX, hPureY, hCrossLeft, hCross]
  calc
    _ = Finset.univ.sum (fun i => Finset.univ.sum (fun j =>
        (x i ^ (q + 2) + y j ^ (q + 2) -
          x i ^ (q + 1) * y j - x i * y j ^ (q + 1)) * w i j)) := by
      simp only [pow_one, add_mul, sub_mul, Finset.sum_add_distrib, Finset.sum_sub_distrib]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro i hi
      apply Finset.sum_congr rfl
      intro j hj
      simp only [pow_add, pow_one, pow_two]
      ring

theorem hamiltonian_trace_squared_increment_readout
    (X Y : Matrix I I Real) (hX : X.IsHermitian) (hY : Y.IsHermitian) (q : Nat) :
    Matrix.trace ((X - Y) ^ 2 * (X ^ q + Y ^ q)) =
      Finset.univ.sum (fun i => Finset.univ.sum (fun j =>
        (hX.eigenvalues i - hY.eigenvalues j) ^ 2 *
          (hX.eigenvalues i ^ q + hY.eigenvalues j ^ q) *
          (((realGaussianEigenMatrix X hX).transpose *
            realGaussianEigenMatrix Y hY) i j) ^ 2)) := by
  let x := hX.eigenvalues
  let y := hY.eigenvalues
  let w := fun i j => (((realGaussianEigenMatrix X hX).transpose *
    realGaussianEigenMatrix Y hY) i j) ^ 2
  have hRead (r s : Nat) : Matrix.trace (X ^ r * Y ^ s) =
      Finset.univ.sum (fun i => Finset.univ.sum (fun j => x i ^ r * y j ^ s * w i j)) :=
    hamiltonian_hermitian_mixed_power_trace X Y hX hY r s
  have hPureX (p : Nat) : Matrix.trace (X ^ p) =
      Finset.univ.sum (fun i => Finset.univ.sum (fun j => x i ^ p * w i j)) := by
    simpa only [pow_zero, Matrix.mul_one, mul_one] using hRead p 0
  have hPureY (p : Nat) : Matrix.trace (Y ^ p) =
      Finset.univ.sum (fun i => Finset.univ.sum (fun j => y j ^ p * w i j)) := by
    simpa only [pow_zero, Matrix.one_mul, one_mul] using hRead 0 p
  change _ = Finset.univ.sum (fun i => Finset.univ.sum (fun j =>
    (x i - y j) ^ 2 * (x i ^ q + y j ^ q) * w i j))
  rw [hamiltonian_trace_squared_increment_expansion]
  have hCrossLeft : Matrix.trace (X ^ (q + 1) * Y) =
      Finset.univ.sum (fun i => Finset.univ.sum (fun j => x i ^ (q + 1) * y j * w i j)) := by
    simpa only [pow_one] using hRead (q + 1) 1
  have hCross : Matrix.trace (X * Y ^ (q + 1)) =
      Finset.univ.sum (fun i => Finset.univ.sum (fun j => x i * y j ^ (q + 1) * w i j)) := by
    simpa only [pow_one] using hRead 1 (q + 1)
  rw [hPureX, hPureY, hRead q 2, hRead 2 q, hCrossLeft, hCross]
  calc
    _ = Finset.univ.sum (fun i => Finset.univ.sum (fun j =>
        (x i ^ (q + 2) + y j ^ (q + 2) + x i ^ q * y j ^ 2 +
          x i ^ 2 * y j ^ q - 2 * (x i ^ (q + 1) * y j) -
          2 * (x i * y j ^ (q + 1))) * w i j)) := by
      simp only [pow_one, add_mul, sub_mul, Finset.sum_add_distrib,
        Finset.sum_sub_distrib, Finset.mul_sum]
      ring
    _ = _ := by
      apply Finset.sum_congr rfl
      intro i hi
      apply Finset.sum_congr rfl
      intro j hj
      simp only [pow_add, pow_one, pow_two]
      ring

theorem hamiltonian_trace_mean_value
    (X Y : Matrix I I Real) (hX : X.IsHermitian) (hY : Y.IsHermitian)
    (q : Nat) (hEven : Even q) :
    Matrix.trace ((X - Y) * (X ^ (q + 1) - Y ^ (q + 1))) <=
      (((q + 1 : Nat) : Real) / 2) *
        Matrix.trace ((X - Y) ^ 2 * (X ^ q + Y ^ q)) := by
  rw [hamiltonian_trace_increment_power_readout X Y hX hY,
    hamiltonian_trace_squared_increment_readout X Y hX hY]
  simp only [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i hi
  apply Finset.sum_le_sum
  intro j hj
  have h := mul_le_mul_of_nonneg_right
    (hamiltonian_trace_mean_value_scalar (hX.eigenvalues i) (hY.eigenvalues j) q hEven)
    (sq_nonneg (((realGaussianEigenMatrix X hX).transpose *
      realGaussianEigenMatrix Y hY) i j))
  simpa only [mul_assoc] using h

theorem hamiltonian_trace_mean_value_odd_power
    (X Y : Matrix I I Real) (hX : X.IsHermitian) (hY : Y.IsHermitian)
    (k : Nat) (hk : 1 <= k) :
    Matrix.trace ((X - Y) * (X ^ (2 * k - 1) - Y ^ (2 * k - 1))) <=
      ((2 * (k : Real) - 1) / 2) *
        Matrix.trace ((X - Y) ^ 2 * (X ^ (2 * k - 2) + Y ^ (2 * k - 2))) := by
  let q := 2 * k - 2
  have hEven : Even q := Exists.intro (k - 1) (by dsimp only [q]; omega)
  have hSucc : q + 1 = 2 * k - 1 := by dsimp only [q]; omega
  have hAdd : ((2 * k - 1 : Nat) : Real) + 1 = 2 * (k : Real) := by
    exact_mod_cast Nat.sub_add_cancel (show 1 <= 2 * k by omega)
  have hCoeff : ((2 * k - 1 : Nat) : Real) = 2 * (k : Real) - 1 := by
    linarith only [hAdd]
  have h := hamiltonian_trace_mean_value X Y hX hY q hEven
  rw [hSucc, hCoeff] at h
  exact h

end PrimeFactorOscillations

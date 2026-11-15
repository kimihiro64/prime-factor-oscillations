/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.HamiltonianDeterminantEntryBudget
import PrimeFactorOscillations.Helpers.HamiltonianScalingLogRemainder

/-! # Signed trace expansion for the actual determinant ratio

The entrywise budget is applied only to terms beyond the full signed
linear trace. No symmetry, positivity or termwise trace erasure is assumed.
-/

set_option autoImplicit false
set_option Elab.async false

noncomputable section

namespace PrimeFactorOscillations

variable {Iota : Type*} [Fintype Iota] [DecidableEq Iota]

theorem hamiltonian_log_determinant_trace_entry_remainder
    (E : Matrix Iota Iota Real) (eps : Real) (hEps : 0 <= eps)
    (hEntry : forall i j, abs (E i j) <= eps)
    (hSmall : (Fintype.card Iota : Real) * eps <= 1 / 8) :
    0 < Matrix.det (1 + E) /\
    abs (Real.log (Matrix.det (1 + E)) - Matrix.trace E) <=
      8 * ((Fintype.card Iota : Real) * eps) ^ 2 := by
  let v := (Fintype.card Iota : Real) * eps
  let d := Matrix.det (1 + E)
  let x := d - 1
  have hv0 : 0 <= v := mul_nonneg (Nat.cast_nonneg _) hEps
  have hvSmall : v <= 1 / 8 := hSmall
  have hvHalf : v <= 1 / 2 := le_trans hvSmall (by norm_num)
  have hRemainder := hamiltonian_determinant_trace_entry_remainder E eps hEps hEntry hvHalf
  change abs (x - Matrix.trace E) <= 2 * v ^ 2 at hRemainder
  have hTrace : abs (Matrix.trace E) <= v := by
    calc
      _ <= Finset.sum Finset.univ (fun i => abs (E i i)) :=
        Finset.abs_sum_le_sum_abs _ _
      _ <= Finset.sum Finset.univ (fun _ : Iota => eps) :=
        Finset.sum_le_sum (fun i _ => hEntry i i)
      _ = _ := by simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]; rfl
  have hx : abs x <= 2 * v := by
    have hTriangle : abs x <= abs (x - Matrix.trace E) + abs (Matrix.trace E) := by
      calc
        _ = abs ((x - Matrix.trace E) + Matrix.trace E) := by congr 1; ring
        _ <= _ := abs_add_le _ _
    have hMul := mul_le_mul_of_nonneg_left hvHalf hv0
    nlinarith only [hTriangle, hRemainder, hTrace, hMul]
  have hxHalf : abs x <= 1 / 2 := by linarith only [hx, hvSmall]
  have hxSquare : x ^ 2 <= 4 * v ^ 2 := by
    have h := mul_le_mul hx hx (abs_nonneg x) (mul_nonneg (by norm_num) hv0)
    nlinarith only [h, sq_abs x]
  have hxCube : 2 * abs x ^ 3 <= x ^ 2 := by
    have h := mul_le_mul_of_nonneg_right hxHalf (sq_nonneg (abs x))
    nlinarith only [h, sq_abs x]
  have hOne : 1 + x = d := by dsimp only [x]; ring
  have hLog := hamiltonian_log_one_add_cubic_small x hxHalf
  rw [hOne] at hLog
  have hTriangle : abs (Real.log d - Matrix.trace E) <=
      abs (Real.log d - x + x ^ 2 / 2) +
        abs (x - Matrix.trace E) + x ^ 2 / 2 := by
    calc
      _ = abs (((Real.log d - x + x ^ 2 / 2) +
          (x - Matrix.trace E)) + -(x ^ 2 / 2)) := by congr 1; ring
      _ <= abs ((Real.log d - x + x ^ 2 / 2) +
          (x - Matrix.trace E)) + abs (-(x ^ 2 / 2)) := abs_add_le _ _
      _ <= (abs (Real.log d - x + x ^ 2 / 2) + abs (x - Matrix.trace E)) +
          x ^ 2 / 2 := by
        apply add_le_add
        exact abs_add_le _ _
        rw [abs_neg, abs_of_nonneg (by positivity)]
  have hPositive : 0 < d := by
    have h := (abs_le.mp hxHalf).1
    change -(1 / 2 : Real) <= d - 1 at h
    linarith only [h]
  exact And.intro hPositive
    (by nlinarith only [hTriangle, hLog, hRemainder, hxSquare, hxCube])

theorem hamiltonian_relative_log_determinant_entry_remainder
    (M R E : Matrix Iota Iota Real) (hInverse : M * R = 1)
    (eps : Real) (hEps : 0 <= eps)
    (hEntry : forall i j, abs ((R * E) i j) <= eps)
    (hSmall : (Fintype.card Iota : Real) * eps <= 1 / 8) :
    0 < Matrix.det (M + E) / Matrix.det M /\
    abs (Real.log (Matrix.det (M + E) / Matrix.det M) - Matrix.trace (R * E)) <=
      8 * ((Fintype.card Iota : Real) * eps) ^ 2 := by
  have hProduct : Matrix.det M * Matrix.det R = 1 := by
    rw [<- Matrix.det_mul, hInverse, Matrix.det_one]
  have hDet : Not (Matrix.det M = 0) := by
    intro h
    rw [h, zero_mul] at hProduct
    norm_num at hProduct
  have hFactor : M + E = M * (1 + R * E) := by
    rw [mul_add, mul_one, <- mul_assoc, hInverse, one_mul]
  have hRatio : Matrix.det (M + E) / Matrix.det M = Matrix.det (1 + R * E) := by
    rw [hFactor, Matrix.det_mul]
    field_simp
  rw [hRatio]
  exact hamiltonian_log_determinant_trace_entry_remainder (R * E) eps hEps hEntry hSmall

end PrimeFactorOscillations

/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import Mathlib.LinearAlgebra.Matrix.SchurComplement
import PrimeFactorOscillations.Helpers.HamiltonianMinorPolynomial

/-! # Bipartite determinant generating functions

The rectangular statement keeps independently selected row and column supports.
Its polynomial specialization is the generating function underlying the signed
occupancy moments, without assuming matching supports or discarding minors.
-/

set_option autoImplicit false
set_option Elab.async false

noncomputable section

namespace PrimeFactorOscillations

variable {Iota Jota R : Type*}
variable [DecidableEq Iota] [Fintype Iota]
variable [DecidableEq Jota] [Fintype Jota] [CommRing R]

def bipartiteLift (T : Matrix Iota Jota R) :
    Matrix (Sum Iota Jota) (Sum Iota Jota) R :=
  Matrix.fromBlocks 0 T T.transpose 0

theorem det_one_add_bipartiteLift (T : Matrix Iota Jota R) (t : R) :
    Matrix.det (1 + HSMul.hSMul t (bipartiteLift T)) =
      Matrix.det (1 - HSMul.hSMul (t ^ 2) (T.transpose * T)) := by
  classical
  have hBlocks :
      (1 : Matrix (Sum Iota Jota) (Sum Iota Jota) R) +
          HSMul.hSMul t (bipartiteLift T) =
        Matrix.fromBlocks 1 (HSMul.hSMul t T)
          (HSMul.hSMul t T.transpose) 1 := by
    ext i j
    cases i <;> cases j <;>
      simp [bipartiteLift, Matrix.fromBlocks, Matrix.one_apply, smul_eq_mul]
  rw [hBlocks]
  calc
    _ = Matrix.det (1 - HSMul.hSMul (t ^ 2) (T * T.transpose)) := by
      simp [Matrix.smul_mul, Matrix.mul_smul, smul_smul, pow_two]
    _ = _ := by
      simpa [Matrix.smul_mul, Matrix.mul_smul, smul_smul, pow_two] using
        (Matrix.det_one_sub_mul_comm (HSMul.hSMul t T)
          (HSMul.hSMul t T.transpose))

theorem principalMinorGeneratingPolynomial_bipartite (T : Matrix Iota Jota R) :
    principalMinorGeneratingPolynomial (bipartiteLift T) =
      Matrix.det ((1 : Matrix Jota Jota (Polynomial R)) -
        HSMul.hSMul ((Polynomial.X : Polynomial R) ^ 2)
          ((T.map Polynomial.C).transpose * T.map Polynomial.C)) := by
  classical
  unfold principalMinorGeneratingPolynomial
  have hMap : (bipartiteLift T).map Polynomial.C =
      bipartiteLift (T.map Polynomial.C) := by
    ext i j
    cases i <;> cases j <;> simp [bipartiteLift, Matrix.fromBlocks]
  rw [hMap, det_one_add_bipartiteLift]

end PrimeFactorOscillations

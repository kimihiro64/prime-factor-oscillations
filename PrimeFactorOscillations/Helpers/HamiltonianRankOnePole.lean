/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import Mathlib.Algebra.Polynomial.Derivative
import PrimeFactorOscillations.Helpers.HamiltonianRankOneDeterminant

/-! # Clearing every rank-one occupancy pole

For any nonempty principal support of size k, the apparent determinant pole
of order k reduces to a single pole. The cleared identity is polynomial and
uses no inverse, limit or nonsingularity premise. The root derivative retains
both the derivative of the determinant factor and that of the full cofactor
contraction, including all compensation terms.
-/

set_option autoImplicit false
set_option Elab.async false

noncomputable section

namespace PrimeFactorOscillations

variable {Iota R : Type*} [DecidableEq Iota] [Fintype Iota] [CommRing R]

def rowCofactorContraction (H : Matrix Iota Iota R) (u v : Iota -> R) : R :=
  Finset.sum Finset.univ (fun i => u i * Matrix.det (Matrix.updateRow H i v))

theorem rowCofactorContraction_smul (H : Matrix Iota Iota R)
    (u v : Iota -> R) (c : R) :
    rowCofactorContraction (HSMul.hSMul c H) u v =
      c ^ (Fintype.card Iota - 1) * rowCofactorContraction H u v := by
  unfold rowCofactorContraction
  simp only [Matrix.det_updateRow_smul_left]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  ring

theorem det_cleared_rankOne_pole [Nonempty Iota]
    (H : Matrix Iota Iota (Polynomial R)) (u v : Iota -> Polynomial R)
    (c : Polynomial R) :
    Matrix.det (fun i j => Polynomial.X * H i j + c * u i * v j) =
      Polynomial.X ^ (Fintype.card Iota - 1) *
        (Polynomial.X * Matrix.det H + c * rowCofactorContraction H u v) := by
  have hCard : 1 <= Fintype.card Iota := Fintype.card_pos
  have hPow : (Polynomial.X : Polynomial R) ^ Fintype.card Iota =
      Polynomial.X ^ (Fintype.card Iota - 1) * Polynomial.X := by
    calc
      _ = (Polynomial.X : Polynomial R) ^ ((Fintype.card Iota - 1) + 1) :=
        congrArg (fun n => (Polynomial.X : Polynomial R) ^ n)
          (Nat.sub_add_cancel hCard).symm
      _ = _ := pow_succ _ _
  calc
    _ = Matrix.det (HSMul.hSMul (Polynomial.X : Polynomial R) H) +
        c * rowCofactorContraction
          (HSMul.hSMul (Polynomial.X : Polynomial R) H) u v := by
      simpa only [rowCofactorContraction, Matrix.smul_apply, smul_eq_mul] using
        (det_rankOne_affine (HSMul.hSMul (Polynomial.X : Polynomial R) H) u v c)
    _ = _ := by
      rw [Matrix.det_smul, rowCofactorContraction_smul, hPow]
      ring

def compensatedPolePolynomial (p : Polynomial R)
    (H : Matrix Iota Iota (Polynomial R)) (u v : Iota -> Polynomial R) : Polynomial R :=
  p * (Polynomial.X * Matrix.det H - 2 * rowCofactorContraction H u v)

theorem compensatedPolePolynomial_rootDerivative (p : Polynomial R)
    (H : Matrix Iota Iota (Polynomial R)) (u v : Iota -> Polynomial R) :
    Polynomial.eval 0 (compensatedPolePolynomial p H u v).derivative =
      Polynomial.eval 0 p * Polynomial.eval 0 (Matrix.det H) -
        2 * (Polynomial.eval 0 p.derivative *
          Polynomial.eval 0 (rowCofactorContraction H u v) +
          Polynomial.eval 0 p *
            Polynomial.eval 0 (rowCofactorContraction H u v).derivative) := by
  simp [compensatedPolePolynomial, Polynomial.derivative_mul]
  ring

end PrimeFactorOscillations

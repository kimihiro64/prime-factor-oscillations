/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import Mathlib.Algebra.Polynomial.Eval.Degree
import Mathlib.Basic.Real.Basic
import Mathlib.LinearAlgebra.Matrix.AbsoluteValue
import Mathlib.Tactic.Linarith
import PrimeFactorOscillations.Helpers.HamiltonianMinorPolynomial

/-! # Entrywise determinant coefficients without a dimension loss

The linear coefficient remains the actual signed trace. Higher principal
minors are bounded only after their exact coefficient has been isolated.
The factorial from each minor is cancelled against the subset count.
-/

set_option autoImplicit false
set_option Elab.async false

noncomputable section

namespace PrimeFactorOscillations

variable {Iota : Type*} [Fintype Iota] [DecidableEq Iota]

theorem hamiltonian_determinant_coefficient_entry_bound
    (E : Matrix Iota Iota Real) (eps : Real) (hEps : 0 <= eps)
    (hEntry : forall i j, abs (E i j) <= eps) (k : Nat) :
    abs ((principalMinorGeneratingPolynomial E).coeff k) <=
      ((Fintype.card Iota : Real) * eps) ^ k := by
  change abs ((Matrix.det (1 + HSMul.hSMul (Polynomial.X : Polynomial Real)
    (E.map Polynomial.C))).coeff k) <= _
  rw [Matrix.coeff_det_one_add_X_smul_eq_sum_minors]
  calc
    _ <= Finset.sum ((Finset.univ : Finset Iota).powersetCard k)
        (fun S => abs (Matrix.det
          (E.submatrix (Subtype.val : S -> Iota) (Subtype.val : S -> Iota)))) :=
      Finset.abs_sum_le_sum_abs _ _
    _ <= Finset.sum ((Finset.univ : Finset Iota).powersetCard k)
        (fun _ => (k.factorial : Real) * eps ^ k) := by
      apply Finset.sum_le_sum
      intro S hS
      have hCard : S.card = k := (Finset.mem_powersetCard.mp hS).2
      have h := Matrix.det_le (abv := AbsoluteValue.abs)
        (fun i j : S => hEntry i.val j.val)
      simpa [AbsoluteValue.abs, Fintype.card_coe, hCard, nsmul_eq_mul] using! h
    _ = ((Fintype.card Iota).choose k : Real) * (k.factorial : Real) * eps ^ k := by
      simp only [Finset.sum_const, Finset.card_powersetCard, Finset.card_univ, nsmul_eq_mul]
      ring
    _ = ((Fintype.card Iota).descFactorial k : Real) * eps ^ k := by
      rw [Nat.descFactorial_eq_factorial_mul_choose, Nat.cast_mul]
      ring
    _ <= ((Fintype.card Iota : Real) ^ k) * eps ^ k := by
      have h : ((Fintype.card Iota).descFactorial k : Real) <=
          (Fintype.card Iota : Real) ^ k := by
        exact_mod_cast Nat.descFactorial_le_pow (Fintype.card Iota) k
      exact mul_le_mul_of_nonneg_right h (pow_nonneg hEps k)
    _ = _ := by rw [mul_pow]

theorem hamiltonian_geometric_sum_le_two
    (v : Real) (hv0 : 0 <= v) (hvHalf : v <= 1 / 2) (n : Nat) :
    Finset.sum (Finset.range n) (fun k => v ^ k) <= 2 := by
  have hStrong : forall m : Nat,
      Finset.sum (Finset.range m) (fun k => v ^ k) <= 2 * (1 - v ^ m) := by
    intro m
    induction m with
    | zero => simp
    | succ m ih =>
      rw [Finset.sum_range_succ, pow_succ]
      have hMul := mul_le_mul_of_nonneg_left hvHalf (pow_nonneg hv0 m)
      nlinarith only [ih, hMul]
  have h := hStrong n
  nlinarith only [h, pow_nonneg hv0 n]


theorem hamiltonian_determinant_trace_entry_remainder
    (E : Matrix Iota Iota Real) (eps : Real) (hEps : 0 <= eps)
    (hEntry : forall i j, abs (E i j) <= eps)
    (hSmall : (Fintype.card Iota : Real) * eps <= 1 / 2) :
    abs (Matrix.det (1 + E) - 1 - Matrix.trace E) <=
      2 * ((Fintype.card Iota : Real) * eps) ^ 2 := by
  let v := (Fintype.card Iota : Real) * eps
  let p := principalMinorGeneratingPolynomial E
  let Q := p.divX.divX
  have hv0 : 0 <= v := mul_nonneg (Nat.cast_nonneg _) hEps
  have hIdentity : Matrix.det (1 + E) - 1 - Matrix.trace E = Q.eval 1 := by
    have h := Matrix.det_one_add_smul (1 : Real) E
    simp only [one_smul, mul_one, one_pow] at h
    change Matrix.det (1 + E) = 1 + Matrix.trace E + Q.eval 1 at h
    linarith only [h]
  have hCoeff (k : Nat) : abs (Q.coeff k) <= v ^ (k + 2) := by
    have h := hamiltonian_determinant_coefficient_entry_bound E eps hEps hEntry (k + 2)
    simpa only [Q, p, Polynomial.coeff_divX, Nat.add_assoc] using h
  have hEval : Q.eval 1 =
      Finset.sum (Finset.range (Q.natDegree + 1)) (fun k => Q.coeff k) := by
    simpa only [one_pow, mul_one] using (Polynomial.eval_eq_sum_range (p := Q) (1 : Real))
  rw [hIdentity, hEval]
  calc
    _ <= Finset.sum (Finset.range (Q.natDegree + 1)) (fun k => abs (Q.coeff k)) :=
      Finset.abs_sum_le_sum_abs _ _
    _ <= Finset.sum (Finset.range (Q.natDegree + 1)) (fun k => v ^ (k + 2)) :=
      Finset.sum_le_sum (fun k _ => hCoeff k)
    _ = v ^ 2 * Finset.sum (Finset.range (Q.natDegree + 1)) (fun k => v ^ k) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro k _
      rw [pow_add]
      ring
    _ <= v ^ 2 * 2 := mul_le_mul_of_nonneg_left
      (hamiltonian_geometric_sum_le_two v hv0 hSmall (Q.natDegree + 1)) (sq_nonneg v)
    _ = _ := by ring

end PrimeFactorOscillations

/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.HamiltonianPhysicalFourierFrame

/-! # The complete signed rational operator and its exceptional blocks

Both character frames and the signed Mobius diagonal are retained.
Only the exact denominator-one and denominator-two blocks are separated.
Every other diagonal coefficient has modulus at most one half.
-/

set_option autoImplicit false
set_option Elab.async false

open scoped Matrix.Norms.L2Operator

noncomputable section

namespace PrimeFactorOscillations.LPF

def hamiltonianRationalOperator (n R : Nat) [NeZero R] (Q : Nat)
    (w : lpfRationalCenters Q -> Complex) : Matrix (Fin n) (Fin n) Complex :=
  HSMul.hSMul (Inv.inv (n : Complex))
    ((hamiltonianPhysicalFourierFrame n R (fun u => -hamiltonianRationalCenter R Q u) *
      Matrix.diagonal w) *
      (hamiltonianPhysicalFourierFrame n R (hamiltonianRationalCenter R Q)).conjTranspose)

def hamiltonianRationalLowCoefficient (Q : Nat) (u : lpfRationalCenters Q) : Complex :=
  if Or (u.1.val + 1 = 1) (u.1.val + 1 = 2)
    then lpfRationalCoefficient (u.1.val + 1) else 0

def hamiltonianRationalRestCoefficient (Q : Nat) (u : lpfRationalCenters Q) : Complex :=
  if Or (u.1.val + 1 = 1) (u.1.val + 1 = 2)
    then 0 else lpfRationalCoefficient (u.1.val + 1)

theorem hamiltonian_rational_operator_apply {R : Nat} [NeZero R]
    (n Q : Nat) (w : lpfRationalCenters Q -> Complex) (i j : Fin n) :
    hamiltonianRationalOperator n R Q w i j =
      (Finset.univ.sum (fun u : lpfRationalCenters Q =>
        w u * ZMod.stdAddChar
          ((-hamiltonianRationalCenter R Q u) *
            (((i.val + 1) + (j.val + 1) : Nat) : ZMod R)))) / (n : Complex) := by
  unfold hamiltonianRationalOperator
  rw [Matrix.mul_assoc]
  simp only [Matrix.smul_apply, smul_eq_mul]
  rw [Matrix.mul_apply]
  simp only [Matrix.diagonal_mul, Matrix.conjTranspose_apply,
    hamiltonianPhysicalFourierFrame]
  rw [div_eq_mul_inv, mul_comm _ (Inv.inv (n : Complex))]
  congr 1
  apply Finset.sum_congr rfl
  intro u hu
  have hArg : (-hamiltonianRationalCenter R Q u) *
      (((i.val + 1) + (j.val + 1) : Nat) : ZMod R) =
      (-hamiltonianRationalCenter R Q u) * ((i.val + 1 : Nat) : ZMod R) -
        hamiltonianRationalCenter R Q u * ((j.val + 1 : Nat) : ZMod R) := by
    push_cast
    ring
  rw [hArg, sub_eq_add_neg, AddChar.map_add_eq_mul, AddChar.map_neg_eq_conj]
  simp only [starRingEnd_apply]
  ring

theorem hamiltonian_rational_sum_operator {R : Nat} [NeZero R] (n Q : Nat) :
    hamiltonianRationalSumMatrix n R Q =
      hamiltonianRationalOperator n R Q (fun u => lpfRationalCoefficient (u.1.val + 1)) := by
  ext i j
  rw [hamiltonian_rational_operator_apply]
  rfl

theorem hamiltonian_rational_operator_add {R : Nat} [NeZero R]
    (n Q : Nat) (w z : lpfRationalCenters Q -> Complex) :
    hamiltonianRationalOperator n R Q (fun u => w u + z u) =
      hamiltonianRationalOperator n R Q w + hamiltonianRationalOperator n R Q z := by
  ext i j
  simp only [Matrix.add_apply, hamiltonian_rational_operator_apply]
  simp_rw [add_mul]
  rw [Finset.sum_add_distrib]
  ring

theorem hamiltonian_rational_low_rest_coefficient (Q : Nat) (u : lpfRationalCenters Q) :
    hamiltonianRationalLowCoefficient Q u + hamiltonianRationalRestCoefficient Q u =
      lpfRationalCoefficient (u.1.val + 1) := by
  unfold hamiltonianRationalLowCoefficient hamiltonianRationalRestCoefficient
  split <;> simp

theorem hamiltonian_rational_low_rest_split {R : Nat} [NeZero R] (n Q : Nat) :
    hamiltonianRationalSumMatrix n R Q =
      hamiltonianRationalOperator n R Q (hamiltonianRationalLowCoefficient Q) +
        hamiltonianRationalOperator n R Q (hamiltonianRationalRestCoefficient Q) := by
  rw [<- hamiltonian_rational_operator_add, hamiltonian_rational_sum_operator]
  congr 1
  funext u
  exact (hamiltonian_rational_low_rest_coefficient Q u).symm

theorem hamiltonian_rational_rest_coefficient_half (Q : Nat) (u : lpfRationalCenters Q) :
    norm (hamiltonianRationalRestCoefficient Q u) <= (1 / 2 : Real) := by
  classical
  unfold hamiltonianRationalRestCoefficient
  split
  next h => norm_num
  next h =>
    have hPhiNat : 0 < (u.1.val + 1).totient :=
      Nat.totient_pos.mpr (Nat.succ_pos _)
    have hNotOne : Not ((u.1.val + 1).totient = 1) := fun hEq =>
      h (Nat.totient_eq_one_iff.mp hEq)
    have hPhi : (2 : Real) <= ((u.1.val + 1).totient : Real) := by
      exact_mod_cast (show 2 <= (u.1.val + 1).totient by omega)
    have hPhiPos : (0 : Real) < ((u.1.val + 1).totient : Real) := by linarith
    calc
      _ <= 1 / ((u.1.val + 1).totient : Real) :=
        norm_lpfRationalCoefficient_le _ (Nat.succ_pos _)
      _ <= (((u.1.val + 1).totient : Real) / 2) /
          ((u.1.val + 1).totient : Real) :=
        div_le_div_of_nonneg_right (by linarith) hPhiPos.le
      _ = _ := by field_simp

end PrimeFactorOscillations.LPF

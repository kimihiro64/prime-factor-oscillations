/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import Mathlib.Data.Fintype.Pi
import PrimeFactorOscillations.Helpers.HamiltonianTraceMeanValue

/-! # The complete finite sign cube and its matrix increments

Every coordinate flip is included. The exact squared increment
is independent of the sign vector and retains the full summand.
These identities feed the signed trace moment recurrence.
-/

set_option autoImplicit false
set_option Elab.async false

noncomputable section

namespace PrimeFactorOscillations

variable {J : Type*} [Fintype J] [DecidableEq J]
variable {I : Type*} [Fintype I] [DecidableEq I]

def hamiltonianSignValue (b : Bool) : Real := if b then 1 else -1

def hamiltonianSignFlip (j : J) (e : J -> Bool) : J -> Bool :=
  fun i => if i = j then !(e i) else e i

theorem hamiltonian_sign_flip_involutive (j : J) :
    Function.Involutive (hamiltonianSignFlip j) := by
  intro e
  funext i
  by_cases hij : i = j
  case pos => simp [hamiltonianSignFlip, hij]
  case neg => simp [hamiltonianSignFlip, hij]

theorem hamiltonian_sign_flip_sum
    {V : Type*} [AddCommMonoid V] (j : J) (f : (J -> Bool) -> V) :
    Finset.univ.sum (fun e => f (hamiltonianSignFlip j e)) =
      Finset.univ.sum f := by
  exact Equiv.sum_comp
    (Function.Involutive.toPerm (hamiltonianSignFlip j)
      (hamiltonian_sign_flip_involutive j)) f

theorem hamiltonian_sign_value_square (b : Bool) :
    hamiltonianSignValue b ^ 2 = 1 := by
  cases b <;> norm_num [hamiltonianSignValue]

theorem hamiltonian_sign_value_flip (b : Bool) :
    hamiltonianSignValue (!b) = -hamiltonianSignValue b := by
  cases b <;> norm_num [hamiltonianSignValue]

def hamiltonianSignMatrix (A : J -> Matrix I I Real) (e : J -> Bool) : Matrix I I Real :=
  Finset.univ.sum (fun j => SMul.smul (hamiltonianSignValue (e j)) (A j))

def hamiltonianSignVariance (A : J -> Matrix I I Real) : Matrix I I Real :=
  Finset.univ.sum (fun j => A j ^ 2)

theorem hamiltonian_sign_smul_entry
    (c : Real) (M : Matrix I I Real) (r s : I) :
    (SMul.smul c M) r s = c * M r s := rfl

theorem hamiltonian_sign_matrix_hermitian
    (A : J -> Matrix I I Real) (hA : forall j, (A j).IsHermitian) (e : J -> Bool) :
    (hamiltonianSignMatrix A e).IsHermitian := by
  have hEntry (j : J) (r s : I) : A j s r = A j r s := by
    have h := hA j
    change (A j).conjTranspose = A j at h
    simpa using congrArg (fun M : Matrix I I Real => M r s) h
  change (hamiltonianSignMatrix A e).conjTranspose = hamiltonianSignMatrix A e
  ext r s
  simp only [Matrix.conjTranspose_apply]
  change hamiltonianSignMatrix A e s r = hamiltonianSignMatrix A e r s
  simp only [hamiltonianSignMatrix, Matrix.sum_apply, hamiltonian_sign_smul_entry]
  apply Finset.sum_congr rfl
  intro j hj
  rw [hEntry]

theorem hamiltonian_sign_matrix_increment
    (A : J -> Matrix I I Real) (j : J) (e : J -> Bool) :
    hamiltonianSignMatrix A e - hamiltonianSignMatrix A (hamiltonianSignFlip j e) =
      SMul.smul (2 * hamiltonianSignValue (e j)) (A j) := by
  ext r s
  simp only [hamiltonianSignMatrix, Matrix.sub_apply, Matrix.sum_apply,
    hamiltonian_sign_smul_entry]
  rw [<- Finset.sum_sub_distrib]
  have hTerm (i : J) :
      hamiltonianSignValue (e i) * A i r s -
          hamiltonianSignValue (hamiltonianSignFlip j e i) * A i r s =
        if i = j then 2 * hamiltonianSignValue (e j) * A j r s else 0 := by
    by_cases hij : i = j
    case pos =>
      subst i
      simp [hamiltonianSignFlip, hamiltonian_sign_value_flip] <;> ring
    case neg => simp [hamiltonianSignFlip, hij]
  simp_rw [hTerm]
  simp

theorem hamiltonian_sign_matrix_increment_square
    (A : J -> Matrix I I Real) (j : J) (e : J -> Bool) :
    (hamiltonianSignMatrix A e - hamiltonianSignMatrix A (hamiltonianSignFlip j e)) ^ 2 =
      SMul.smul (4 : Real) (A j ^ 2) := by
  rw [hamiltonian_sign_matrix_increment]
  ext r s
  simp only [pow_two, Matrix.mul_apply, hamiltonian_sign_smul_entry]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  have hSq := hamiltonian_sign_value_square (e j)
  calc
    _ = 4 * hamiltonianSignValue (e j) ^ 2 * (A j r i * A j i s) := by ring
    _ = _ := by rw [hSq]; ring

theorem hamiltonian_sign_matrix_increment_sum
    (A : J -> Matrix I I Real) (e : J -> Bool) :
    Finset.univ.sum (fun j =>
      hamiltonianSignMatrix A e - hamiltonianSignMatrix A (hamiltonianSignFlip j e)) =
      SMul.smul (2 : Real) (hamiltonianSignMatrix A e) := by
  simp_rw [hamiltonian_sign_matrix_increment]
  ext r s
  simp only [hamiltonianSignMatrix, Matrix.sum_apply, hamiltonian_sign_smul_entry,
    Finset.mul_sum, mul_assoc]

end PrimeFactorOscillations

/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.HamiltonianSignCube

/-! # Exact finite sign-flip trace moments

The complete sign cube and every coordinate flip remain coupled.
The two powers in the trace mean-value estimate are combined by
the exact flip bijection before using any variance inequality.
-/

set_option autoImplicit false
set_option Elab.async false

noncomputable section

namespace PrimeFactorOscillations

variable {J : Type*} [Fintype J] [DecidableEq J]
variable {I : Type*} [Fintype I] [DecidableEq I]

theorem hamiltonian_trace_scaled_left
    (c : Real) (X Y : Matrix I I Real) :
    Matrix.trace ((SMul.smul c X) * Y) = c * Matrix.trace (X * Y) := by
  have hScale : (SMul.smul c X) * Y = SMul.smul c (X * Y) := by
    ext r s
    simp only [Matrix.mul_apply, hamiltonian_sign_smul_entry, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    ring
  rw [hScale]
  unfold Matrix.trace
  simp only [Matrix.diag_apply, hamiltonian_sign_smul_entry, Finset.mul_sum]

theorem hamiltonian_sign_flip_trace_compensation
    (F : (J -> Bool) -> Matrix I I Real) (j : J) (p : Nat) :
    Finset.univ.sum (fun e => Matrix.trace
      ((F e - F (hamiltonianSignFlip j e)) * F (hamiltonianSignFlip j e) ^ p)) =
      -Finset.univ.sum (fun e => Matrix.trace
        ((F e - F (hamiltonianSignFlip j e)) * F e ^ p)) := by
  let g := fun e => Matrix.trace
    ((F e - F (hamiltonianSignFlip j e)) * F (hamiltonianSignFlip j e) ^ p)
  calc
    _ = Finset.univ.sum (fun e => g (hamiltonianSignFlip j e)) :=
      (hamiltonian_sign_flip_sum j g).symm
    _ = _ := by
      rw [<- Finset.sum_neg_distrib]
      apply Finset.sum_congr rfl
      intro e he
      dsimp only [g]
      rw [hamiltonian_sign_flip_involutive j e]
      have hNeg : F (hamiltonianSignFlip j e) - F e =
          -(F e - F (hamiltonianSignFlip j e)) := by noncomm_ring
      rw [hNeg, neg_mul, Matrix.trace_neg]

theorem hamiltonian_sign_increment_moment_identity
    (A : J -> Matrix I I Real) (p : Nat) :
    4 * Finset.univ.sum (fun e => Matrix.trace (hamiltonianSignMatrix A e ^ (p + 1))) =
      Finset.univ.sum (fun e => Finset.univ.sum (fun j => Matrix.trace
        ((hamiltonianSignMatrix A e - hamiltonianSignMatrix A (hamiltonianSignFlip j e)) *
          (hamiltonianSignMatrix A e ^ p -
            hamiltonianSignMatrix A (hamiltonianSignFlip j e) ^ p)))) := by
  let F := hamiltonianSignMatrix A
  let T := fun e j => Matrix.trace ((F e - F (hamiltonianSignFlip j e)) * F e ^ p)
  let U := fun e j => Matrix.trace
    ((F e - F (hamiltonianSignFlip j e)) * F (hamiltonianSignFlip j e) ^ p)
  have hFirst (e : J -> Bool) :
      Finset.univ.sum (T e) = 2 * Matrix.trace (F e ^ (p + 1)) := by
    calc
      _ = Matrix.trace
          ((Finset.univ.sum (fun j => F e - F (hamiltonianSignFlip j e))) * F e ^ p) := by
        simp only [Matrix.sum_mul, Matrix.trace_sum]
        rfl
      _ = Matrix.trace ((SMul.smul (2 : Real) (F e)) * F e ^ p) := by
        rw [hamiltonian_sign_matrix_increment_sum]
      _ = _ := by
        rw [hamiltonian_trace_scaled_left, <- pow_succ']
  have hSecond : Finset.univ.sum (fun e => Finset.univ.sum (U e)) =
      -Finset.univ.sum (fun e => Finset.univ.sum (T e)) := by
    calc
      _ = Finset.univ.sum (fun j => Finset.univ.sum (fun e => U e j)) := Finset.sum_comm
      _ = Finset.univ.sum (fun j => -Finset.univ.sum (fun e => T e j)) := by
        apply Finset.sum_congr rfl
        intro j hj
        exact hamiltonian_sign_flip_trace_compensation F j p
      _ = _ := by rw [Finset.sum_neg_distrib, Finset.sum_comm]
  change 4 * Finset.univ.sum (fun e => Matrix.trace (F e ^ (p + 1))) =
    Finset.univ.sum (fun e => Finset.univ.sum (fun j => Matrix.trace
      ((F e - F (hamiltonianSignFlip j e)) *
        (F e ^ p - F (hamiltonianSignFlip j e) ^ p))))
  simp only [Matrix.mul_sub, Matrix.trace_sub, Finset.sum_sub_distrib]
  change _ = Finset.univ.sum (fun e => Finset.univ.sum (T e)) -
    Finset.univ.sum (fun e => Finset.univ.sum (U e))
  rw [hSecond]
  simp_rw [hFirst]
  rw [<- Finset.mul_sum]
  ring

theorem hamiltonian_sign_squared_increment_moment_identity
    (A : J -> Matrix I I Real) (q : Nat) :
    Finset.univ.sum (fun e => Finset.univ.sum (fun j => Matrix.trace
      ((hamiltonianSignMatrix A e - hamiltonianSignMatrix A (hamiltonianSignFlip j e)) ^ 2 *
        (hamiltonianSignMatrix A e ^ q +
          hamiltonianSignMatrix A (hamiltonianSignFlip j e) ^ q)))) =
      8 * Finset.univ.sum (fun e => Matrix.trace
        (hamiltonianSignVariance A * hamiltonianSignMatrix A e ^ q)) := by
  let F := hamiltonianSignMatrix A
  let T := fun e j => Matrix.trace (A j ^ 2 * F e ^ q)
  let U := fun e j => Matrix.trace (A j ^ 2 * F (hamiltonianSignFlip j e) ^ q)
  have hPoint (e : J -> Bool) (j : J) :
      Matrix.trace ((F e - F (hamiltonianSignFlip j e)) ^ 2 *
        (F e ^ q + F (hamiltonianSignFlip j e) ^ q)) =
        4 * T e j + 4 * U e j := by
    rw [hamiltonian_sign_matrix_increment_square, Matrix.mul_add, Matrix.trace_add,
      hamiltonian_trace_scaled_left, hamiltonian_trace_scaled_left]
  have hSame : Finset.univ.sum (fun e => Finset.univ.sum (U e)) =
      Finset.univ.sum (fun e => Finset.univ.sum (T e)) := by
    calc
      _ = Finset.univ.sum (fun j => Finset.univ.sum (fun e => U e j)) := Finset.sum_comm
      _ = Finset.univ.sum (fun j => Finset.univ.sum (fun e => T e j)) := by
        apply Finset.sum_congr rfl
        intro j hj
        exact hamiltonian_sign_flip_sum j (fun e => Matrix.trace (A j ^ 2 * F e ^ q))
      _ = _ := Finset.sum_comm
  have hVariance (e : J -> Bool) :
      Finset.univ.sum (T e) = Matrix.trace (hamiltonianSignVariance A * F e ^ q) := by
    simp only [hamiltonianSignVariance, Matrix.sum_mul, Matrix.trace_sum]
    rfl
  change Finset.univ.sum (fun e => Finset.univ.sum (fun j => Matrix.trace
    ((F e - F (hamiltonianSignFlip j e)) ^ 2 *
      (F e ^ q + F (hamiltonianSignFlip j e) ^ q)))) = _
  simp_rw [hPoint]
  simp only [Finset.sum_add_distrib, <- Finset.mul_sum]
  rw [hSame]
  simp_rw [hVariance]
  ring

theorem hamiltonian_sign_trace_moment_variance_bound
    (A : J -> Matrix I I Real) (hA : forall j, (A j).IsHermitian)
    (q : Nat) (hEven : Even q) :
    Finset.univ.sum (fun e => Matrix.trace (hamiltonianSignMatrix A e ^ (q + 2))) <=
      ((q + 1 : Nat) : Real) * Finset.univ.sum (fun e => Matrix.trace
        (hamiltonianSignVariance A * hamiltonianSignMatrix A e ^ q)) := by
  let F := hamiltonianSignMatrix A
  have hPoint (e : J -> Bool) (j : J) :=
    hamiltonian_trace_mean_value (F e) (F (hamiltonianSignFlip j e))
      (hamiltonian_sign_matrix_hermitian A hA e)
      (hamiltonian_sign_matrix_hermitian A hA (hamiltonianSignFlip j e)) q hEven
  have hSum := Finset.sum_le_sum (s := Finset.univ) (fun e he =>
    Finset.sum_le_sum (s := Finset.univ) (fun j hj => hPoint e j))
  simp only [<- Finset.mul_sum] at hSum
  have hIdentity := hamiltonian_sign_increment_moment_identity A (q + 1)
  have hSucc : q + 1 + 1 = q + 2 := by omega
  rw [hSucc] at hIdentity
  change 4 * Finset.univ.sum (fun e => Matrix.trace (F e ^ (q + 2))) = _ at hIdentity
  rw [<- hIdentity, hamiltonian_sign_squared_increment_moment_identity] at hSum
  change Finset.univ.sum (fun e => Matrix.trace (F e ^ (q + 2))) <= _
  linarith only [hSum]

theorem hamiltonian_sign_trace_even_moment_recurrence
    (A : J -> Matrix I I Real) (hA : forall j, (A j).IsHermitian)
    (k : Nat) (hk : 1 <= k) :
    Finset.univ.sum (fun e => Matrix.trace (hamiltonianSignMatrix A e ^ (2 * k))) <=
      (2 * (k : Real) - 1) * Finset.univ.sum (fun e => Matrix.trace
        (hamiltonianSignVariance A * hamiltonianSignMatrix A e ^ (2 * k - 2))) := by
  let q := 2 * k - 2
  have hEven : Even q := Exists.intro (k - 1) (by dsimp only [q]; omega)
  have hSucc : q + 1 = 2 * k - 1 := by dsimp only [q]; omega
  have hPower : q + 2 = 2 * k := by dsimp only [q]; omega
  have hAdd : ((2 * k - 1 : Nat) : Real) + 1 = 2 * (k : Real) := by
    exact_mod_cast Nat.sub_add_cancel (show 1 <= 2 * k by omega)
  have hCoeff : ((2 * k - 1 : Nat) : Real) = 2 * (k : Real) - 1 := by
    linarith only [hAdd]
  have h := hamiltonian_sign_trace_moment_variance_bound A hA q hEven
  rw [hSucc, hPower, hCoeff] at h
  exact h

end PrimeFactorOscillations

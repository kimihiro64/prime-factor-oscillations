/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.HamiltonianPrimeDegrees

/-! # The actual real prime matrix and its complete analytic inputs

Real vectors embed isometrically into the complex Euclidean space.
The real operator norm is therefore bounded by its exact complex image.
This transfers the true-prime half-gap without a norm conversion loss.
-/

set_option autoImplicit false
set_option Elab.async false

open scoped Matrix.Norms.L2Operator

noncomputable section

namespace PrimeFactorOscillations.LPF

variable {Iota : Type*} [Fintype Iota] [DecidableEq Iota]

def hamiltonianComplexVector (x : EuclideanSpace Real Iota) : EuclideanSpace Complex Iota :=
  WithLp.toLp 2 (fun i => (x.ofLp i : Complex))

def hamiltonianComplexMatrix (M : Matrix Iota Iota Real) : Matrix Iota Iota Complex :=
  fun i j => (M i j : Complex)

theorem hamiltonian_complex_vector_norm (x : EuclideanSpace Real Iota) :
    norm (hamiltonianComplexVector x) = norm x := by
  have hSquare : norm (hamiltonianComplexVector x) ^ 2 = norm x ^ 2 := by
    rw [EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq]
    apply Finset.sum_congr rfl
    intro i hi
    change norm (x.ofLp i : Complex) ^ 2 = norm (x.ofLp i) ^ 2
    rw [Complex.norm_real]
  nlinarith only [hSquare, norm_nonneg (hamiltonianComplexVector x), norm_nonneg x]

theorem hamiltonian_real_complex_l2_norm_le (M : Matrix Iota Iota Real) :
    norm M <= norm (hamiltonianComplexMatrix M) := by
  let opR := (@Matrix.toEuclideanCLM Real Iota _ _ _) M
  let opC := (@Matrix.toEuclideanCLM Complex Iota _ _ _) (hamiltonianComplexMatrix M)
  have hImage (x : EuclideanSpace Real Iota) :
      hamiltonianComplexVector (opR x) = opC (hamiltonianComplexVector x) := by
    ext i
    change ((Finset.univ.sum (fun j => M i j * x.ofLp j) : Real) : Complex) =
      Finset.univ.sum (fun j => (M i j : Complex) * (x.ofLp j : Complex))
    push_cast <;> rfl
  have hNorm : norm opR <= norm opC := by
    apply ContinuousLinearMap.opNorm_le_bound opR (norm_nonneg _)
    intro x
    have h := opC.le_opNorm (hamiltonianComplexVector x)
    rw [<- hImage x, hamiltonian_complex_vector_norm, hamiltonian_complex_vector_norm] at h
    exact h
  rwa [Matrix.l2_opNorm_toEuclideanCLM, Matrix.l2_opNorm_toEuclideanCLM] at hNorm

theorem hamiltonian_complex_matrix_sub (M N : Matrix Iota Iota Real) :
    hamiltonianComplexMatrix (M - N) =
      hamiltonianComplexMatrix M - hamiltonianComplexMatrix N := by
  ext i j
  simp only [hamiltonianComplexMatrix, Matrix.sub_apply, Complex.ofReal_sub]

def hamiltonianPrimeRealMatrix (n : Nat) : Matrix (Fin n) (Fin n) Real :=
  fun i j => if i = j then 0 else
    hamiltonianPrimeValue ((i.val + 1) + (j.val + 1)) / (n : Real)

def hamiltonianRealConstantParityMatrix (n : Nat) : Matrix (Fin n) (Fin n) Real :=
  fun i j => (1 - (-1 : Real) ^ ((i.val + 1) + (j.val + 1))) / (n : Real)

theorem hamiltonian_prime_real_complex_matrix (n : Nat) :
    hamiltonianComplexMatrix (hamiltonianPrimeRealMatrix n) = hamiltonianPrimeSumMatrix n := by
  classical
  ext i j
  rw [hamiltonian_prime_sum_matrix_apply]
  by_cases hij : i = j
  . simp [hamiltonianComplexMatrix, hamiltonianPrimeRealMatrix, hij]
  . by_cases hp : Nat.Prime ((i.val + 1) + (j.val + 1))
    <;> simp [hamiltonianComplexMatrix, hamiltonianPrimeRealMatrix,
      hamiltonianPrimeValue, hij, hp]

theorem hamiltonian_real_constant_parity_complex_matrix (n : Nat) :
    hamiltonianComplexMatrix (hamiltonianRealConstantParityMatrix n) =
      hamiltonianConstantParityMatrix n := by
  ext i j
  unfold hamiltonianComplexMatrix hamiltonianRealConstantParityMatrix hamiltonianConstantParityMatrix
  push_cast <;> rfl

theorem hamiltonian_prime_real_operator_gap (eps : Real) (hEps : 0 < eps) :
    exists N0 : Nat, And (1 <= N0)
      (forall n : Nat, N0 <= n ->
        norm (hamiltonianPrimeRealMatrix n - hamiltonianRealConstantParityMatrix n) <=
          (1 / 2 : Real) + eps) := by
  choose N0 hN0 hGap using hamiltonian_true_prime_operator_gap eps hEps
  refine Exists.intro N0 (And.intro hN0 ?_)
  intro n hn
  have h := hamiltonian_real_complex_l2_norm_le
    (hamiltonianPrimeRealMatrix n - hamiltonianRealConstantParityMatrix n)
  rw [hamiltonian_complex_matrix_sub, hamiltonian_prime_real_complex_matrix,
    hamiltonian_real_constant_parity_complex_matrix] at h
  exact h.trans (hGap n hn)

theorem hamiltonian_prime_real_row_degree (n : Nat) (i : Fin n) :
    Finset.univ.sum (fun j : Fin n => hamiltonianPrimeRealMatrix n i j) =
      hamiltonianPrimeDegree n i := by
  have h := hamiltonian_prime_degree_cast n i
  rw [<- hamiltonian_prime_real_complex_matrix] at h
  change Finset.univ.sum (fun j : Fin n =>
    (hamiltonianPrimeRealMatrix n i j : Complex)) = (hamiltonianPrimeDegree n i : Complex) at h
  apply Complex.ofReal_injective
  push_cast
  exact h

theorem hamiltonian_prime_real_degree_uniform (m : Nat) :
    exists D : Real, And (0 < D)
      (exists N0 : Nat, And (256 <= N0)
        (forall n : Nat, N0 <= n -> forall i : Fin n,
          abs (Finset.univ.sum (fun j : Fin n => hamiltonianPrimeRealMatrix n i j) - 1) <=
            D / Real.log (n : Real) ^ m)) := by
  choose D hD N0 hN0 hDegree using hamiltonian_prime_degree_uniform m
  refine Exists.intro D (And.intro hD (Exists.intro N0 (And.intro hN0 ?_)))
  intro n hn i
  rw [hamiltonian_prime_real_row_degree]
  exact hDegree n hn i

theorem hamiltonian_prime_real_nonnegative (n : Nat) (i j : Fin n) :
    0 <= hamiltonianPrimeRealMatrix n i j := by
  unfold hamiltonianPrimeRealMatrix
  split
  next => exact le_refl _
  next => exact div_nonneg (hamiltonian_prime_value_nonnegative _) (Nat.cast_nonneg n)

theorem hamiltonian_prime_real_symmetric (n : Nat) (i j : Fin n) :
    hamiltonianPrimeRealMatrix n i j = hamiltonianPrimeRealMatrix n j i := by
  classical
  by_cases hij : i = j
  . subst j
    rfl
  . have hji : Not (j = i) := fun h => hij h.symm
    simp only [hamiltonianPrimeRealMatrix, hij, hji, ite_false]
    rw [Nat.add_comm (i.val + 1) (j.val + 1)]

theorem hamiltonian_prime_real_entry_bound {n : Nat} [NeZero n] (i j : Fin n) :
    hamiltonianPrimeRealMatrix n i j <= Real.log (2 * (n : Real)) / (n : Real) := by
  have hn : (1 : Real) <= (n : Real) := by exact_mod_cast (NeZero.pos n)
  have hBound := hamiltonian_prime_raw_entry_bound i j
  unfold hamiltonianPrimeRawMatrix at hBound
  rw [norm_div, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (hamiltonian_prime_value_nonnegative _), Complex.norm_natCast] at hBound
  unfold hamiltonianPrimeRealMatrix
  split
  next => exact div_nonneg (Real.log_nonneg (by linarith only [hn])) (Nat.cast_nonneg n)
  next => exact hBound


theorem hamiltonian_prime_real_diagonal (n : Nat) (i : Fin n) :
    hamiltonianPrimeRealMatrix n i i = 0 := by
  simp only [hamiltonianPrimeRealMatrix, ite_true]

theorem hamiltonian_prime_real_bipartite (n : Nat) (i j : Fin n)
    (hParity : i.val % 2 = j.val % 2) :
    hamiltonianPrimeRealMatrix n i j = 0 := by
  classical
  by_cases hij : i = j
  . simp only [hamiltonianPrimeRealMatrix, hij, ite_true]
  . have hNotPrime : Not (Nat.Prime ((i.val + 1) + (j.val + 1))) := by
      intro hp
      cases hp.eq_two_or_odd with
      | inl hTwo =>
          apply hij
          apply Fin.ext
          omega
      | inr hOdd => omega
    simp only [hamiltonianPrimeRealMatrix, hij, ite_false, hamiltonianPrimeValue,
      hNotPrime, zero_div]

end PrimeFactorOscillations.LPF

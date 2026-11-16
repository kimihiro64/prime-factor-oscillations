/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.HamiltonianPrimeOperatorGap
import PrimeFactorOscillations.Helpers.HamiltonianPrimeSupportNorm
import PrimeFactorOscillations.Helpers.ThetaPolylogDecay

/-! # Exact true-prime support and its removed-mass operator error

The physical row images are retained as injective subsets of [1,2n].
The complete nonprime Mangoldt mass is exactly psi(2n)-theta(2n).
The diagonal prime contribution is accounted for separately.
-/

set_option autoImplicit false
set_option Elab.async false

open scoped Matrix.Norms.L2Operator

noncomputable section

namespace PrimeFactorOscillations.LPF

def hamiltonianPrimeValue (t : Nat) : Real := if Nat.Prime t then Real.log (t : Real) else 0

def hamiltonianPrimePowerError (t : Nat) : Real :=
  ArithmeticFunction.vonMangoldt t - hamiltonianPrimeValue t

def hamiltonianPrimeRawMatrix (n : Nat) : Matrix (Fin n) (Fin n) Complex :=
  fun i j => (hamiltonianPrimeValue ((i.val + 1) + (j.val + 1)) : Complex) / (n : Complex)

def hamiltonianPrimeSumMatrix (n : Nat) : Matrix (Fin n) (Fin n) Complex :=
  hamiltonianPrimeRawMatrix n -
    Matrix.diagonal (fun i => hamiltonianPrimeRawMatrix n i i)

theorem hamiltonian_prime_power_error_eq (t : Nat) :
    hamiltonianPrimePowerError t = if Nat.Prime t then 0 else ArithmeticFunction.vonMangoldt t := by
  unfold hamiltonianPrimePowerError hamiltonianPrimeValue
  by_cases h : Nat.Prime t
  . rw [if_pos h, if_pos h, ArithmeticFunction.vonMangoldt_apply_prime h, sub_self]
  . simp only [h, ite_false, sub_zero]

theorem hamiltonian_prime_power_error_nonnegative (t : Nat) :
    0 <= hamiltonianPrimePowerError t := by
  rw [hamiltonian_prime_power_error_eq]
  split
  next => exact le_refl _
  next => exact ArithmeticFunction.vonMangoldt_nonneg

theorem hamiltonian_prime_power_error_sum (M : Nat) :
    (Finset.Ioc 0 M).sum hamiltonianPrimePowerError =
      Chebyshev.psi (M : Real) - Chebyshev.theta (M : Real) := by
  rw [Chebyshev.psi_sub_theta_eq_sum_not_prime, Nat.floor_natCast, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro t ht
  rw [hamiltonian_prime_power_error_eq]
  by_cases h : Nat.Prime t <;> simp only [h, ite_true, ite_false, not_true_eq_false, not_false_eq_true]

theorem hamiltonian_prime_power_error_row (n : Nat) (i : Fin n) :
    Finset.univ.sum (fun j : Fin n =>
      hamiltonianPrimePowerError ((i.val + 1) + (j.val + 1))) <=
        Chebyshev.psi (2 * (n : Real)) - Chebyshev.theta (2 * (n : Real)) := by
  classical
  let f := fun j : Fin n => (i.val + 1) + (j.val + 1)
  let S := Finset.univ.image f
  have hInj : Set.InjOn f ((Finset.univ : Finset (Fin n)) : Set (Fin n)) := by
    intro a ha b hb h
    apply Fin.ext
    dsimp [f] at h
    omega
  have hSub : S <= Finset.Ioc 0 (2 * n) := by
    intro t ht
    choose j hj hEq using Finset.mem_image.mp ht
    rw [<- hEq]
    apply Finset.mem_Ioc.mpr
    have hi := i.isLt
    have hjn := j.isLt
    dsimp [f]
    constructor <;> omega
  calc
    _ = S.sum hamiltonianPrimePowerError := (Finset.sum_image hInj).symm
    _ <= (Finset.Ioc 0 (2 * n)).sum hamiltonianPrimePowerError :=
      Finset.sum_le_sum_of_subset_of_nonneg hSub
        (fun t ht htNot => hamiltonian_prime_power_error_nonnegative t)
    _ = _ := by
      rw [hamiltonian_prime_power_error_sum]
      norm_cast

theorem hamiltonian_prime_raw_difference_norm {n : Nat} [NeZero n] (i j : Fin n) :
    norm ((hamiltonianMangoldtSumMatrix n - hamiltonianPrimeRawMatrix n) i j) =
      hamiltonianPrimePowerError ((i.val + 1) + (j.val + 1)) / (n : Real) := by
  change norm ((ArithmeticFunction.vonMangoldt ((i.val + 1) + (j.val + 1)) : Complex) / (n : Complex) -
    (hamiltonianPrimeValue ((i.val + 1) + (j.val + 1)) : Complex) / (n : Complex)) = _
  rw [<- sub_div, <- Complex.ofReal_sub, norm_div, Complex.norm_real, Real.norm_eq_abs,
    Complex.norm_natCast]
  change abs (hamiltonianPrimePowerError ((i.val + 1) + (j.val + 1))) / (n : Real) = _
  rw [abs_of_nonneg (hamiltonian_prime_power_error_nonnegative _)]

theorem hamiltonian_prime_raw_operator_error {n : Nat} [NeZero n] :
    norm (hamiltonianMangoldtSumMatrix n - hamiltonianPrimeRawMatrix n) <=
      (Chebyshev.psi (2 * (n : Real)) - Chebyshev.theta (2 * (n : Real))) / (n : Real) := by
  have hSym : forall i j : Fin n,
      (hamiltonianMangoldtSumMatrix n - hamiltonianPrimeRawMatrix n) i j =
        (hamiltonianMangoldtSumMatrix n - hamiltonianPrimeRawMatrix n) j i := by
    intro i j
    change (ArithmeticFunction.vonMangoldt ((i.val + 1) + (j.val + 1)) : Complex) / (n : Complex) -
      (hamiltonianPrimeValue ((i.val + 1) + (j.val + 1)) : Complex) / (n : Complex) = _
    rw [Nat.add_comm (i.val + 1) (j.val + 1)]
    rfl
  apply hamiltonian_complex_symmetric_row_budget _ hSym _
    (div_nonneg (sub_nonneg.mpr (Chebyshev.theta_le_psi _)) (Nat.cast_nonneg _))
  intro i
  simp_rw [hamiltonian_prime_raw_difference_norm]
  rw [<- Finset.sum_div]
  exact div_le_div_of_nonneg_right (hamiltonian_prime_power_error_row n i) (Nat.cast_nonneg n)

theorem hamiltonian_prime_value_nonnegative (t : Nat) : 0 <= hamiltonianPrimeValue t := by
  unfold hamiltonianPrimeValue
  split
  next h => exact Real.log_nonneg (by exact_mod_cast h.one_lt.le)
  next => exact le_refl _

theorem hamiltonian_prime_raw_entry_bound {n : Nat} [NeZero n] (i j : Fin n) :
    norm (hamiltonianPrimeRawMatrix n i j) <= Real.log (2 * (n : Real)) / (n : Real) := by
  have hn : (1 : Real) <= (n : Real) := by exact_mod_cast (NeZero.pos n)
  have hi := i.isLt
  have hj := j.isLt
  have ht : 0 < (i.val + 1) + (j.val + 1) := by omega
  have hTop : (((i.val + 1) + (j.val + 1) : Nat) : Real) <= 2 * (n : Real) := by
    exact_mod_cast (show (i.val + 1) + (j.val + 1) <= 2 * n by omega)
  have hValue : hamiltonianPrimeValue ((i.val + 1) + (j.val + 1)) <= Real.log (2 * (n : Real)) := by
    unfold hamiltonianPrimeValue
    split
    next h => exact Real.log_le_log (by exact_mod_cast ht) hTop
    next => exact Real.log_nonneg (by linarith only [hn])
  unfold hamiltonianPrimeRawMatrix
  rw [norm_div, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (hamiltonian_prime_value_nonnegative _), Complex.norm_natCast]
  exact div_le_div_of_nonneg_right hValue (Nat.cast_nonneg n)

theorem hamiltonian_prime_diagonal_error {n : Nat} [NeZero n] :
    norm (Matrix.diagonal (fun i => hamiltonianPrimeRawMatrix n i i)) <=
      Real.log (2 * (n : Real)) / (n : Real) := by
  have hn : (1 : Real) <= (n : Real) := by exact_mod_cast (NeZero.pos n)
  have hR : 0 <= Real.log (2 * (n : Real)) / (n : Real) := by
    exact div_nonneg (Real.log_nonneg (by linarith only [hn])) (Nat.cast_nonneg n)
  rw [Matrix.l2_opNorm_diagonal]
  exact (pi_norm_le_iff_of_nonneg hR).mpr (fun i => hamiltonian_prime_raw_entry_bound i i)

theorem hamiltonian_prime_support_operator_error {n : Nat} [NeZero n] :
    norm (hamiltonianMangoldtSumMatrix n - hamiltonianPrimeSumMatrix n) <=
      (Chebyshev.psi (2 * (n : Real)) - Chebyshev.theta (2 * (n : Real)) +
        Real.log (2 * (n : Real))) / (n : Real) := by
  have hExact : hamiltonianMangoldtSumMatrix n - hamiltonianPrimeSumMatrix n =
      (hamiltonianMangoldtSumMatrix n - hamiltonianPrimeRawMatrix n) +
        Matrix.diagonal (fun i => hamiltonianPrimeRawMatrix n i i) := by
    unfold hamiltonianPrimeSumMatrix
    abel
  rw [hExact]
  calc
    _ <= norm (hamiltonianMangoldtSumMatrix n - hamiltonianPrimeRawMatrix n) +
      norm (Matrix.diagonal (fun i => hamiltonianPrimeRawMatrix n i i)) := norm_add_le _ _
    _ <= (Chebyshev.psi (2 * (n : Real)) - Chebyshev.theta (2 * (n : Real))) / (n : Real) +
        Real.log (2 * (n : Real)) / (n : Real) :=
      add_le_add hamiltonian_prime_raw_operator_error hamiltonian_prime_diagonal_error
    _ = _ := by ring

theorem hamiltonian_prime_support_square_root_error :
    exists C : Real, And (0 < C) (forall n : Nat, 0 < n ->
      norm (hamiltonianMangoldtSumMatrix n - hamiltonianPrimeSumMatrix n) <=
        (C * Real.sqrt (2 * (n : Real)) + Real.log (2 * (n : Real))) / (n : Real)) := by
  choose C hC using Chebyshev.psi_sub_theta_le_mul_sqrt
  refine Exists.intro (abs C + 1) (And.intro (by positivity) ?_)
  intro n hn
  letI : NeZero n := NeZero.mk (Nat.ne_of_gt hn)
  have hMass := (hC (2 * (n : Real))).trans
    (mul_le_mul_of_nonneg_right (le_trans (le_abs_self C) (by linarith : abs C <= abs C + 1))
      (Real.sqrt_nonneg _))
  exact hamiltonian_prime_support_operator_error.trans
    (div_le_div_of_nonneg_right (add_le_add hMass (le_refl _)) (Nat.cast_nonneg n))

end PrimeFactorOscillations.LPF

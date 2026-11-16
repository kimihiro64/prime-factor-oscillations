/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.HamiltonianPrimeLogTransfer

/-! # The actual constant-edge prime matrix with its complete transfer error

The original distinct-prime and loop masks are retained. Every physical
row is charged to its injective output interval and then to the complete
finite prime mass comparison. Both row and column budgets are consumed
by the real Euclidean operator bound.
-/

set_option autoImplicit false
set_option Elab.async false

open scoped Matrix.Norms.L2Operator

noncomputable section

namespace PrimeFactorOscillations.LPF

def hamiltonianUnweightedPrimeMatrix (n : Nat) : Matrix (Fin n) (Fin n) Real :=
  fun i j => if i = j then 0
    else if Nat.Prime ((i.val + 1) + (j.val + 1))
      then Real.log (n : Real) / (n : Real) else 0

theorem hamiltonian_unweighted_prime_symmetric (n : Nat) (i j : Fin n) :
    hamiltonianUnweightedPrimeMatrix n i j = hamiltonianUnweightedPrimeMatrix n j i := by
  by_cases hij : i = j
  . subst j
    rfl
  . have hji : Not (j = i) := fun h => hij h.symm
    simp only [hamiltonianUnweightedPrimeMatrix, hij, hji, ite_false]
    rw [Nat.add_comm (i.val + 1) (j.val + 1)]

theorem hamiltonian_unweighted_prime_entry_difference (n : Nat) (i j : Fin n) :
    abs (hamiltonianUnweightedPrimeMatrix n i j - hamiltonianPrimeRealMatrix n i j) <=
      hamiltonianPrimeLogWeight n ((i.val + 1) + (j.val + 1)) / (n : Real) := by
  by_cases hij : i = j
  . simp only [hamiltonianUnweightedPrimeMatrix, hamiltonianPrimeRealMatrix, hij,
      ite_true, sub_self, abs_zero]
    exact div_nonneg (hamiltonian_prime_log_weight_nonnegative _ _) (Nat.cast_nonneg n)
  . by_cases hp : Nat.Prime ((i.val + 1) + (j.val + 1))
    . simp only [hamiltonianUnweightedPrimeMatrix, hamiltonianPrimeRealMatrix,
        hamiltonianPrimeLogWeight, hamiltonianPrimeValue, hij, hp, ite_false, ite_true]
      rw [<- sub_div, abs_div,
        abs_of_nonneg (Nat.cast_nonneg n : (0 : Real) <= (n : Real))]
    . simp only [hamiltonianUnweightedPrimeMatrix, hamiltonianPrimeRealMatrix,
        hamiltonianPrimeLogWeight, hamiltonianPrimeValue, hij, hp, ite_false,
        zero_div, sub_self, abs_zero, le_refl]

theorem hamiltonian_unweighted_prime_row_transfer (n : Nat)
    (hn : 1 <= n) (hL : 64 <= Real.log (n : Real)) (i : Fin n) :
    Finset.univ.sum (fun j => abs
      (hamiltonianUnweightedPrimeMatrix n i j - hamiltonianPrimeRealMatrix n i j)) <=
      hamiltonianPrimeLogTransferError n := by
  have hRange : i.val + 1 + n <= 2 * n := by have h := i.isLt; omega
  have hWindow := hamiltonian_nonnegative_shift_budget n (i.val + 1) (2 * n)
    (hamiltonianPrimeLogWeight n) hRange
    (fun t _ => hamiltonian_prime_log_weight_nonnegative n t)
  calc
    _ <= Finset.univ.sum (fun j : Fin n =>
        hamiltonianPrimeLogWeight n ((i.val + 1) + (j.val + 1)) / (n : Real)) :=
      Finset.sum_le_sum (fun j _ => hamiltonian_unweighted_prime_entry_difference n i j)
    _ = Finset.univ.sum (fun j : Fin n =>
        hamiltonianPrimeLogWeight n ((i.val + 1) + (j.val + 1))) / (n : Real) :=
      (Finset.sum_div _ _ _).symm
    _ <= (Finset.Ioc 0 (2 * n)).sum (hamiltonianPrimeLogWeight n) / (n : Real) :=
      div_le_div_of_nonneg_right hWindow (Nat.cast_nonneg n)
    _ <= _ := hamiltonian_prime_log_transfer_sum n hn hL

theorem hamiltonian_unweighted_prime_column_transfer (n : Nat)
    (hn : 1 <= n) (hL : 64 <= Real.log (n : Real)) (j : Fin n) :
    Finset.univ.sum (fun i => abs
      (hamiltonianUnweightedPrimeMatrix n i j - hamiltonianPrimeRealMatrix n i j)) <=
      hamiltonianPrimeLogTransferError n := by
  have h := hamiltonian_unweighted_prime_row_transfer n hn hL j
  convert h using 1
  apply Finset.sum_congr rfl
  intro i hi
  rw [hamiltonian_unweighted_prime_symmetric n i j, hamiltonian_prime_real_symmetric n i j]

theorem hamiltonian_unweighted_prime_operator_transfer (n : Nat)
    (hn : 1 <= n) (hL : 64 <= Real.log (n : Real)) :
    norm (hamiltonianUnweightedPrimeMatrix n - hamiltonianPrimeRealMatrix n) <=
      hamiltonianPrimeLogTransferError n := by
  have hMass : 0 <= (Finset.Ioc 0 (2 * n)).sum (hamiltonianPrimeLogWeight n) :=
    Finset.sum_nonneg (fun t _ => hamiltonian_prime_log_weight_nonnegative n t)
  have hError : 0 <= hamiltonianPrimeLogTransferError n :=
    (div_nonneg hMass (Nat.cast_nonneg n)).trans (hamiltonian_prime_log_transfer_sum n hn hL)
  apply hamiltonian_l2_row_column_budget _ _ hError
  . intro i
    simpa only [Matrix.sub_apply, Real.norm_eq_abs] using
      hamiltonian_unweighted_prime_row_transfer n hn hL i
  . intro j
    simpa only [Matrix.sub_apply, Real.norm_eq_abs] using
      hamiltonian_unweighted_prime_column_transfer n hn hL j

end PrimeFactorOscillations.LPF

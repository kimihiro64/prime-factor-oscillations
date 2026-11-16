/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.HamiltonianBalancedRationalFactors
import PrimeFactorOscillations.Helpers.HamiltonianPrimeFiniteModeApproximation
import PrimeFactorOscillations.Helpers.HamiltonianPrimeLogTransferDecay

/-! # Actual simple prime matrices have uniformly bounded real finite modes -/

set_option autoImplicit false
set_option Elab.async false

open scoped Matrix.Norms.L2Operator

noncomputable section

namespace PrimeFactorOscillations.LPF

def hamiltonianPrimeRealFiniteModeModel (n R : Nat) [NeZero R] (K : Nat) :
    Matrix (Fin n) (Fin n) Real :=
  hamiltonianRealPartMatrix (hamiltonianPrimeFiniteModeModel n R K)

theorem hamiltonian_prime_sum_real_part (n : Nat) :
    hamiltonianRealPartMatrix (hamiltonianPrimeSumMatrix n) =
      hamiltonianPrimeRealMatrix n := by
  rw [<- hamiltonian_prime_real_complex_matrix]
  ext i j
  rfl

theorem hamiltonian_prime_real_finite_mode_factors (n R : Nat) [NeZero R]
    (K : Nat) (hn : 0 < n) :
    exists U : Matrix (Fin n)
        (Sum (lpfRationalCenters (27 * K ^ 4)) (lpfRationalCenters (27 * K ^ 4))) Real,
      exists V : Matrix
        (Sum (lpfRationalCenters (27 * K ^ 4)) (lpfRationalCenters (27 * K ^ 4))) (Fin n) Real,
        hamiltonianPrimeRealFiniteModeModel n R K = U * V /\
          norm U <=
            (Fintype.card (Sum (lpfRationalCenters (27 * K ^ 4))
              (lpfRationalCenters (27 * K ^ 4))) : Real) + 1 /\
          norm V <=
            (Fintype.card (Sum (lpfRationalCenters (27 * K ^ 4))
              (lpfRationalCenters (27 * K ^ 4))) : Real) + 1 := by
  apply hamiltonian_rational_real_bounded_factorization n R (27 * K ^ 4) hn
    (fun u => if u.1.val + 1 <= hamiltonianPrimeCutoff (2 * n)
      then lpfRationalCoefficient (u.1.val + 1) else 0)
  intro u
  split_ifs
  next h => exact hamiltonian_rational_coefficient_norm_one _ (Nat.succ_pos _)
  next h => norm_num

theorem hamiltonian_prime_real_finite_mode_approximation_uniform
    (eta : Real) (hEta : 0 < eta) :
    exists K : Nat, 0 < K /\
      exists N0 : Nat, 1 <= N0 /\
        forall {n R : Nat} [NeZero n] [NeZero R],
          N0 <= n -> 2 * n < R -> Dvd.dvd (2 * n) R ->
          (forall q, 0 < q -> q <= hamiltonianPrimeCutoff (2 * n) -> Dvd.dvd q R) ->
          norm (hamiltonianUnweightedPrimeMatrix n -
            hamiltonianPrimeRealFiniteModeModel n R K) <= eta := by
  have hThird : 0 < eta / 3 := div_pos hEta (by norm_num)
  choose K hK N1 hN1 hApprox using
    hamiltonian_prime_finite_mode_approximation_uniform (eta / 3) hThird
  choose N2 hN2 hLog using hamiltonian_unweighted_prime_operator_uniform (eta / 3) hThird
  choose N3 hN3 hSupport using hamiltonian_prime_support_error_vanishes (eta / 3) hThird
  let N0 := max N1 (max N2 N3)
  refine Exists.intro K (And.intro hK (Exists.intro N0
    (And.intro (hN1.trans (le_max_left _ _)) ?_)))
  intro n R instN instR hn hGrid hDivM hDiv
  have hn1 : N1 <= n := (le_max_left _ _).trans hn
  have hn2 : N2 <= n := (le_trans (le_max_left _ _) (le_max_right _ _)).trans hn
  have hn3 : N3 <= n := (le_trans (le_max_right _ _) (le_max_right _ _)).trans hn
  have hA := hApprox (n := n) (R := R) hn1 hGrid hDivM hDiv
  have hS := hSupport n hn3
  have hL := hLog n hn2
  have hTriangle := norm_sub_le_norm_sub_add_norm_sub (hamiltonianPrimeSumMatrix n)
    (hamiltonianMangoldtSumMatrix n) (hamiltonianPrimeFiniteModeModel n R K)
  rw [norm_sub_rev (hamiltonianPrimeSumMatrix n) (hamiltonianMangoldtSumMatrix n)] at hTriangle
  have hReal : norm (hamiltonianPrimeRealMatrix n -
      hamiltonianPrimeRealFiniteModeModel n R K) <=
        norm (hamiltonianPrimeSumMatrix n - hamiltonianPrimeFiniteModeModel n R K) := by
    have h := hamiltonian_real_part_matrix_norm_le
      (hamiltonianPrimeSumMatrix n - hamiltonianPrimeFiniteModeModel n R K)
    simpa only [hamiltonian_real_part_matrix_sub, hamiltonian_prime_sum_real_part,
      hamiltonianPrimeRealFiniteModeModel] using h
  have hPhysical := norm_sub_le_norm_sub_add_norm_sub
    (hamiltonianUnweightedPrimeMatrix n) (hamiltonianPrimeRealMatrix n)
    (hamiltonianPrimeRealFiniteModeModel n R K)
  linarith only [hA, hS, hL, hTriangle, hReal, hPhysical]

end PrimeFactorOscillations.LPF

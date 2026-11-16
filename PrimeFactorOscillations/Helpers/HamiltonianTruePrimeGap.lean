/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.HamiltonianPrimeSupportError

/-! # The unconditional half-gap on the actual true-prime support

Every removed proper prime power and loop is retained in an explicit
operator error. Its uniform decay is consumed with the actual integer
Mangoldt half-gap. The final matrix has precisely the distinct prime-sum
weights, without a probability proxy or auxiliary grid.
-/

set_option autoImplicit false
set_option Elab.async false

open scoped Matrix.Norms.L2Operator

noncomputable section

namespace PrimeFactorOscillations.LPF

theorem hamiltonian_prime_sum_matrix_apply (n : Nat) (i j : Fin n) :
    hamiltonianPrimeSumMatrix n i j =
      if i = j then 0 else
        if Nat.Prime ((i.val + 1) + (j.val + 1))
          then (Real.log (((i.val + 1) + (j.val + 1) : Nat) : Real) : Complex) / (n : Complex)
          else 0 := by
  classical
  by_cases h : i = j
  . subst j
    simp [hamiltonianPrimeSumMatrix]
  . by_cases hp : Nat.Prime ((i.val + 1) + (j.val + 1))
    <;> simp [hamiltonianPrimeSumMatrix, h, hp,
      hamiltonianPrimeRawMatrix, hamiltonianPrimeValue]

theorem hamiltonian_prime_support_error_vanishes (eps : Real) (hEps : 0 < eps) :
    exists N0 : Nat, And (1 <= N0)
      (forall n : Nat, N0 <= n ->
        norm (hamiltonianMangoldtSumMatrix n - hamiltonianPrimeSumMatrix n) <= eps) := by
  choose C hC hError using hamiltonian_prime_support_square_root_error
  let K := 4 * C + 1
  have hK : 0 < K := by dsimp [K]; positivity
  choose N0 hN0 hDom using hamiltonian_log_power_dominated_uniform
    (K / eps) (div_pos hK hEps) 1 (1 / 2) (by norm_num)
  refine Exists.intro N0 (And.intro (le_trans (by decide : 1 <= 256) hN0) ?_)
  intro n hn
  have hnPos : 0 < n := by omega
  have hnR : (1 : Real) <= (n : Real) := by exact_mod_cast hnPos
  let s := Real.sqrt (n : Real)
  let L := Real.log (2 * (n : Real))
  have hsSquare : s ^ 2 = (n : Real) := Real.sq_sqrt (Nat.cast_nonneg n)
  have hs0 : 0 <= s := Real.sqrt_nonneg _
  have hs1 : 1 <= s := by nlinarith only [hsSquare, hs0, hnR]
  have hRootSquare : Real.sqrt (2 * (n : Real)) ^ 2 = 2 * (n : Real) :=
    Real.sq_sqrt (by positivity)
  have hRoot0 : 0 <= Real.sqrt (2 * (n : Real)) := Real.sqrt_nonneg _
  have hRoot : Real.sqrt (2 * (n : Real)) <= 2 * s := by
    nlinarith only [hRootSquare, hsSquare, hs0, hRoot0, hnR]
  have hLog2 : (1 / 2 : Real) <= Real.log (2 : Real) := by
    have h := Real.log_le_sub_one_of_pos
      (by norm_num : (0 : Real) < (2 : Real) ^ (-1 : Int))
    rw [zpow_neg_one, Real.log_inv] at h
    norm_num at h
    linarith
  have hL : (1 / 2 : Real) <= L := by
    have h := Real.log_le_log (by norm_num : (0 : Real) < 2)
      (show (2 : Real) <= 2 * (n : Real) by linarith only [hnR])
    dsimp [L]
    linarith only [hLog2, h]
  have hL0 : 0 <= L := by linarith only [hL]
  have hNum : C * Real.sqrt (2 * (n : Real)) + L <= K * L * s := by
    have hFirst := mul_le_mul_of_nonneg_left hRoot hC.le
    have hSecond := mul_le_mul_of_nonneg_left hs1 hL0
    have hThird := mul_le_mul_of_nonneg_right hL (by positivity : 0 <= 4 * C * s)
    dsimp [K]
    nlinarith only [hFirst, hSecond, hThird]
  have hBound := hDom n hn
  simp only [pow_one] at hBound
  rw [<- Real.sqrt_eq_rpow] at hBound
  change (K / eps) * L <= s at hBound
  have hScaled : K * L <= eps * s := by
    have h := mul_le_mul_of_nonneg_right hBound hEps.le
    have hCancel : ((K / eps) * L) * eps = K * L := by field_simp
    rw [hCancel] at h
    nlinarith only [h]
  have hTotal : C * Real.sqrt (2 * (n : Real)) + L <= eps * (n : Real) := by
    have h : K * L * s <= eps * (n : Real) := by
      calc
        _ <= (eps * s) * s := mul_le_mul_of_nonneg_right hScaled hs0
        _ = _ := by rw [mul_assoc, <- pow_two, hsSquare]
    exact hNum.trans h
  exact (hError n hnPos).trans (by
    change (C * Real.sqrt (2 * (n : Real)) + L) / (n : Real) <= eps
    calc
      _ <= (eps * (n : Real)) / (n : Real) :=
        div_le_div_of_nonneg_right hTotal (Nat.cast_nonneg n)
      _ = _ := by field_simp)

theorem hamiltonian_true_prime_operator_gap (eps : Real) (hEps : 0 < eps) :
    exists N0 : Nat, And (1 <= N0)
      (forall n : Nat, N0 <= n ->
        norm (hamiltonianPrimeSumMatrix n - hamiltonianConstantParityMatrix n) <=
          (1 / 2 : Real) + eps) := by
  choose A hA hMangoldt using hamiltonian_prime_operator_gap (eps / 2) (by positivity)
  choose B hB hRemoved using hamiltonian_prime_support_error_vanishes (eps / 2) (by positivity)
  let N0 := max A B
  refine Exists.intro N0 (And.intro (hA.trans (le_max_left _ _)) ?_)
  intro n hn
  have hFirst := hMangoldt n ((le_max_left A B).trans hn)
  have hSecond := hRemoved n ((le_max_right A B).trans hn)
  have hTriangle := norm_sub_le_norm_sub_add_norm_sub
    (hamiltonianPrimeSumMatrix n) (hamiltonianMangoldtSumMatrix n)
    (hamiltonianConstantParityMatrix n)
  rw [norm_sub_rev (hamiltonianPrimeSumMatrix n) (hamiltonianMangoldtSumMatrix n)] at hTriangle
  linarith only [hFirst, hSecond, hTriangle]

end PrimeFactorOscillations.LPF

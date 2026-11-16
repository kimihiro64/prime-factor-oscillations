/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.HamiltonianUnweightedPrimeTransfer

/-! # Uniform disappearance of the complete unweighted-prime transfer error

The explicit finite comparison is consumed on an entire terminal interval.
The actual constant-edge matrix inherits uniform degrees and the full
constant/parity half-gap. No subsequence or numerical sample is used.
-/

set_option autoImplicit false
set_option Elab.async false

open scoped Matrix.Norms.L2Operator

noncomputable section

namespace PrimeFactorOscillations.LPF

def hamiltonianPrimeLogDecayConstant : Real :=
  1 + 16 * Real.log 4 + 4 * Real.log 4 * Real.log 2

theorem hamiltonian_prime_log_decay_constant_positive :
    0 < hamiltonianPrimeLogDecayConstant := by
  have hFour : 0 <= Real.log (4 : Real) := Real.log_nonneg (by norm_num)
  have hTwo : 0 <= Real.log (2 : Real) := Real.log_nonneg (by norm_num)
  unfold hamiltonianPrimeLogDecayConstant
  positivity

theorem hamiltonian_log_terminal_lower (b : Real) :
    exists N0 : Nat, And (1 <= N0)
      (forall n : Nat, N0 <= n -> b <= Real.log (n : Real)) := by
  let B := max 0 b
  let N0 := Nat.ceil (Real.exp B)
  have hB : 0 <= B := le_max_left _ _
  have hExp : (1 : Real) <= Real.exp B := by
    simpa only [Real.exp_zero] using Real.exp_le_exp.mpr hB
  have hN0 : (1 : Real) <= (N0 : Real) := hExp.trans (Nat.le_ceil (Real.exp B))
  refine Exists.intro N0 (And.intro (by exact_mod_cast hN0) ?_)
  intro n hn
  have hArg : Real.exp B <= (n : Real) :=
    (Nat.le_ceil (Real.exp B)).trans (Nat.cast_le.mpr hn)
  have hLog := Real.log_le_log (Real.exp_pos B) hArg
  rw [Real.log_exp] at hLog
  exact (le_max_right 0 b).trans hLog

theorem hamiltonian_prime_log_transfer_sqrt_bound (n : Nat)
    (hL : 64 <= Real.log (n : Real)) :
    hamiltonianPrimeLogTransferError n <=
      hamiltonianPrimeLogDecayConstant / Real.sqrt (Real.log (n : Real)) := by
  let L := Real.log (n : Real)
  let s := Real.sqrt L
  let b := 1 + 4 * Real.log 4 * Real.log 2
  have hLOne : 1 <= L := by dsimp only [L]; linarith only [hL]
  have hLPos : 0 < L := lt_of_lt_of_le zero_lt_one hLOne
  have hs : 0 <= s := Real.sqrt_nonneg L
  have hsPos : 0 < s := Real.sqrt_pos.mpr hLPos
  have hSquare : s ^ 2 = L := Real.sq_sqrt hLPos.le
  have hsOne : 1 <= s := by nlinarith only [hSquare, hs, hLOne]
  have hLogEq : Real.log L = 2 * Real.log s := by
    calc
      _ = Real.log (s ^ 2) := congrArg Real.log hSquare.symm
      _ = _ := by rw [Real.log_pow]; norm_num
  have hLogSqrt := Real.log_le_sub_one_of_pos hsPos
  have hLog : Real.log L <= 2 * s := by nlinarith only [hLogEq, hLogSqrt]
  have hFour : 0 <= Real.log (4 : Real) := Real.log_nonneg (by norm_num)
  have hTwo : 0 <= Real.log (2 : Real) := Real.log_nonneg (by norm_num)
  have hb : 0 <= b := by dsimp only [b]; positivity
  have hConst : b <= b * s := by
    simpa only [mul_one] using mul_le_mul_of_nonneg_left hsOne hb
  have hLogFactor := mul_le_mul_of_nonneg_left hLog
    (by positivity : 0 <= 8 * Real.log (4 : Real))
  have hNumerator : 1 + 4 * Real.log 4 * (2 * Real.log L + Real.log 2) <=
      hamiltonianPrimeLogDecayConstant * s := by
    dsimp only [b] at hConst
    unfold hamiltonianPrimeLogDecayConstant
    nlinarith only [hConst, hLogFactor]
  have hFormula : hamiltonianPrimeLogDecayConstant * s / L =
      hamiltonianPrimeLogDecayConstant / s := by
    rw [<- hSquare]
    field_simp [ne_of_gt hsPos]
  change (1 + 4 * Real.log 4 * (2 * Real.log L + Real.log 2)) / L <=
    hamiltonianPrimeLogDecayConstant / s
  exact (div_le_div_of_nonneg_right hNumerator hLPos.le).trans_eq hFormula

theorem hamiltonian_prime_log_transfer_error_uniform (eps : Real) (hEps : 0 < eps) :
    exists N0 : Nat, And (1 <= N0)
      (forall n : Nat, N0 <= n ->
        And (64 <= Real.log (n : Real)) (hamiltonianPrimeLogTransferError n <= eps)) := by
  let C := hamiltonianPrimeLogDecayConstant
  have hC : 0 < C := hamiltonian_prime_log_decay_constant_positive
  let b := max 64 ((C / eps) ^ 2)
  choose N0 hN0 hLog using hamiltonian_log_terminal_lower b
  refine Exists.intro N0 (And.intro hN0 ?_)
  intro n hn
  have hLower := hLog n hn
  have hL : 64 <= Real.log (n : Real) := (le_max_left _ _).trans hLower
  have hRatio : (C / eps) ^ 2 <= Real.log (n : Real) := (le_max_right _ _).trans hLower
  have hL0 : 0 <= Real.log (n : Real) := by linarith only [hL]
  have hRatioPos : 0 < C / eps := div_pos hC hEps
  have hSqrt : C / eps <= Real.sqrt (Real.log (n : Real)) := by
    nlinarith only [hRatio, Real.sq_sqrt hL0, Real.sqrt_nonneg (Real.log (n : Real)), hRatioPos]
  have hBound : C / Real.sqrt (Real.log (n : Real)) <= eps := by
    calc
      _ <= C / (C / eps) := div_le_div_of_nonneg_left hC.le hRatioPos hSqrt
      _ = eps := by field_simp [ne_of_gt hC, ne_of_gt hEps]
  exact And.intro hL ((hamiltonian_prime_log_transfer_sqrt_bound n hL).trans hBound)

theorem hamiltonian_unweighted_prime_operator_uniform (eps : Real) (hEps : 0 < eps) :
    exists N0 : Nat, And (1 <= N0)
      (forall n : Nat, N0 <= n ->
        norm (hamiltonianUnweightedPrimeMatrix n - hamiltonianPrimeRealMatrix n) <= eps) := by
  choose N0 hN0 hError using hamiltonian_prime_log_transfer_error_uniform eps hEps
  refine Exists.intro N0 (And.intro hN0 ?_)
  intro n hn
  exact (hamiltonian_unweighted_prime_operator_transfer n (hN0.trans hn) (hError n hn).1).trans
    (hError n hn).2

theorem hamiltonian_unweighted_prime_operator_gap (eps : Real) (hEps : 0 < eps) :
    exists N0 : Nat, And (1 <= N0)
      (forall n : Nat, N0 <= n ->
        norm (hamiltonianUnweightedPrimeMatrix n - hamiltonianRealConstantParityMatrix n) <=
          (1 / 2 : Real) + eps) := by
  have hHalf : 0 < eps / 2 := by linarith only [hEps]
  choose N1 hN1 hError using hamiltonian_unweighted_prime_operator_uniform (eps / 2) hHalf
  choose N2 hN2 hGap using hamiltonian_prime_real_operator_gap (eps / 2) hHalf
  refine Exists.intro (max N1 N2) (And.intro (hN1.trans (le_max_left _ _)) ?_)
  intro n hn
  have hn1 : N1 <= n := (le_max_left _ _).trans hn
  have hn2 : N2 <= n := (le_max_right _ _).trans hn
  have h := norm_add_le
    (hamiltonianUnweightedPrimeMatrix n - hamiltonianPrimeRealMatrix n)
    (hamiltonianPrimeRealMatrix n - hamiltonianRealConstantParityMatrix n)
  have hId : (hamiltonianUnweightedPrimeMatrix n - hamiltonianPrimeRealMatrix n) +
      (hamiltonianPrimeRealMatrix n - hamiltonianRealConstantParityMatrix n) =
        hamiltonianUnweightedPrimeMatrix n - hamiltonianRealConstantParityMatrix n := by abel
  rw [hId] at h
  have h1 := hError n hn1
  have h2 := hGap n hn2
  linarith only [h, h1, h2]

theorem hamiltonian_unweighted_prime_degree_uniform (eps : Real) (hEps : 0 < eps) :
    exists N0 : Nat, And (1 <= N0)
      (forall n : Nat, N0 <= n -> forall i : Fin n,
        abs (Finset.univ.sum (fun j => hamiltonianUnweightedPrimeMatrix n i j) - 1) <= eps) := by
  have hHalf : 0 < eps / 2 := by linarith only [hEps]
  choose D hD N1 hN1 hDegree using hamiltonian_prime_real_degree_uniform 1
  choose N2 hN2 hError using hamiltonian_prime_log_transfer_error_uniform (eps / 2) hHalf
  choose N3 hN3 hLog using hamiltonian_log_terminal_lower (2 * D / eps)
  let N0 := max N1 (max N2 N3)
  have hN0 : 1 <= N0 := by dsimp only [N0]; omega
  refine Exists.intro N0 (And.intro hN0 ?_)
  intro n hn i
  have hn1 : N1 <= n := by dsimp only [N0] at hn; omega
  have hn2 : N2 <= n := by dsimp only [N0] at hn; omega
  have hn3 : N3 <= n := by dsimp only [N0] at hn; omega
  have hBounds := hError n hn2
  have hDiff : abs (Finset.univ.sum (fun j => hamiltonianUnweightedPrimeMatrix n i j) -
      Finset.univ.sum (fun j => hamiltonianPrimeRealMatrix n i j)) <=
        hamiltonianPrimeLogTransferError n := by
    rw [<- Finset.sum_sub_distrib]
    exact (Finset.abs_sum_le_sum_abs _ _).trans
      (hamiltonian_unweighted_prime_row_transfer n (hN2.trans hn2) hBounds.1 i)
  have hDivide : D / Real.log (n : Real) <= eps / 2 := by
    calc
      _ <= D / (2 * D / eps) :=
        div_le_div_of_nonneg_left hD.le (div_pos (by positivity) hEps) (hLog n hn3)
      _ = eps / 2 := by field_simp [ne_of_gt hD, ne_of_gt hEps] <;> ring
  have hQ : abs (Finset.univ.sum (fun j => hamiltonianPrimeRealMatrix n i j) - 1) <= eps / 2 := by
    have hRaw : abs (Finset.univ.sum (fun j => hamiltonianPrimeRealMatrix n i j) - 1) <=
        D / Real.log (n : Real) := by
      simpa only [pow_one] using hDegree n hn1 i
    exact hRaw.trans hDivide
  have hTriangle := abs_sub_le
    (Finset.univ.sum (fun j => hamiltonianUnweightedPrimeMatrix n i j))
    (Finset.univ.sum (fun j => hamiltonianPrimeRealMatrix n i j)) 1
  linarith only [hTriangle, hDiff, hQ, hBounds.2]


theorem hamiltonian_unweighted_prime_degree_rate (m : Nat) :
    exists D : Real, And (0 < D)
      (exists N0 : Nat, And (256 <= N0)
        (forall n : Nat, N0 <= n -> forall i : Fin n,
          abs (Finset.univ.sum (fun j => hamiltonianUnweightedPrimeMatrix n i j) - 1) <=
            hamiltonianPrimeLogTransferError n + D / Real.log (n : Real) ^ m)) := by
  choose D hD N1 hN1 hDegree using hamiltonian_prime_real_degree_uniform m
  choose N2 hN2 hLog using hamiltonian_log_terminal_lower 64
  refine Exists.intro D (And.intro hD (Exists.intro (max N1 N2)
    (And.intro (hN1.trans (le_max_left _ _)) ?_)))
  intro n hn i
  have hn1 : N1 <= n := (le_max_left _ _).trans hn
  have hn2 : N2 <= n := (le_max_right _ _).trans hn
  have hnPos : 1 <= n := by omega
  have hDiff : abs (Finset.univ.sum (fun j => hamiltonianUnweightedPrimeMatrix n i j) -
      Finset.univ.sum (fun j => hamiltonianPrimeRealMatrix n i j)) <=
        hamiltonianPrimeLogTransferError n := by
    rw [<- Finset.sum_sub_distrib]
    exact (Finset.abs_sum_le_sum_abs _ _).trans
      (hamiltonian_unweighted_prime_row_transfer n hnPos (hLog n hn2) i)
  have hTriangle := abs_sub_le
    (Finset.univ.sum (fun j => hamiltonianUnweightedPrimeMatrix n i j))
    (Finset.univ.sum (fun j => hamiltonianPrimeRealMatrix n i j)) 1
  have hRaw := hDegree n hn1 i
  linarith only [hTriangle, hDiff, hRaw]

end PrimeFactorOscillations.LPF

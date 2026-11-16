/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.HamiltonianTotientSublog

/-! # Uniform native coprime endpoint-count parameter budgets

The existing unconditional totient bound discharges both retained
density domains. Explicit log-power domination supplies repair
smallness and the full half-mass comparison, with the positive
base-count cost and the complete avoidance allowance kept together.
-/

set_option autoImplicit false
set_option Elab.async false

noncomputable section

namespace PrimeFactorOscillations

theorem hamiltonian_half_deleted_rank_log (n : Nat) (hn : 16 <= n) :
    0 < (n - 2) / 2 /\
      Real.log (n : Real) <= 2 * Real.log (((n - 2) / 2 : Nat) : Real) := by
  let m := (n - 2) / 2
  have hm3 : 3 <= m := by dsimp only [m]; omega
  have hNle : n <= 2 * m + 3 := by dsimp only [m]; omega
  have hmR : (3 : Real) <= m := by exact_mod_cast hm3
  have hNleR : (n : Real) <= 2 * (m : Real) + 3 := by exact_mod_cast hNle
  have hProduct : 0 <= ((m : Real) - 3) * ((m : Real) + 1) :=
    mul_nonneg (sub_nonneg.mpr hmR) (by linarith only [hmR])
  have hSquare : (n : Real) <= (m : Real) ^ 2 := by
    nlinarith only [hProduct, hNleR]
  have hnPos : 0 < (n : Real) := by exact_mod_cast (show 0 < n by omega)
  have hLog := Real.log_le_log hnPos hSquare
  rw [Real.log_pow] at hLog
  refine And.intro (by dsimp only [m] at hm3; omega) ?_
  simpa only [Nat.cast_ofNat] using hLog

theorem hamiltonian_coprime_path_uniform_parameter_budget
    (beta gamma : Real) (hBeta : 0 < beta) (hGamma : 0 < gamma) :
    exists N0 : Nat, 512 <= N0 /\ forall n : Nat, N0 <= n ->
      let A := (n : Real) / (n.totient : Real)
      4 <= (n.totient : Real) /\
        4 * A ^ 2 <= beta * Real.log ((n - 2 : Nat) : Real) /\
        2 * A <= gamma * Real.log (((n - 2) / 2 : Nat) : Real) /\
        16 * A ^ 3 / (n : Real) <= 1 / 10000 /\
        1 + 170 * A + 64 * A * Real.log (2 * (n : Real)) +
          Real.log (8 * ((n - 2 : Nat) : Real)) <= (n : Real) / (4 * A ^ 2) := by
  let eta := min 1 (min (beta / 8) (gamma / 4))
  have hEta : 0 < eta := lt_min (by norm_num)
    (lt_min (div_pos hBeta (by norm_num)) (div_pos hGamma (by norm_num)))
  choose B hB hTotient using hamiltonian_totient_squared_sublogarithmic eta hEta
  choose C hC hCube using hamiltonian_log_power_dominated_uniform
    160000 (by norm_num) 3 1 (by norm_num)
  choose D hD hFourth using hamiltonian_log_power_dominated_uniform
    1000 (by norm_num) 4 1 (by norm_num)
  let N0 := max 512 (max B (max C D))
  refine Exists.intro N0 (And.intro (le_max_left _ _) ?_)
  intro n hn
  have hn512 : 512 <= n := (le_max_left _ _).trans hn
  have hnB : B <= n := by dsimp only [N0] at hn; omega
  have hnC : C <= n := by dsimp only [N0] at hn; omega
  have hnD : D <= n := by dsimp only [N0] at hn; omega
  let N : Real := n
  let A := (n : Real) / (n.totient : Real)
  let L := Real.log (2 * N)
  let m := (n - 2) / 2
  have hN512 : (512 : Real) <= N := by dsimp only [N]; exact_mod_cast hn512
  have hNPos : 0 < N := by linarith only [hN512]
  have hN1 : 1 <= N := by linarith only [hN512]
  have hPhiPos : 0 < (n.totient : Real) := by
    exact_mod_cast Nat.totient_pos.mpr (show 0 < n by omega)
  have hA1 : 1 <= A := hamiltonian_totient_ratio_ge_one n (by omega)
  have hA0 : 0 <= A := le_trans (by norm_num) hA1
  have hAPos : 0 < A := lt_of_lt_of_le (by norm_num) hA1
  have hASquare : A <= A ^ 2 := by nlinarith only [hA1, sq_nonneg (A - 1)]
  have hLogN0 : 0 <= Real.log N := Real.log_nonneg hN1
  have hLogNtoL : Real.log N <= L :=
    Real.log_le_log hNPos (by linarith only [hNPos])
  have hL1 : 1 <= L := by
    have hArg : Real.exp 1 < 2 * N :=
      Real.exp_one_lt_three.trans_le (by linarith only [hN512])
    exact ((Real.lt_log_iff_exp_lt (mul_pos (by norm_num) hNPos)).mpr hArg).le
  have hL0 : 0 <= L := le_trans (by norm_num) hL1
  have hSmall : A ^ 2 <= eta * Real.log N := hTotient n hnB
  have hEta1 : eta <= 1 := min_le_left _ _
  have hEtaBeta : eta <= beta / 8 := (min_le_right _ _).trans (min_le_left _ _)
  have hEtaGamma : eta <= gamma / 4 := (min_le_right _ _).trans (min_le_right _ _)
  have hEtaLog := mul_le_mul_of_nonneg_right hEta1 hLogN0
  have hALog : A <= Real.log N :=
    hASquare.trans (hSmall.trans (by simpa only [one_mul] using hEtaLog))
  have hAL : A <= L := hALog.trans hLogNtoL
  have hRank := hamiltonian_half_deleted_rank_log n (by omega)
  have hmPos : 0 < (m : Real) := by exact_mod_cast hRank.1
  have hDouble : Real.log N <= 2 * Real.log (m : Real) := hRank.2
  have hMle : m <= n - 2 := by dsimp only [m]; exact Nat.div_le_self _ _
  have hMleR : (m : Real) <= ((n - 2 : Nat) : Real) := by exact_mod_cast hMle
  have hFullLog : Real.log (m : Real) <= Real.log ((n - 2 : Nat) : Real) :=
    Real.log_le_log hmPos hMleR
  have hBetaScale := mul_le_mul_of_nonneg_right hEtaBeta hLogN0
  have hGammaScale := mul_le_mul_of_nonneg_right hEtaGamma hLogN0
  have hBetaDouble := mul_le_mul_of_nonneg_left hDouble
    (div_nonneg hBeta.le (by norm_num : (0 : Real) <= 2))
  have hGammaDouble := mul_le_mul_of_nonneg_left hDouble
    (div_nonneg hGamma.le (by norm_num : (0 : Real) <= 2))
  have hBetaFull := mul_le_mul_of_nonneg_left hFullLog hBeta.le
  have hDensityOdd : 4 * A ^ 2 <= beta * Real.log ((n - 2 : Nat) : Real) := by
    nlinarith only [hSmall, hBetaScale, hBetaDouble, hBetaFull]
  have hDensityEven : 2 * A <= gamma * Real.log (m : Real) := by
    nlinarith only [hASquare, hSmall, hGammaScale, hGammaDouble]
  have hNCube : 160000 * L ^ 3 <= N := by
    simpa only [Real.rpow_one] using hCube n hnC
  have hNFourth : 1000 * L ^ 4 <= N := by
    simpa only [Real.rpow_one] using hFourth n hnD
  have hASquareL : A ^ 2 <= L ^ 2 := by
    have h := mul_le_mul hAL hAL hA0 hL0
    nlinarith only [h]
  have hACubeL : A ^ 3 <= L ^ 3 := by
    have h := mul_le_mul hASquareL hAL hA0 (sq_nonneg L)
    nlinarith only [h]
  have hBigA : 160000 * A ^ 3 <= N :=
    (mul_le_mul_of_nonneg_left hACubeL (by norm_num)).trans hNCube
  have hRepair : 16 * A ^ 3 / N <= 1 / 10000 := by
    apply le_of_mul_le_mul_right _ hNPos
    have hClear : (16 * A ^ 3 / N) * N = 16 * A ^ 3 := by
      field_simp [ne_of_gt hNPos]
    rw [hClear]
    nlinarith only [hBigA]
  have hL2 : L <= L ^ 2 := by nlinarith only [hL1, sq_nonneg (L - 1)]
  have hL3 : L ^ 2 <= L ^ 3 := by
    have h := mul_le_mul_of_nonneg_left hL1 (sq_nonneg L)
    nlinarith only [h]
  have hFourA : 4 * A <= N := by
    nlinarith only [hNCube, hAL, hL2, hL3, pow_nonneg hL0 3]
  have hAPhi : A * (n.totient : Real) = N := by
    dsimp only [A, N]
    field_simp [ne_of_gt hPhiPos]
  have hPhi4 : 4 <= (n.totient : Real) := by
    apply le_of_mul_le_mul_left _ hAPos
    calc
      A * 4 = 4 * A := mul_comm _ _
      _ <= N := hFourA
      _ = A * (n.totient : Real) := hAPhi.symm
  have hAdd : ((n - 2 : Nat) : Real) + 2 = N := by
    dsimp only [N]
    exact_mod_cast Nat.sub_add_cancel (show 2 <= n by omega)
  have hSub : ((n - 2 : Nat) : Real) = N - 2 := by linarith only [hAdd]
  have hArgPos : 0 < 8 * ((n - 2 : Nat) : Real) := by
    rw [hSub]
    exact mul_pos (by norm_num) (by linarith only [hN512])
  have hArgBound : 8 * ((n - 2 : Nat) : Real) <= (2 * N) ^ 2 := by
    rw [hSub]
    nlinarith only [sq_nonneg (N - 1)]
  have hLogAllowance : Real.log (8 * ((n - 2 : Nat) : Real)) <= 2 * L := by
    have h := Real.log_le_log hArgPos hArgBound
    simpa only [Real.log_pow, Nat.cast_ofNat] using h
  have hALProduct := mul_le_mul_of_nonneg_right hAL hL0
  have hAllowance : 1 + 170 * A + 64 * A * L +
      Real.log (8 * ((n - 2 : Nat) : Real)) <= 240 * L ^ 2 := by
    nlinarith only [hLogAllowance, hAL, hALProduct, hL2, hL1, sq_nonneg L]
  have hSaving : 250 * L ^ 2 <= N / (4 * A ^ 2) := by
    have hSquareMult := mul_le_mul_of_nonneg_left hASquareL
      (mul_nonneg (by norm_num : (0 : Real) <= 1000) (sq_nonneg L))
    have hCross : (250 * L ^ 2) * (4 * A ^ 2) <= N := by
      nlinarith only [hSquareMult, hNFourth]
    have hDen : 0 < 4 * A ^ 2 := mul_pos (by norm_num) (sq_pos_of_pos hAPos)
    apply le_of_mul_le_mul_right _ hDen
    have hClear : (N / (4 * A ^ 2)) * (4 * A ^ 2) = N := by
      field_simp [ne_of_gt hAPos]
    rw [hClear]
    exact hCross
  have hFinal : 1 + 170 * A + 64 * A * L +
      Real.log (8 * ((n - 2 : Nat) : Real)) <= N / (4 * A ^ 2) := by
    have hOrder : 240 * L ^ 2 <= 250 * L ^ 2 := by nlinarith only [sq_nonneg L]
    exact hAllowance.trans (hOrder.trans hSaving)
  exact And.intro hPhi4 (And.intro hDensityOdd
    (And.intro hDensityEven (And.intro hRepair hFinal)))

end PrimeFactorOscillations

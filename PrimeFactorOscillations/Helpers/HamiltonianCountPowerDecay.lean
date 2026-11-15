/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.HamiltonianCycleLogEnvelope

/-! # Power decay from the complete actual count envelope

Every power below min(1,2-beta) is retained when amplification is
at most N^beta. The numerical3/5 endpoint is a specialization.
-/

set_option autoImplicit false
set_option Elab.async false

open scoped Matrix.Norms.L2Operator

noncomputable section

namespace PrimeFactorOscillations

theorem hamiltonian_log_power_dominated_uniform
    (C : Real) (hC : 0 < C) (H : Nat) (s : Real) (hs : 0 < s) :
    exists N0 : Nat, 256 <= N0 /\
      forall n : Nat, N0 <= n ->
        C * (Real.log (2 * (n : Real))) ^ H <= (n : Real) ^ s := by
  let D := C * (2 : Real) ^ H
  let eps := 1 / D
  have hD : 0 < D := mul_pos hC (pow_pos (by norm_num) H)
  have hEps : 0 < eps := div_pos (by norm_num) hD
  let range := Filter.eventually_atTop.mp
    ((_root_.isLittleO_log_rpow_rpow_atTop (s := s) (H : Real) hs).bound hEps)
  let x1 := range.choose
  let x0 := 256 + max 0 x1
  let N0 := max 256 (Nat.ceil x0)
  refine Exists.intro N0 (And.intro (le_max_left _ _) ?_)
  intro n hn
  have hn256 : (256 : Real) <= n := by exact_mod_cast le_trans (le_max_left 256 _) hn
  have hn0 : 0 < (n : Real) := by linarith only [hn256]
  have hnCeil : Nat.ceil x0 <= n := le_trans (le_max_right _ _) hn
  have hx : x0 <= (n : Real) := le_trans (Nat.le_ceil _) (by exact_mod_cast hnCeil)
  have hx1 : x1 <= (n : Real) := by
    have hMax := le_max_right (0 : Real) x1
    dsimp only [x0] at hx
    linarith only [hx, hMax]
  have hLog0 : 0 <= Real.log (n : Real) := Real.log_nonneg (by linarith only [hn256])
  have hLogDouble0 : 0 <= Real.log (2 * (n : Real)) :=
    Real.log_nonneg (by linarith only [hn256])
  have hLog2 : Real.log 2 <= Real.log (n : Real) :=
    Real.log_le_log (by norm_num) (by linarith only [hn256])
  have hSplit : Real.log (2 * (n : Real)) = Real.log 2 + Real.log (n : Real) :=
    Real.log_mul (by norm_num) (ne_of_gt hn0)
  have hDouble : Real.log (2 * (n : Real)) <= 2 * Real.log (n : Real) := by
    linarith only [hSplit, hLog2]
  have hPower := wick_nonnegative_power_le _ _ hLogDouble0 hDouble H
  rw [mul_pow] at hPower
  have hBound := range.choose_spec (n : Real) hx1
  simp only [Real.norm_eq_abs] at hBound
  rw [abs_of_nonneg (Real.rpow_nonneg hLog0 _),
    abs_of_nonneg (Real.rpow_nonneg (le_of_lt hn0) _)] at hBound
  have hCast : (Real.log (n : Real)) ^ (H : Real) = Real.log (n : Real) ^ H :=
    Real.rpow_natCast _ H
  rw [hCast] at hBound
  have hClear : D * eps = 1 := by dsimp only [eps]; field_simp [ne_of_gt hD]
  calc
    _ <= C * ((2 : Real) ^ H * Real.log (n : Real) ^ H) :=
      mul_le_mul_of_nonneg_left hPower (le_of_lt hC)
    _ = D * Real.log (n : Real) ^ H := by dsimp only [D]; ring
    _ <= D * (eps * (n : Real) ^ s) := mul_le_mul_of_nonneg_left hBound (le_of_lt hD)
    _ = _ := by rw [<- mul_assoc, hClear, one_mul]

theorem hamiltonian_count_power_decay_scalar
    (n X gamma beta t s : Real) (hn : 1 <= n)
    (hGamma : 0 <= gamma) (hGammaCap : gamma <= n ^ beta)
    (hX : 2 * X <= n ^ s) (hs1 : s - 1 <= -t) (hs2 : s + beta - 2 <= -t) :
    X / n + X * gamma / n ^ 2 <= n ^ (-t) := by
  have hn0 : 0 < n := lt_of_lt_of_le (by norm_num) hn
  have hHalf : X <= n ^ s / 2 := by linarith only [hX]
  have hHalf0 : 0 <= n ^ s / 2 := div_nonneg (Real.rpow_nonneg (le_of_lt hn0) _) (by norm_num)
  have hFirstPower : n ^ s = n ^ (s - 1) * n := by
    calc
      _ = n ^ ((s - 1) + 1) := by congr 1 <;> ring
      _ = _ := by rw [Real.rpow_add hn0, Real.rpow_one]
  have hSecondPower : n ^ (s + beta) = n ^ (s + beta - 2) * n ^ (2 : Nat) := by
    calc
      _ = n ^ ((s + beta - 2) + 2) := by congr 1 <;> ring
      _ = n ^ (s + beta - 2) * n ^ (2 : Real) := Real.rpow_add hn0 _ _
      _ = _ := congrArg (fun z : Real => n ^ (s + beta - 2) * z) (Real.rpow_natCast n 2)
  have hFirst : X / n <= n ^ (-t) / 2 := by
    calc
      _ <= (n ^ s / 2) / n := div_le_div_of_nonneg_right hHalf (le_of_lt hn0)
      _ = n ^ (s - 1) / 2 := by rw [hFirstPower]; field_simp [ne_of_gt hn0] <;> ring
      _ <= _ := div_le_div_of_nonneg_right (Real.rpow_le_rpow_of_exponent_le hn hs1) (by norm_num)
  have hSecond : X * gamma / n ^ 2 <= n ^ (-t) / 2 := by
    calc
      _ <= ((n ^ s / 2) * n ^ beta) / n ^ 2 :=
        div_le_div_of_nonneg_right (mul_le_mul hHalf hGammaCap hGamma hHalf0) (sq_nonneg n)
      _ = (n ^ s * n ^ beta) / n ^ 2 / 2 := by ring
      _ = n ^ (s + beta) / n ^ 2 / 2 := by rw [<- Real.rpow_add hn0]
      _ = n ^ (s + beta - 2) / 2 := by
        rw [hSecondPower]
        field_simp [ne_of_gt hn0]
        <;> ring
      _ <= _ := div_le_div_of_nonneg_right (Real.rpow_le_rpow_of_exponent_le hn hs2) (by norm_num)
  linarith only [hFirst, hSecond]

universe u

theorem stochastic_weighted_cycle_power_decay_uniform
    (delta c beta t : Real) (hDelta : 0 < delta) (hDelta1 : delta <= 1)
    (hc : 0 <= c) (ht : 0 < t) (ht1 : t < 1) (htBeta : t < 2 - beta) :
    exists N0 : Nat, 256 <= N0 /\
      forall (J : Type u) [Fintype J] [DecidableEq J] [Nonempty J],
        N0 <= Fintype.card J ->
        forall (T : Matrix J J Real) (q a : Real),
          (Fintype.card J : Real) * q = 1 -> 1 <= a ->
          a <= c * Real.log (2 * (Fintype.card J : Real)) ->
          (forall i, Finset.univ.sum (fun j => T i j) = 1) ->
          (forall j, Finset.univ.sum (fun i => T i j) = 1) ->
          (forall i j, 0 <= T i j) -> (forall i j, T i j <= a * q) ->
          norm (centeredKernel T q) <= 1 - delta ->
          hamiltonianGramAmplification T q <= (Fintype.card J : Real) ^ beta ->
          abs (hamiltonianBipartiteCountRatio T - 1) <= (Fintype.card J : Real) ^ (-t) := by
  let s := min (1 - t) (2 - beta - t) / 2
  have hMin : 0 < min (1 - t) (2 - beta - t) :=
    lt_min (by linarith only [ht1]) (by linarith only [htBeta])
  have hs : 0 < s := div_pos hMin (by norm_num)
  have hs1 : s - 1 <= -t := by
    have h := min_le_left (1 - t) (2 - beta - t)
    dsimp only [s]
    linarith only [h, hMin]
  have hs2 : s + beta - 2 <= -t := by
    have h := min_le_right (1 - t) (2 - beta - t)
    dsimp only [s]
    linarith only [h, hMin]
  have hRange := stochastic_weighted_cycle_log_envelope_uniform.{u} delta c hDelta hDelta1 hc
  refine hRange.elim ?_
  intro C hC
  have hC2 : 0 < 2 * C := mul_pos (by norm_num) hC.1
  have hScalarRange := hamiltonian_log_power_dominated_uniform
    (2 * C) hC2 hamiltonianCountLogExponent s hs
  refine hC.2.elim ?_
  intro NC hNC
  refine hScalarRange.elim ?_
  intro NL hNL
  let N0 := max NC NL
  refine Exists.intro N0 (And.intro (le_trans hNC.1 (le_max_left _ _)) ?_)
  intro J instF instD instN hn T q a hq ha hA hRow hCol hNonneg hUpper hNorm hAmpCap
  have hnC : NC <= Fintype.card J := le_trans (le_max_left _ _) hn
  have hnL : NL <= Fintype.card J := le_trans (le_max_right _ _) hn
  have hN256 : (256 : Real) <= Fintype.card J := by exact_mod_cast le_trans hNC.1 hnC
  have hN1 : (1 : Real) <= Fintype.card J := by linarith only [hN256]
  have hCount := hNC.2 J hnC T q a hq ha hA hRow hCol hNonneg hUpper hNorm
  have hLogPower := hNL.2 (Fintype.card J) hnL
  let X := C * (Real.log (2 * (Fintype.card J : Real))) ^ hamiltonianCountLogExponent
  have hX : 2 * X <= (Fintype.card J : Real) ^ s := by nlinarith only [hLogPower]
  have hRho0 : 0 <= 1 - delta := sub_nonneg.mpr hDelta1
  have hRho1 : 1 - delta < 1 := by linarith only [hDelta]
  have hAmp := stochastic_gram_amplification_upper T q a (1 - delta) hq
    hRow hNonneg hUpper hRho0 hRho1 hNorm
  exact le_trans hCount (hamiltonian_count_power_decay_scalar (Fintype.card J : Real)
    X (hamiltonianGramAmplification T q) beta t s hN1 (le_of_lt hAmp.1) hAmpCap hX hs1 hs2)

theorem stochastic_three_fifths_cycle_power_uniform :
    exists N0 : Nat, 256 <= N0 /\
      forall (J : Type u) [Fintype J] [DecidableEq J] [Nonempty J],
        N0 <= Fintype.card J ->
        forall (T : Matrix J J Real) (q a : Real),
          (Fintype.card J : Real) * q = 1 -> 1 <= a ->
          (forall i, Finset.univ.sum (fun j => T i j) = 1) ->
          (forall j, Finset.univ.sum (fun i => T i j) = 1) ->
          (forall i j, 0 <= T i j) -> (forall i j, T i j <= a * q) ->
          norm (centeredKernel T q) <= (3 / 5 : Real) ->
          a - 1 <= (3 / 5 : Real) * Real.log (Fintype.card J : Real) ->
          abs (hamiltonianBipartiteCountRatio T - 1) <=
            (Fintype.card J : Real) ^ (-3 / 5 : Real) := by
  have hRange := stochastic_weighted_cycle_power_decay_uniform.{u}
    (2 / 5) 2 (27 / 20) (3 / 5) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num)
  refine hRange.elim ?_
  intro NC hNC
  let N0 := max NC (Nat.ceil (Real.exp 1))
  refine Exists.intro N0 (And.intro (le_trans hNC.1 (le_max_left _ _)) ?_)
  intro J instF instD instN hn T q a hq ha hRow hCol hNonneg hUpper hNorm hCap
  have hnC : NC <= Fintype.card J := le_trans (le_max_left _ _) hn
  have hnCeil : Nat.ceil (Real.exp 1) <= Fintype.card J := le_trans (le_max_right _ _) hn
  have hN256 : (256 : Real) <= Fintype.card J := by exact_mod_cast le_trans hNC.1 hnC
  have hN1 : (1 : Real) <= Fintype.card J := by linarith only [hN256]
  have hN : 0 < (Fintype.card J : Real) := by linarith only [hN256]
  have hExp : Real.exp 1 <= (Fintype.card J : Real) :=
    le_trans (Nat.le_ceil _) (by exact_mod_cast hnCeil)
  have hLogN : 1 <= Real.log (Fintype.card J : Real) := by
    have h := Real.log_le_log (Real.exp_pos 1) hExp
    simpa only [Real.log_exp] using h
  have hLog2 : 0 <= Real.log 2 := Real.log_nonneg (by norm_num)
  have hSplit : Real.log (2 * (Fintype.card J : Real)) =
      Real.log 2 + Real.log (Fintype.card J : Real) :=
    Real.log_mul (by norm_num) (ne_of_gt hN)
  have hA : a <= 2 * Real.log (2 * (Fintype.card J : Real)) := by
    linarith only [hCap, hLogN, hLog2, hSplit]
  have hAmp := stochastic_three_fifths_amplification_power T q a
    (Fintype.card J : Real) hq hRow hNonneg hUpper hNorm hN1 hCap
  have hNormDelta : norm (centeredKernel T q) <= 1 - (2 / 5 : Real) := by
    norm_num
    exact hNorm
  simpa only [neg_div] using hNC.2 J hnC T q a hq ha hA hRow hCol hNonneg hUpper hNormDelta hAmp

end PrimeFactorOscillations

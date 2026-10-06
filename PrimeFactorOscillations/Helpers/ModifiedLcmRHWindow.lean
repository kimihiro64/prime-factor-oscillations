/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.LcmNormalizedComparison
import PrimeFactorOscillations.Helpers.NicolasNegativeLimit

/-!
# The actual modified-LCM critical window under RH

The normalized lower budget uses the proved Nicolas upper envelope.
Its complete signed limit retains the positive tail and every leading loss.
-/

set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace PrimeFactorOscillations

open Filter Robin1984

def lcmRHWindowBudget (N : Nat) : Real :=
  lcmFiniteTailLowerSum N 1000000 ((1001 / 1000 : Real) ^ 2)
      (lcmMovingExponent (2 / 5) N) * Real.sqrt (N : Real) * Real.log (N : Real) -
    lcmMovingExponent (2 / 5) N *
      max (nicolasRHUpperEnvelope (N : Real) * Real.sqrt (N : Real) * Real.log (N : Real) +
        modifiedLcmHeightCorrection N * Real.sqrt (N : Real) * Real.log (N : Real) +
        lcmDefectSum (modifiedLcm N) * Real.sqrt (N : Real) * Real.log (N : Real)) 0 -
    lcmDefectRemainder (modifiedLcm N) * Real.sqrt (N : Real) * Real.log (N : Real)

def lcmRHWindowLimit : Real :=
  lcmFiniteTailCoefficient ((1001 / 1000 : Real) ^ 2) 1000000 *
      Real.exp (-(2 / 5 : Real)) -
    (3 / 2 : Real) *
      max ((Real.eulerMascheroniConstant + 2 - Real.log (4 * Real.pi) - 2) +
        Real.sqrt 2 + Real.sqrt 2) 0

theorem tendsto_lcmRHWindowBudget :
    Tendsto lcmRHWindowBudget atTop (nhds lcmRHWindowLimit) := by
  have hEnv : Tendsto (fun N : Nat =>
      nicolasRHUpperEnvelope (N : Real) * Real.sqrt (N : Real) * Real.log (N : Real))
      atTop (nhds (Real.eulerMascheroniConstant + 2 - Real.log (4 * Real.pi) - 2)) := by
    simpa only [Function.comp_def, Real.sqrt_eq_rpow, mul_assoc] using
      tendsto_nicolasRHUpperEnvelope_scaled.comp
        (tendsto_natCast_atTop_atTop :
          Tendsto (fun N : Nat => (N : Real)) atTop atTop)
  have hA := (hEnv.add tendsto_modifiedLcm_heightCorrection_scaled).add
    tendsto_modifiedLcm_defect_scaled
  have hMax := hA.max (tendsto_const_nhds (x := (0 : Real)))
  have hLoss := (tendsto_lcmMovingExponent (2 / 5)).mul hMax
  have hTail := tendsto_lcmFiniteTailLowerSum_scaled
    ((1001 / 1000 : Real) ^ 2) (2 / 5) (by norm_num) 1000000
  change Tendsto (fun N : Nat => lcmRHWindowBudget N) atTop (nhds lcmRHWindowLimit)
  simpa only [lcmRHWindowBudget, lcmRHWindowLimit, sub_zero] using
    (hTail.sub hLoss).sub tendsto_modifiedLcm_remainder_scaled

theorem lcmRHWindowLimit_gt :
    (7 / 600 : Real) < lcmRHWindowLimit := by
  have hMargin := lcmFiniteTailCoefficient_explicit_margin (1 / 20) le_rfl
  have hRoot : (1 : Real) <= Real.sqrt 2 := by
    nlinarith only [Real.sq_sqrt (by norm_num : (0 : Real) <= 2),
      Real.sqrt_nonneg (2 : Real)]
  have hMax :
      max ((Real.eulerMascheroniConstant + 2 - Real.log (4 * Real.pi) - 2) +
        Real.sqrt 2 + Real.sqrt 2) 0 <= 2 * Real.sqrt 2 - 2 + 1 / 20 := by
    apply max_le
    . linarith only [robin_zero_constant_le_one_twentieth]
    . linarith only [hRoot]
  have hLoss := mul_le_mul_of_nonneg_left hMax
    (by norm_num : (0 : Real) <= 3 / 2)
  unfold lcmRHWindowLimit
  generalize hCoeffEq :
    lcmFiniteTailCoefficient ((1001 / 1000 : Real) ^ 2) 1000000 = coeff at *
  linarith only [hMargin, hLoss]

theorem lcmRHWindowBudget_le_scaled_logRatio
    (N : Nat) (hN : 8 <= N)
    (hBound : nicolasLogMertensOscillation (N : Real) <= nicolasRHUpperEnvelope (N : Real) \/
      nicolasLogMertensOscillation (N : Real) + modifiedLcmHeightCorrection N +
        lcmDefectSum (modifiedLcm N) <= 0)
    (k : Real) (hk : 1 < k) (hLe : k <= lcmMovingExponent (2 / 5) N)
    (hTwo : lcmMovingExponent (2 / 5) N <= 2) :
    lcmRHWindowBudget N <=
      Real.log (lcmRobinRatio k (zero_lt_one.trans hk) (modifiedLcm N)) *
        Real.sqrt (N : Real) * Real.log (N : Real) := by
  let S := Real.sqrt (N : Real) * Real.log (N : Real)
  let K := lcmMovingExponent (2 / 5) N
  let L := lcmFiniteTailLowerSum N 1000000 ((1001 / 1000 : Real) ^ 2) K
  let R := lcmDefectRemainder (modifiedLcm N)
  let A := nicolasLogMertensOscillation (N : Real) +
    modifiedLcmHeightCorrection N + lcmDefectSum (modifiedLcm N)
  let B := nicolasRHUpperEnvelope (N : Real) * Real.sqrt (N : Real) * Real.log (N : Real) +
    modifiedLcmHeightCorrection N * Real.sqrt (N : Real) * Real.log (N : Real) +
    lcmDefectSum (modifiedLcm N) * Real.sqrt (N : Real) * Real.log (N : Real)
  have hNat : (1 : Real) < N := by exact_mod_cast (show 1 < N by omega)
  have hS : 0 < S :=
    mul_pos (Real.sqrt_pos.2 (zero_lt_one.trans hNat)) (Real.log_pos hNat)
  have hK : 0 <= K := (zero_lt_one.trans (hk.trans_le hLe)).le
  have hAS : A * S <= max B 0 := by
    rcases hBound with hEnv | hNegative
    . have hEnvS := mul_le_mul_of_nonneg_right hEnv hS.le
      have hAB : A * S <= B := by
        dsimp only [A, B, S] at *
        nlinarith only [hEnvS]
      exact hAB.trans (le_max_left B 0)
    . exact (mul_nonpos_of_nonpos_of_nonneg hNegative hS.le).trans (le_max_right B 0)
  have hMaxScale : max A 0 * S = max (A * S) 0 := by
    by_cases hA : 0 <= A
    . rw [max_eq_left hA, max_eq_left (mul_nonneg hA hS.le)]
    . have hA' : A <= 0 := (lt_of_not_ge hA).le
      rw [max_eq_right hA',
        max_eq_right (mul_nonpos_of_nonpos_of_nonneg hA' hS.le), zero_mul]
  have hComparison := mul_le_mul_of_nonneg_left
    (max_le hAS (le_max_right B 0)) hK
  have hFinite := modifiedLcm_logRatio_finite_window_lower k K
    ((1001 / 1000 : Real) ^ 2) (zero_lt_one.trans hk) hk hLe hTwo
    (by norm_num) N 1000000 hN
  have hFiniteS := mul_le_mul_of_nonneg_right hFinite hS.le
  change (L - K * max A 0 - R) * S <=
    Real.log (lcmRobinRatio k (zero_lt_one.trans hk) (modifiedLcm N)) * S at hFiniteS
  have hAlgebra : (L - K * max A 0 - R) * S =
      L * S - K * max (A * S) 0 - R * S := by
    rw [show (L - K * max A 0 - R) * S =
      L * S - K * (max A 0 * S) - R * S by ring, hMaxScale]
  rw [hAlgebra] at hFiniteS
  calc
    lcmRHWindowBudget N = L * S - K * max B 0 - R * S := by
      dsimp only [lcmRHWindowBudget, L, S, K, B, R]
      ring
    _ <= L * S - K * max (A * S) 0 - R * S := by
      linarith only [hComparison]
    _ <= Real.log (lcmRobinRatio k (zero_lt_one.trans hk) (modifiedLcm N)) * S :=
      hFiniteS
    _ = _ := by dsimp only [S]; ring

theorem eventually_modifiedLcm_window_scaled_of_RH (hRH : RiemannHypothesis) :
    Filter.Eventually (fun N : Nat => forall k : Real, forall hk : 1 < k,
      k <= lcmMovingExponent (2 / 5) N ->
        (1 / 100 : Real) <
          Real.log (lcmRobinRatio k (zero_lt_one.trans hk) (modifiedLcm N)) *
            Real.sqrt (N : Real) * Real.log (N : Real)) atTop := by
  have hLimit : (1 / 100 : Real) < lcmRHWindowLimit := by
    linarith only [lcmRHWindowLimit_gt]
  have hBudget := tendsto_lcmRHWindowBudget.eventually_const_lt hLimit
  have hTwo := (tendsto_lcmMovingExponent (2 / 5)).eventually_lt_const
    (by norm_num : (3 / 2 : Real) < 2)
  filter_upwards [hBudget, hTwo, eventually_ge_atTop (8 : Nat)] with N hB hK hN
  intro k hk hLe
  have hEnv := nicolasLog_le_RH_upper_envelope hRH
    (show (4 : Real) <= N by exact_mod_cast (show 4 <= N by omega))
  exact hB.trans_le
    (lcmRHWindowBudget_le_scaled_logRatio N hN (Or.inl hEnv) k hk hLe hK.le)

theorem eventually_modifiedLcm_window_of_RH (hRH : RiemannHypothesis) :
    Filter.Eventually (fun N : Nat => forall k : Real, forall hk : 1 < k,
      k <= lcmMovingExponent (2 / 5) N ->
        1 / (100 * Real.sqrt (N : Real) * Real.log (N : Real)) <
          Real.log (lcmRobinRatio k (zero_lt_one.trans hk) (modifiedLcm N))) atTop := by
  filter_upwards [eventually_modifiedLcm_window_scaled_of_RH hRH,
    eventually_ge_atTop (8 : Nat)] with N hWindow hN
  intro k hk hLe
  have hNat : (1 : Real) < N := by exact_mod_cast (show 1 < N by omega)
  have hS : 0 < Real.sqrt (N : Real) * Real.log (N : Real) :=
    mul_pos (Real.sqrt_pos.2 (zero_lt_one.trans hNat)) (Real.log_pos hNat)
  have hRoot := Real.sqrt_pos.2 (zero_lt_one.trans hNat)
  have hLog := Real.log_pos hNat
  have hCancel :
      (1 / (100 * Real.sqrt (N : Real) * Real.log (N : Real))) *
        (Real.sqrt (N : Real) * Real.log (N : Real)) = (1 / 100 : Real) := by
    field_simp [hRoot.ne', hLog.ne']
  by_contra hNot
  have hUpper := mul_le_mul_of_nonneg_right (le_of_not_gt hNot) hS.le
  rw [hCancel] at hUpper
  have hScaled := hWindow k hk hLe
  rw [mul_assoc] at hScaled
  exact (not_lt_of_ge hUpper) hScaled

end PrimeFactorOscillations

/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.LcmStripCorrections
import PrimeFactorOscillations.Helpers.LcmStripMargin
import PrimeFactorOscillations.Helpers.NicolasStripAsymptotic

/-!
# Modified-LCM windows from a zero-free strip

The complete signed lower bound is normalized by N^(1-b) log N, retaining
the finite prime tail, the maximum with zero, and all arithmetic corrections.
For fixed 1/2 < b < 1, a positive limiting budget gives a uniform eventual
window in the divisor exponent.

At b=7/8 the explicit twenty-four-block margin gives the lower bound
1/(200 N^(1/8) log N), throughout 1 < k <= 9/8 + 4/log(log(M_N)).
The zero-free hypothesis is explicit in every theorem that needs it.
No unconditional seven-eighths theorem is asserted in this module.
-/

set_option autoImplicit false
set_option Elab.async false

noncomputable section
namespace PrimeFactorOscillations
open Filter Robin1984

def lcmStripSpectralConstant (b : Real) : Real :=
  (Real.eulerMascheroniConstant + 2 - Real.log (4 * Real.pi)) /
    (2 * Real.sqrt (b * (1 - b)))

def lcmStripWindowBudget (b c q : Real) (m N : Nat) : Real :=
  lcmFiniteTailLowerSum N m q (lcmStripMovingExponent b c N) *
      (N : Real) ^ (1 - b) * Real.log (N : Real) -
    lcmStripMovingExponent b c N *
      max (lcmStripSpectralConstant b + nicolasStripNormalizedError b (N : Real) +
        modifiedLcmHeightCorrection N * (N : Real) ^ (1 - b) * Real.log (N : Real) +
        lcmDefectSum (modifiedLcm N) * (N : Real) ^ (1 - b) * Real.log (N : Real)) 0 -
    lcmDefectRemainder (modifiedLcm N) * (N : Real) ^ (1 - b) * Real.log (N : Real)

def lcmStripWindowLimit (b c q : Real) (m : Nat) : Real :=
  lcmStripFiniteTailCoefficient b q m * Real.exp (-c) -
    (2 - b) * max (lcmStripSpectralConstant b) 0

theorem tendsto_lcmStripWindowBudget
    (b c q : Real) (m : Nat) (hb : 1 / 2 < b) (hq : 0 < q) :
    Tendsto (lcmStripWindowBudget b c q m) atTop
      (nhds (lcmStripWindowLimit b c q m)) := by
  have hb0 : 0 < b := by linarith
  have hE := (tendsto_nicolasStripNormalizedError hb0).comp
    (tendsto_natCast_atTop_atTop :
      Tendsto (fun N : Nat => (N : Real)) atTop atTop)
  have hA := (((tendsto_const_nhds (x := lcmStripSpectralConstant b)).add hE).add
    (tendsto_modifiedLcm_heightCorrection_strip_scaled b hb)).add
      (tendsto_modifiedLcm_defect_strip_scaled b hb)
  have hMax := hA.max (tendsto_const_nhds (x := (0 : Real)))
  have hLoss := (tendsto_lcmStripMovingExponent b c).mul hMax
  have hTail := tendsto_lcmStripFiniteTailLowerSum_scaled b q c hq m
  change Tendsto (fun N : Nat => lcmStripWindowBudget b c q m N)
    atTop (nhds (lcmStripWindowLimit b c q m))
  simpa only [lcmStripWindowBudget, lcmStripWindowLimit, Function.comp_def,
    add_zero, sub_zero] using
    (hTail.sub hLoss).sub (tendsto_modifiedLcm_remainder_strip_scaled b hb)

theorem lcmStripWindowBudget_le_scaled_logRatio
    (b c q : Real) (m N : Nat) (hN : 8 <= N) (hq : 1 <= q)
    (hBound : ((N : Real) ^ (1 - b) * Real.log (N : Real)) *
      nicolasLogMertensOscillation (N : Real) <=
        lcmStripSpectralConstant b + nicolasStripNormalizedError b (N : Real))
    (k : Real) (hk : 1 < k) (hLe : k <= lcmStripMovingExponent b c N)
    (hTwo : lcmStripMovingExponent b c N <= 2) :
    lcmStripWindowBudget b c q m N <=
      Real.log (lcmRobinRatio k (zero_lt_one.trans hk) (modifiedLcm N)) *
        (N : Real) ^ (1 - b) * Real.log (N : Real) := by
  let S := (N : Real) ^ (1 - b) * Real.log (N : Real)
  let K := lcmStripMovingExponent b c N
  let L := lcmFiniteTailLowerSum N m q K
  let R := lcmDefectRemainder (modifiedLcm N)
  let A := nicolasLogMertensOscillation (N : Real) +
    modifiedLcmHeightCorrection N + lcmDefectSum (modifiedLcm N)
  let B := lcmStripSpectralConstant b + nicolasStripNormalizedError b (N : Real) +
    modifiedLcmHeightCorrection N * S + lcmDefectSum (modifiedLcm N) * S
  have hNat : (1 : Real) < N := by exact_mod_cast (show 1 < N by omega)
  have hS : 0 < S :=
    mul_pos (Real.rpow_pos_of_pos (zero_lt_one.trans hNat) _) (Real.log_pos hNat)
  have hK : 0 <= K := (zero_lt_one.trans (hk.trans_le hLe)).le
  have hAS : A * S <= B := by
    dsimp only [A, B, S]
    nlinarith only [hBound]
  have hMaxScale : max A 0 * S = max (A * S) 0 := by
    by_cases hA : 0 <= A
    . rw [max_eq_left hA, max_eq_left (mul_nonneg hA hS.le)]
    . have hA' : A <= 0 := (lt_of_not_ge hA).le
      rw [max_eq_right hA',
        max_eq_right (mul_nonpos_of_nonpos_of_nonneg hA' hS.le), zero_mul]
  have hComparison := mul_le_mul_of_nonneg_left
    (max_le_max hAS (le_refl (0 : Real))) hK
  have hFinite := modifiedLcm_logRatio_finite_window_lower k K q
    (zero_lt_one.trans hk) hk hLe hTwo hq N m hN
  have hFiniteS := mul_le_mul_of_nonneg_right hFinite hS.le
  change (L - K * max A 0 - R) * S <=
    Real.log (lcmRobinRatio k (zero_lt_one.trans hk) (modifiedLcm N)) * S at hFiniteS
  have hAlgebra : (L - K * max A 0 - R) * S =
      L * S - K * max (A * S) 0 - R * S := by
    rw [show (L - K * max A 0 - R) * S =
      L * S - K * (max A 0 * S) - R * S by ring, hMaxScale]
  rw [hAlgebra] at hFiniteS
  calc
    lcmStripWindowBudget b c q m N = L * S - K * max B 0 - R * S := by
      dsimp only [lcmStripWindowBudget, L, S, K, B, R]
      ring
    _ <= L * S - K * max (A * S) 0 - R * S := by
      linarith only [hComparison]
    _ <= Real.log (lcmRobinRatio k (zero_lt_one.trans hk) (modifiedLcm N)) * S :=
      hFiniteS
    _ = _ := by dsimp only [S]; ring

theorem eventually_modifiedLcm_strip_window_scaled
    (b c q delta : Real) (m : Nat) (hb : 1 / 2 < b) (hbOne : b < 1)
    (hq : 1 <= q)
    (hZeroFree : forall s : Complex, b < s.re -> Not (s = 1) ->
      Not (riemannZeta s = 0))
    (hMargin : delta < lcmStripWindowLimit b c q m) :
    Filter.Eventually (fun N : Nat => forall k : Real, forall hk : 1 < k,
      k <= lcmStripMovingExponent b c N ->
        delta < Real.log (lcmRobinRatio k (zero_lt_one.trans hk) (modifiedLcm N)) *
          (N : Real) ^ (1 - b) * Real.log (N : Real)) atTop := by
  have hb0 : 0 < b := by linarith
  have hBudget := (tendsto_lcmStripWindowBudget b c q m hb
    (zero_lt_one.trans_le hq)).eventually_const_lt hMargin
  have hTwo := (tendsto_lcmStripMovingExponent b c).eventually_lt_const
    (show 2 - b < 2 by linarith)
  filter_upwards [hBudget, hTwo, eventually_ge_atTop (8 : Nat)] with N hB hK hN
  intro k hk hLe
  have hBound := nicolasLog_scaled_strip_bound hb0 hbOne hZeroFree
    (show (3 : Real) <= N by exact_mod_cast (show 3 <= N by omega))
  exact hB.trans_le
    (lcmStripWindowBudget_le_scaled_logRatio b c q m N hN hq hBound k hk hLe hK.le)

theorem lcmStripWindowLimit_seven_eighths_gt :
    (1 / 200 : Real) <
      lcmStripWindowLimit (7 / 8) 4 ((12 / 11 : Real) ^ 8) 24 := by
  let beta := Real.eulerMascheroniConstant + 2 - Real.log (4 * Real.pi)
  have hLoss := lcmStrip_seven_eighths_loss_lt beta
    robin_zero_constant_le_one_twentieth
  have hRoot : Real.sqrt ((7 / 8 : Real) * (1 - 7 / 8)) = Real.sqrt 7 / 8 := by
    have h64 : Real.sqrt (64 : Real) = 8 := by
      rw [show (64 : Real) = 8 ^ 2 by norm_num,
        Real.sqrt_sq (by norm_num : (0 : Real) <= 8)]
    rw [show (7 / 8 : Real) * (1 - 7 / 8) = 7 / 64 by norm_num,
      Real.sqrt_div (by norm_num : (0 : Real) <= 7), h64]
  have hCoeff : (9 / 8 : Real) * lcmStripSpectralConstant (7 / 8) =
      9 * beta / (2 * Real.sqrt 7) := by
    unfold lcmStripSpectralConstant
    rw [hRoot]
    dsimp only [beta]
    ring
  have hMaxLoss : (9 / 8 : Real) * max (lcmStripSpectralConstant (7 / 8)) 0 <
      (3 / 35 : Real) := by
    by_cases h : 0 <= lcmStripSpectralConstant (7 / 8)
    . rw [max_eq_left h, hCoeff]
      exact hLoss
    . rw [max_eq_right (le_of_not_ge h), mul_zero]
      norm_num
  have hMargin := lcmStrip_seven_eighths_explicit_margin
  unfold lcmStripWindowLimit
  rw [show (2 : Real) - 7 / 8 = 9 / 8 by norm_num]
  linarith only [hMargin, hMaxLoss]

theorem eventually_modifiedLcm_seven_eighths_window_scaled
    (hZeroFree : forall s : Complex, (7 / 8 : Real) < s.re -> Not (s = 1) ->
      Not (riemannZeta s = 0)) :
    Filter.Eventually (fun N : Nat => forall k : Real, forall hk : 1 < k,
      k <= lcmStripMovingExponent (7 / 8) 4 N ->
        (1 / 200 : Real) <
          Real.log (lcmRobinRatio k (zero_lt_one.trans hk) (modifiedLcm N)) *
            (N : Real) ^ (1 / 8 : Real) * Real.log (N : Real)) atTop := by
  have h := eventually_modifiedLcm_strip_window_scaled
    (7 / 8) 4 ((12 / 11 : Real) ^ 8) (1 / 200) 24
    (by norm_num) (by norm_num) (by norm_num) hZeroFree
    lcmStripWindowLimit_seven_eighths_gt
  norm_num only [show (1 : Real) - 7 / 8 = 1 / 8 by norm_num] at h
  exact h

theorem eventually_modifiedLcm_seven_eighths_window
    (hZeroFree : forall s : Complex, (7 / 8 : Real) < s.re -> Not (s = 1) ->
      Not (riemannZeta s = 0)) :
    Filter.Eventually (fun N : Nat => forall k : Real, forall hk : 1 < k,
      k <= lcmStripMovingExponent (7 / 8) 4 N ->
        1 / (200 * (N : Real) ^ (1 / 8 : Real) * Real.log (N : Real)) <
          Real.log (lcmRobinRatio k (zero_lt_one.trans hk) (modifiedLcm N))) atTop := by
  filter_upwards [eventually_modifiedLcm_seven_eighths_window_scaled hZeroFree,
    eventually_ge_atTop (8 : Nat)] with N hWindow hN
  intro k hk hLe
  have hNat : (1 : Real) < N := by exact_mod_cast (show 1 < N by omega)
  have hPow : 0 < (N : Real) ^ (1 / 8 : Real) :=
    Real.rpow_pos_of_pos (zero_lt_one.trans hNat) _
  have hLog := Real.log_pos hNat
  have hS : 0 < (N : Real) ^ (1 / 8 : Real) * Real.log (N : Real) :=
    mul_pos hPow hLog
  have hCancel :
      (1 / (200 * (N : Real) ^ (1 / 8 : Real) * Real.log (N : Real))) *
        ((N : Real) ^ (1 / 8 : Real) * Real.log (N : Real)) = (1 / 200 : Real) := by
    field_simp [hPow.ne', hLog.ne']
  by_contra hNot
  have hUpper := mul_le_mul_of_nonneg_right (le_of_not_gt hNot) hS.le
  rw [hCancel] at hUpper
  have hScaled := hWindow k hk hLe
  rw [mul_assoc] at hScaled
  exact (not_lt_of_ge hUpper) hScaled

end PrimeFactorOscillations

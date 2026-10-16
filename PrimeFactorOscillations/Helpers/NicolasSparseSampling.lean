/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/

import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import PrimeFactorOscillations.Helpers.NicolasLogSpectral
import PrimeFactorOscillations.Helpers.NicolasPowerPersistence
import PrimeFactorOscillations.Helpers.QuadraticProfileRH
import PrimeFactorOscillations.Mathlib.Analysis.SpecialFunctions.Pow.Sampling

/-!
# Sparse detection of the Nicolas oscillation

Subpower meshes preserve arbitrarily large off-RH excursions and the RH comparison criterion.
-/

set_option autoImplicit false
set_option Elab.async false

open Filter
open scoped Topology

namespace PrimeFactorOscillations

open Robin1984

/-- False RH has arbitrarily large normalized positive excursions on every
strict mesh with subpower gap exponent three quarters. -/
theorem nicolasLog_unbounded_on_subpower_mesh_of_not_RH
    (u : Nat -> Nat) (hu : StrictMono u)
    (hmesh : Nat.SubpowerGapBound u (3 / 4))
    (hNotRH : Not RiemannHypothesis) (A X : Real) :
    exists j : Nat, X < (u j : Real) /\
      A < (u j : Real) ^ (1 / 2 : Real) * Real.log (u j : Real) *
        nicolasLogMertensOscillation (u j : Real) := by
  choose b hb hbHalf hIntervals using
    exists_nicolasLog_power_intervals_of_not_RH hNotRH
  let d : Real := ((3 / 4) + (1 - b / 2)) / 2
  have hdLow : (3 / 4 : Real) < d := by dsimp [d]; linarith
  have hdHigh : d < 1 - b / 2 := by dsimp [d]; linarith
  have hSample := Nat.eventually_exists_sample_mem_power_window
    u hu (3 / 4) d (by norm_num) hdLow hmesh
  have hGrowth : Filter.Eventually
      (fun x : Real => A < x ^ (1 / 2 - b)) atTop :=
    (tendsto_rpow_atTop (by linarith : 0 < (1 / 2 : Real) - b)).eventually_gt_atTop A
  have hLate : Filter.Eventually (fun x : Real =>
      (exists j : Nat, x <= (u j : Real) /\ (u j : Real) <= x + x ^ d) /\
        A < x ^ (1 / 2 - b) /\ Real.exp 1 <= x /\ 0 < x) atTop := by
    filter_upwards [hSample, hGrowth, eventually_ge_atTop (Real.exp 1),
      eventually_gt_atTop (0 : Real)] with x hs hg he hx
    exact And.intro hs (And.intro hg (And.intro he hx))
  choose Y hY using eventually_atTop.1 hLate
  choose n hn hnSix hWindow using hIntervals d 1 (max X Y) hdHigh (by norm_num)
  have hnY : Y <= (n : Real) := le_trans (le_max_right X Y) (le_of_lt hn)
  have hnX : X < (n : Real) := lt_of_le_of_lt (le_max_left X Y) hn
  have hData := hY (n : Real) hnY
  choose j hjLow hjHigh using hData.1
  have hF : (n : Real) ^ (-b) < nicolasLogMertensOscillation (u j : Real) := by
    simpa only [one_mul] using hWindow (u j : Real) hjLow hjHigh
  have hnPos : (0 : Real) < n := hData.2.2.2
  have hFPos : 0 < nicolasLogMertensOscillation (u j : Real) :=
    lt_trans (Real.rpow_pos_of_pos hnPos _) hF
  have hPow : (n : Real) ^ (1 / 2 : Real) <= (u j : Real) ^ (1 / 2 : Real) :=
    Real.rpow_le_rpow hnPos.le hjLow (by norm_num)
  have hLog : 1 <= Real.log (u j : Real) := by
    have h := Real.log_le_log (Real.exp_pos 1) (hData.2.2.1.trans hjLow)
    simpa only [Real.log_exp] using h
  refine Exists.intro j (And.intro (lt_of_lt_of_le hnX hjLow) ?_)
  calc
    A < (n : Real) ^ (1 / 2 - b) := hData.2.1
    _ = (n : Real) ^ (1 / 2 : Real) * (n : Real) ^ (-b) := by
      rw [<- Real.rpow_add hnPos]
      congr 1
    _ < (n : Real) ^ (1 / 2 : Real) *
        nicolasLogMertensOscillation (u j : Real) :=
      mul_lt_mul_of_pos_left hF (Real.rpow_pos_of_pos hnPos _)
    _ <= (u j : Real) ^ (1 / 2 : Real) *
        nicolasLogMertensOscillation (u j : Real) :=
      mul_le_mul_of_nonneg_right hPow hFPos.le
    _ <= (u j : Real) ^ (1 / 2 : Real) * Real.log (u j : Real) *
        nicolasLogMertensOscillation (u j : Real) := by
      have h := mul_le_mul_of_nonneg_left hLog
        (mul_nonneg (Real.rpow_nonneg (Nat.cast_nonneg (u j)) (1 / 2 : Real)) hFPos.le)
      convert h using 1 <;> ring

/-- The normalized Nicolas signal has the complete zero wave as its main term. -/
theorem eventually_nicolasLog_normalized_wave_error (hRH : RiemannHypothesis) :
    Filter.Eventually (fun x : Real =>
      abs (x ^ (1 / 2 : Real) * Real.log x * nicolasLogMertensOscillation x +
        2 + nicolasZeroWave x) <= nicolasLogSpectralConstant / Real.log x) atTop := by
  filter_upwards [eventually_nicolasLog_wave_uniform_error hRH,
      eventually_gt_atTop (1 : Real)] with x he hx
  have hxPos : 0 < x := zero_lt_one.trans hx
  have hRoot := Real.rpow_pos_of_pos hxPos (1 / 2 : Real)
  have hLog := Real.log_pos hx
  let S := x ^ (1 / 2 : Real) * Real.log x
  have hS : 0 < S := mul_pos hRoot hLog
  calc
    abs (x ^ (1 / 2 : Real) * Real.log x * nicolasLogMertensOscillation x +
        2 + nicolasZeroWave x) =
        S * abs (nicolasLogMertensOscillation x + (2 + nicolasZeroWave x) / S) := by
      have hid : x ^ (1 / 2 : Real) * Real.log x * nicolasLogMertensOscillation x +
          2 + nicolasZeroWave x =
          S * (nicolasLogMertensOscillation x + (2 + nicolasZeroWave x) / S) := by
        dsimp [S]
        field_simp [hRoot.ne', hLog.ne'] <;> ring
      rw [hid, abs_mul, abs_of_pos hS]
    _ <= S * (nicolasLogSpectralConstant * x ^ (-(1 / 2 : Real)) *
        Inv.inv ((Real.log x) ^ 2)) :=
      mul_le_mul_of_nonneg_left he hS.le
    _ = nicolasLogSpectralConstant / Real.log x := by
      dsimp [S]
      rw [Real.rpow_neg hxPos.le]
      field_simp [hRoot.ne', hLog.ne'] <;> ring

theorem exists_eventually_nicolasLog_normalized_le_of_RH (hRH : RiemannHypothesis) :
    exists C : Real, Filter.Eventually (fun x : Real =>
      x ^ (1 / 2 : Real) * Real.log x * nicolasLogMertensOscillation x <= C) atTop := by
  let beta := Real.eulerMascheroniConstant + 2 - Real.log (4 * Real.pi)
  refine Exists.intro (nicolasLogSpectralConstant + abs beta + 2) ?_
  filter_upwards [eventually_nicolasLog_normalized_wave_error hRH,
      eventually_ge_atTop (Real.exp 1)] with x he hx
  have hxOne : 1 < x := lt_of_lt_of_le (Real.one_lt_exp_iff.mpr (by norm_num)) hx
  have hLog : 1 <= Real.log x := by
    have h := Real.log_le_log (Real.exp_pos 1) hx
    simpa only [Real.log_exp] using h
  have hDiv : nicolasLogSpectralConstant / Real.log x <= nicolasLogSpectralConstant :=
    div_le_self nicolasLogSpectralConstant_pos.le hLog
  have hWave := abs_nicolasZeroWave_le hRH hxOne
  change abs (nicolasZeroWave x) <= beta at hWave
  linarith only [(abs_le.mp he).2, (abs_le.mp hWave).1, hDiv, le_abs_self beta]

/-- RH is detected by eventual upper boundedness on any admissible sparse mesh. -/
theorem riemannHypothesis_iff_nicolasLog_subpower_mesh_bounded
    (u : Nat -> Nat) (hu : StrictMono u)
    (hmesh : Nat.SubpowerGapBound u (3 / 4)) :
    RiemannHypothesis <-> exists C : Real, Filter.Eventually (fun j : Nat =>
      (u j : Real) ^ (1 / 2 : Real) * Real.log (u j : Real) *
        nicolasLogMertensOscillation (u j : Real) <= C) atTop := by
  constructor
  . intro hRH
    choose C hC using exists_eventually_nicolasLog_normalized_le_of_RH hRH
    have ht : Tendsto (fun j : Nat => (u j : Real)) atTop atTop :=
      tendsto_natCast_atTop_atTop.comp hu.tendsto_atTop
    exact Exists.intro C (ht.eventually hC)
  . intro hBound
    by_contra hNotRH
    choose C hC using hBound
    choose J hJ using eventually_atTop.1 hC
    choose j hj hLarge using
      nicolasLog_unbounded_on_subpower_mesh_of_not_RH u hu hmesh hNotRH C (u J : Real)
    have hJj : J <= j := by
      by_contra h
      have hle : j <= J := le_of_lt (lt_of_not_ge h)
      have hule : (u j : Real) <= (u J : Real) := by exact_mod_cast hu.monotone hle
      linarith
    exact not_lt_of_ge (hJ j hJj) hLarge

/-- In particular fourth-power samples alone detect RH. -/
theorem riemannHypothesis_iff_nicolasLog_fourthPower_bounded :
    RiemannHypothesis <-> exists C : Real, Filter.Eventually (fun j : Nat =>
      ((j ^ 4 : Nat) : Real) ^ (1 / 2 : Real) * Real.log ((j ^ 4 : Nat) : Real) *
        nicolasLogMertensOscillation ((j ^ 4 : Nat) : Real) <= C) atTop :=
  riemannHypothesis_iff_nicolasLog_subpower_mesh_bounded
    (fun j : Nat => j ^ 4) Nat.strictMono_fourthPower Nat.subpowerGapBound_fourthPower

theorem eventually_nicolas_normalization_le_endpoint :
    Filter.Eventually (fun x : Real =>
      x ^ (1 / 2 : Real) * Real.log x <= x) atTop := by
  have hRatio : Tendsto (fun x : Real => Real.log x / x ^ (1 / 2 : Real))
      atTop (nhds 0) :=
    (isLittleO_log_rpow_atTop (by norm_num : (0 : Real) < 1 / 2)).tendsto_div_nhds_zero
  have hSmall := hRatio.eventually
    (eventually_le_nhds (by norm_num : (0 : Real) < 1))
  filter_upwards [hSmall, eventually_gt_atTop (0 : Real)] with x hs hx
  have hRoot := Real.rpow_pos_of_pos hx (1 / 2 : Real)
  have hLog : Real.log x <= x ^ (1 / 2 : Real) := (div_le_one hRoot).mp hs
  calc
    x ^ (1 / 2 : Real) * Real.log x <=
        x ^ (1 / 2 : Real) * x ^ (1 / 2 : Real) :=
      mul_le_mul_of_nonneg_left hLog hRoot.le
    _ = x := by rw [<- Real.rpow_add hx]; norm_num

namespace QuadraticPrimeLaw

/-- The exact ratio criterion needs only sparse samples, for every qualifying law. -/
theorem riemannHypothesis_iff_subpower_mesh_densityRatio_le_reference
    (law : QuadraticPrimeLaw) (alpha : Real) (ha : 0 < alpha)
    (u : Nat -> Nat) (hu : StrictMono u)
    (hmesh : Nat.SubpowerGapBound u (3 / 4)) :
    RiemannHypothesis <-> Filter.Eventually (fun j : Nat =>
      let N := u j
      let r := Nat.floor (alpha * law.referenceClock N)
      law.densityRatio N r <= law.referenceRatio r (law.referenceClock N)) atTop := by
  constructor
  . intro hRH
    exact hu.tendsto_atTop.eventually
      ((law.eventually_densityRatio_lt_reference_of_RH alpha ha hRH).mono
        (fun _ h => h.le))
  . intro hRatio
    apply (riemannHypothesis_iff_nicolasLog_subpower_mesh_bounded u hu hmesh).mpr
    choose C hC hSign using law.exists_eventually_densityRatio_reference_sign alpha ha
    have ht : Tendsto (fun j : Nat => (u j : Real)) atTop atTop :=
      tendsto_natCast_atTop_atTop.comp hu.tendsto_atTop
    refine Exists.intro (C / law.nu) ?_
    filter_upwards [hu.tendsto_atTop.eventually hSign, hRatio,
      ht.eventually eventually_nicolas_normalization_le_endpoint,
      hu.tendsto_atTop.eventually_ge_atTop 1] with j hs hr hw hjOne
    have hn : (0 : Real) < u j := by exact_mod_cast hjOne
    have hF : law.nu * nicolasLogMertensOscillation (u j : Real) <= C / (u j : Real) := by
      by_contra h
      have hAbove := hs.2.2.2.2.1 (lt_of_not_ge h)
      exact not_lt_of_ge hr hAbove
    have hS : 0 <= (u j : Real) ^ (1 / 2 : Real) * Real.log (u j : Real) :=
      mul_nonneg (Real.rpow_nonneg hn.le _)
        (Real.log_nonneg (by exact_mod_cast hjOne))
    have hScaled := mul_le_mul_of_nonneg_left hF hS
    have hBudget := mul_le_mul_of_nonneg_right hw (div_nonneg hC hn.le)
    have hCancel : (u j : Real) * (C / (u j : Real)) = C := by field_simp
    rw [hCancel] at hBudget
    apply _root_.le_of_mul_le_mul_left ?_ law.nu_pos
    have hNuCancel : law.nu * (C / law.nu) = C := by field_simp [law.nu_pos.ne']
    rw [hNuCancel]
    nlinarith only [hScaled, hBudget]

theorem riemannHypothesis_iff_subpower_mesh_densityRatio_lt_reference
    (law : QuadraticPrimeLaw) (alpha : Real) (ha : 0 < alpha)
    (u : Nat -> Nat) (hu : StrictMono u)
    (hmesh : Nat.SubpowerGapBound u (3 / 4)) :
    RiemannHypothesis <-> Filter.Eventually (fun j : Nat =>
      let N := u j
      let r := Nat.floor (alpha * law.referenceClock N)
      law.densityRatio N r < law.referenceRatio r (law.referenceClock N)) atTop := by
  constructor
  . intro hRH
    exact hu.tendsto_atTop.eventually
      (law.eventually_densityRatio_lt_reference_of_RH alpha ha hRH)
  . intro h
    exact (law.riemannHypothesis_iff_subpower_mesh_densityRatio_le_reference
      alpha ha u hu hmesh).mpr (h.mono (fun _ hx => hx.le))

end QuadraticPrimeLaw

end PrimeFactorOscillations

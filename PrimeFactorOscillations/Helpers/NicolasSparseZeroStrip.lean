/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/

import PrimeFactorOscillations.Helpers.NicolasSparseSampling

/-!
# Sparse comparison and zero strips

For real q >= 1 the sampled comparison forces Re rho <= max(1/2,1-2/q). For q <= 4 it is equivalent to RH.
-/

set_option autoImplicit false
set_option Elab.async false

open Filter Robin1984
open scoped Topology

noncomputable section

namespace PrimeFactorOscillations

theorem nicolasLog_unbounded_on_subpower_mesh_of_zero
    {rho : Complex} (hZero : riemannZeta rho = 0)
    (hHalf : (1 / 2 : Real) < rho.re) (hOne : rho.re < 1)
    (a : Real) (ha : 0 <= a) (hSep : 2 * a - 1 < rho.re)
    (u : Nat -> Nat) (hu : StrictMono u) (hmesh : Nat.SubpowerGapBound u a) (A X : Real) :
    exists j : Nat, X < (u j : Real) /\
      A < (u j : Real) ^ (1 / 2 : Real) * Real.log (u j : Real) *
        nicolasLogMertensOscillation (u j : Real) := by
  have hLoHalf : 1 - rho.re < (1 / 2 : Real) := by linarith
  have hLoMesh : 1 - rho.re < 2 * (1 - a) := by linarith
  have hLoMin : 1 - rho.re < min (1 / 2 : Real) (2 * (1 - a)) :=
    lt_min hLoHalf hLoMesh
  let b : Real := ((1 - rho.re) + min (1 / 2 : Real) (2 * (1 - a))) / 2
  have hLower : 1 - rho.re < b := by dsimp only [b]; linarith
  have hbHalf : b < (1 / 2 : Real) := by
    dsimp only [b]
    linarith [min_le_left (1 / 2 : Real) (2 * (1 - a))]
  have hbMesh : b < 2 * (1 - a) := by
    dsimp only [b]
    linarith [min_le_right (1 / 2 : Real) (2 * (1 - a))]
  have hb : 0 < b := by linarith
  have hIntervals := fun d A X hd hA =>
    nicolasLog_power_intervals_of_zero hZero hHalf hOne hLower hbHalf.le d A X hd hA
  let d : Real := (a + (1 - b / 2)) / 2
  have hdLow : a < d := by dsimp only [d]; linarith
  have hdHigh : d < 1 - b / 2 := by dsimp only [d]; linarith
  have hSample := Nat.eventually_exists_sample_mem_power_window
    u hu a d ha hdLow hmesh
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

namespace QuadraticPrimeLaw

/-- The sampled one-sided ratio comparison bounds the full Nicolas signal,
independently of any mesh exponent or RH assumption. -/
theorem exists_eventually_nicolasLog_normalized_le_of_ratio
    (law : QuadraticPrimeLaw) (alpha : Real) (ha : 0 < alpha)
    (u : Nat -> Nat) (hu : StrictMono u)
    (hRatio : Filter.Eventually (fun j : Nat =>
      let N := u j
      let r := Nat.floor (alpha * law.referenceClock N)
      law.densityRatio N r <= law.referenceRatio r (law.referenceClock N)) atTop) :
    exists D : Real, Filter.Eventually (fun j : Nat =>
      (u j : Real) ^ (1 / 2 : Real) * Real.log (u j : Real) *
        nicolasLogMertensOscillation (u j : Real) <= D) atTop := by
  choose C hC hSign using law.exists_eventually_densityRatio_reference_sign alpha ha
  have ht : Tendsto (fun j : Nat => (u j : Real)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp hu.tendsto_atTop
  refine Exists.intro (C / law.nu) ?_
  filter_upwards [hu.tendsto_atTop.eventually hSign, hRatio,
    ht.eventually eventually_nicolas_normalization_le_endpoint,
    hu.tendsto_atTop.eventually_ge_atTop 1] with j hs hr hw hjOne
  have hn : (0 : Real) < u j := Nat.cast_pos.mpr (Nat.lt_of_lt_of_le Nat.zero_lt_one hjOne)
  have hF : law.nu * nicolasLogMertensOscillation (u j : Real) <= C / (u j : Real) := by
    by_contra h
    have hAbove := hs.2.2.2.2.1 (lt_of_not_ge h)
    exact not_lt_of_ge hr hAbove
  have hOneReal : (1 : Real) <= u j := by
    simpa only [Nat.cast_one] using
      (Nat.cast_le.mpr hjOne : ((1 : Nat) : Real) <= (u j : Real))
  have hS : 0 <= (u j : Real) ^ (1 / 2 : Real) * Real.log (u j : Real) :=
    mul_nonneg (Real.rpow_nonneg hn.le _)
      (Real.log_nonneg hOneReal)
  have hScaled := mul_le_mul_of_nonneg_left hF hS
  have hBudget := mul_le_mul_of_nonneg_right hw (div_nonneg hC hn.le)
  have hCancel : (u j : Real) * (C / (u j : Real)) = C := by field_simp
  rw [hCancel] at hBudget
  apply _root_.le_of_mul_le_mul_left ?_ law.nu_pos
  have hNuCancel : law.nu * (C / law.nu) = C := by field_simp [law.nu_pos.ne']
  rw [hNuCancel]
  nlinarith only [hScaled, hBudget]

theorem re_zero_le_max_of_subpower_mesh_densityRatio_le
    (law : QuadraticPrimeLaw) (alpha : Real) (ha : 0 < alpha)
    (a : Real) (haNonneg : 0 <= a)
    (u : Nat -> Nat) (hu : StrictMono u) (hmesh : Nat.SubpowerGapBound u a)
    (hRatio : Filter.Eventually (fun j : Nat =>
      let N := u j
      let r := Nat.floor (alpha * law.referenceClock N)
      law.densityRatio N r <= law.referenceRatio r (law.referenceClock N)) atTop)
    {rho : Complex} (hZero : riemannZeta rho = 0) (hOne : rho.re < 1) :
    rho.re <= max (1 / 2 : Real) (2 * a - 1) := by
  by_contra hn
  have hAbove : max (1 / 2 : Real) (2 * a - 1) < rho.re := lt_of_not_ge hn
  have hHalf : (1 / 2 : Real) < rho.re := (le_max_left _ _).trans_lt hAbove
  have hSep : 2 * a - 1 < rho.re := (le_max_right _ _).trans_lt hAbove
  choose D hBound using law.exists_eventually_nicolasLog_normalized_le_of_ratio alpha ha u hu hRatio
  choose J hJ using eventually_atTop.mp hBound
  choose j hj hGrowth using nicolasLog_unbounded_on_subpower_mesh_of_zero hZero hHalf hOne
    a haNonneg hSep u hu hmesh D (u J : Real)
  have hIndex : J <= j := (hu.lt_iff_lt.mp (Nat.cast_lt.mp hj)).le
  exact not_lt_of_ge (hJ j hIndex) hGrowth

/-- The exact floor-power sampling consequence, for every real q >= 1. -/
theorem re_zero_le_max_of_powerSamples_densityRatio_le
    (law : QuadraticPrimeLaw) (alpha : Real) (ha : 0 < alpha)
    (q : Real) (hq : 1 <= q)
    (hRatio : Filter.Eventually (fun j : Nat =>
      let N := Nat.powerSamples q j
      let r := Nat.floor (alpha * law.referenceClock N)
      law.densityRatio N r <= law.referenceRatio r (law.referenceClock N)) atTop)
    {rho : Complex} (hZero : riemannZeta rho = 0) (hOne : rho.re < 1) :
    rho.re <= max (1 / 2 : Real) (1 - 2 / q) := by
  have haNonneg : 0 <= 1 - 1 / q := by
    have hInv := _root_.div_le_self (by norm_num : (0 : Real) <= 1) hq
    linarith
  have h := law.re_zero_le_max_of_subpower_mesh_densityRatio_le alpha ha
    (1 - 1 / q) haNonneg (Nat.powerSamples q) (Nat.strictMono_powerSamples q hq)
    (Nat.subpowerGapBound_powerSamples q hq) hRatio hZero hOne
  have hId : 2 * (1 - 1 / q) - 1 = 1 - 2 / q := by ring
  simpa only [hId] using h

theorem riemannHypothesis_iff_powerSamples_densityRatio_le
    (law : QuadraticPrimeLaw) (alpha : Real) (ha : 0 < alpha)
    (q : Real) (hq : 1 <= q) (hqUpper : q <= 4) :
    RiemannHypothesis <-> Filter.Eventually (fun j : Nat =>
      let N := Nat.powerSamples q j
      let r := Nat.floor (alpha * law.referenceClock N)
      law.densityRatio N r <= law.referenceRatio r (law.referenceClock N)) atTop := by
  constructor
  . intro hRH
    exact (Nat.strictMono_powerSamples q hq).tendsto_atTop.eventually
      ((law.eventually_densityRatio_lt_reference_of_RH alpha ha hRH).mono (fun _ h => h.le))
  . intro hRatio
    by_contra hNotRH
    choose rho hZero hHalf hOne using
      exists_riemannZeta_zero_re_gt_half_of_not_riemannHypothesis hNotRH
    have hBound := law.re_zero_le_max_of_powerSamples_densityRatio_le
      alpha ha q hq hRatio hZero hOne
    have hqPos : 0 < q := lt_of_lt_of_le zero_lt_one hq
    have hInv : 1 / (4 : Real) <= 1 / q := one_div_le_one_div_of_le hqPos hqUpper
    have hTwo : (1 / 2 : Real) <= 2 / q := by
      have h := mul_le_mul_of_nonneg_left hInv (by norm_num : (0 : Real) <= 2)
      convert h using 1 <;> ring
    have hEndpoint : 1 - 2 / q <= (1 / 2 : Real) := by linarith
    rw [max_eq_left hEndpoint] at hBound
    exact not_le_of_gt hHalf hBound

end QuadraticPrimeLaw

end PrimeFactorOscillations

/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.QuadraticProfileClockSign
import PrimeFactorOscillations.Mathlib.Algebra.Order.Floor.Interval

/-!
# Eventual sign transfer for moving floor ranks

Divergence of the reference clock and convergence of their difference place
the entire clock segment in the proved uniform ratio-comparison range.
-/

set_option autoImplicit false
set_option Elab.async false

namespace PrimeFactorOscillations.QuadraticPrimeLaw

open BombieriVinogradov.ComplexAnalysis

theorem exists_eventually_prefixProfile_moving_floor_sign (law : QuadraticPrimeLaw)
    (alpha : Real) (ha : 0 < alpha) (B L : Nat -> Real)
    (hL : Filter.Tendsto L Filter.atTop Filter.atTop)
    (hBL : Filter.Tendsto (fun N => B N - L N) Filter.atTop (nhds 0)) :
    exists C : Real, 0 <= C /\ Filter.Eventually (fun N : Nat =>
      let r := Nat.floor (alpha * L N)
      let cN : Nat -> Real := fun j => (taylorCoefficient (law.complexPrefix N) 0 j).re
      let RP := Nat.factorialConvolution cN (r - 1) (B N) /
        Nat.factorialConvolution cN r (B N)
      let RR := Nat.factorialConvolution law.realCoefficient (r - 1) (L N) /
        Nat.factorialConvolution law.realCoefficient r (L N)
      0 < r /\ 0 < Nat.factorialConvolution cN r (B N) /\
        0 < Nat.factorialConvolution law.realCoefficient r (L N) /\
        (C / (N : Real) < L N - B N -> RR < RP) /\
        (L N - B N < -C / (N : Real) -> RP < RR)) Filter.atTop := by
  have ha3 : 0 < alpha / 3 := by linarith
  have hab : alpha / 3 <= 2 * alpha := by linarith
  obtain hs := law.exists_prefixProfile_clock_sign_transfer
    (alpha / 3) (2 * alpha) ha3 hab
  choose r0 N0 C hr0 hN0 hC hsign using hs
  refine Exists.intro C (And.intro hC ?_)
  have hcloseLo := (tendsto_order.mp hBL).1 (-1) (by norm_num : (-1 : Real) < 0)
  have hcloseHi := (tendsto_order.mp hBL).2 1 (by norm_num : (0 : Real) < 1)
  have hclose : Filter.Eventually (fun N => abs (B N - L N) <= 1) Filter.atTop := by
    apply (hcloseLo.and hcloseHi).mono
    intro N hN
    exact abs_le.mpr (And.intro hN.1.le hN.2.le)
  have hlargeL := hL.eventually_ge_atTop (max 2 (max (2 / alpha) (((r0 : Real) + 1) / alpha)))
  have hlargeN : Filter.Eventually (fun N : Nat => N0 <= N) Filter.atTop :=
    Filter.eventually_ge_atTop N0
  apply ((hlargeL.and hclose).and hlargeN).mono
  intro N hN
  have hLN : 2 <= L N := (le_max_left _ _).trans hN.1.1
  have h2 : 2 / alpha <= L N := (le_max_left _ _).trans ((le_max_right _ _).trans hN.1.1)
  have hr : ((r0 : Real) + 1) / alpha <= L N :=
    (le_max_right _ _).trans ((le_max_right _ _).trans hN.1.1)
  have h2a : 2 <= alpha * L N := by
    have hm := mul_le_mul_of_nonneg_right h2 ha.le
    have hc : 2 / alpha * alpha = 2 := by field_simp
    rw [hc] at hm
    nlinarith
  have hra : (r0 : Real) + 1 <= alpha * L N := by
    have hm := mul_le_mul_of_nonneg_right hr ha.le
    have hc : (((r0 : Real) + 1) / alpha) * alpha = (r0 : Real) + 1 := by field_simp
    rw [hc] at hm
    nlinarith
  have hrank : r0 <= Nat.floor (alpha * L N) := by
    have hlo := Nat.lt_floor_add_one (alpha * L N)
    have hle : (r0 : Real) <= Nat.floor (alpha * L N) := by linarith
    exact_mod_cast hle
  have hseg := Nat.floor_mul_div_mem_compact_of_abs_sub_le_one
    alpha (B N) (L N) ha hLN h2a hN.1.2
  have hresult := hsign (Nat.floor (alpha * L N)) hrank N hN.2 (B N) (L N) hseg.2
  exact And.intro hseg.1 hresult

end PrimeFactorOscillations.QuadraticPrimeLaw

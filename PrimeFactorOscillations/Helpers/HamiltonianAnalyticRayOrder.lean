/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import Mathlib.Analysis.Analytic.Order
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity

/-! # Taylor order certified by a bound on the positive real ray

A finite Gaussian jet is controlled initially at nonnegative real parameters.
Analyticity promotes its power saving to exact complex Taylor coefficient
agreement. No differentiation under an unbounded integral is assumed.
-/

set_option autoImplicit false
set_option Elab.async false

noncomputable section

namespace PrimeFactorOscillations

open scoped Topology

theorem hamiltonian_analytic_order_of_positive_ray
    (f : Complex -> Complex) (hf : AnalyticAt Complex f 0)
    (H : Nat) (C r : Real) (hC : 0 <= C) (hr : 0 < r)
    (hBound : forall t : Real, 0 < t -> t < r -> norm (f (t : Complex)) <= C * t ^ H) :
    (H : ENat) <= analyticOrderAt f 0 := by
  classical
  by_contra hOrder
  have hFinite : Not (analyticOrderAt f 0 = Top.top) := by
    intro hTop
    rw [hTop] at hOrder
    exact hOrder le_top
  let m := analyticOrderNatAt f 0
  have hNat : (m : ENat) = analyticOrderAt f 0 := Nat.cast_analyticOrderNatAt hFinite
  have hm : m < H := by
    have hLt := lt_of_not_ge hOrder
    rw [<- hNat] at hLt
    exact_mod_cast hLt
  have hFactor := hf.analyticOrderAt_ne_top.mp hFinite
  let g := hFactor.choose
  have hg : AnalyticAt Complex g 0 := hFactor.choose_spec.1
  have hg0 : Not (g 0 = 0) := hFactor.choose_spec.2.1
  have hEq := hFactor.choose_spec.2.2
  let a : Real := norm (g 0)
  have ha : 0 < a := norm_pos_iff.mpr hg0
  have hHalf : a / 2 < norm (g 0) := by dsimp only [a]; linarith
  have hNear : Filter.Eventually (fun z => a / 2 < norm (g z))
      (nhds (0 : Complex)) :=
    hg.continuousAt.norm.eventually (Ioi_mem_nhds hHalf)
  have hBoth := Metric.eventually_nhds_iff.mp (hEq.and hNear)
  let d : Real := hBoth.choose
  have hd : 0 < d := hBoth.choose_spec.1
  have hLocal := hBoth.choose_spec.2
  have hC1 : 0 < C + 1 := by linarith
  have hSmall : 0 < min r (min d (min 1 (a / (2 * (C + 1))))) :=
    lt_min hr (lt_min hd (lt_min (by norm_num) (div_pos ha (by positivity))))
  have hChoose := exists_between hSmall
  let t : Real := hChoose.choose
  have ht : 0 < t := hChoose.choose_spec.1
  have htSmall := hChoose.choose_spec.2
  have htr : t < r := lt_of_lt_of_le htSmall (min_le_left _ _)
  have htd : t < d := lt_of_lt_of_le htSmall
    (le_trans (min_le_right _ _) (min_le_left _ _))
  have htOne : t <= 1 := le_of_lt (lt_of_lt_of_le htSmall
    (le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_left _ _))))
  have htA : t < a / (2 * (C + 1)) := lt_of_lt_of_le htSmall
    (le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_right _ _)))
  have hDist : dist (t : Complex) 0 < d := by
    simpa only [dist_zero_right, Complex.norm_real, Real.norm_eq_abs, abs_of_pos ht] using htd
  have hAt := hLocal hDist
  have hScalar : f (t : Complex) = (t : Complex) ^ m * g (t : Complex) := by
    simpa only [sub_zero, smul_eq_mul] using hAt.1
  have hNorm : t ^ m * norm (g (t : Complex)) <= C * t ^ H := by
    have hB := hBound t ht htr
    rw [hScalar, norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos ht] at hB
    exact hB
  have hExponents : H = m + (H - m) := by omega
  have hCancel : t ^ m * norm (g (t : Complex)) <=
      t ^ m * (C * t ^ (H - m)) := by
    calc
      _ <= C * t ^ H := hNorm
      _ = _ := by
        have hPowerEq : t ^ H = t ^ m * t ^ (H - m) := by
          rw [<- pow_add, <- hExponents]
        rw [hPowerEq]
        ring
  have hG : norm (g (t : Complex)) <= C * t ^ (H - m) := by
    by_contra h
    have hLt := mul_lt_mul_of_pos_left (lt_of_not_ge h) (pow_pos ht m)
    exact (not_lt_of_ge hCancel) hLt
  have hPowers : forall k : Nat, t ^ k <= 1 := by
    intro k
    induction k with
    | zero => simp only [pow_zero, le_refl]
    | succ k ih =>
      rw [pow_succ]
      exact le_trans (mul_le_mul_of_nonneg_right ih ht.le) (by simpa using htOne)
  have hPow : t ^ (H - m) <= t := by
    have hIndex : H - m = (H - m - 1) + 1 := by omega
    rw [hIndex, pow_succ]
    exact le_trans (mul_le_mul_of_nonneg_right (hPowers _) ht.le) (by simp)
  have hGT : norm (g (t : Complex)) <= C * t :=
    le_trans hG (mul_le_mul_of_nonneg_left hPow hC)
  have hDen : Not (2 * (C + 1) = 0) := ne_of_gt (by positivity)
  have hDiv : a / (2 * (C + 1)) * (2 * (C + 1)) = a := by
    field_simp
  have hTMul := mul_lt_mul_of_pos_right htA (show 0 < 2 * (C + 1) by positivity)
  rw [hDiv] at hTMul
  nlinarith [hAt.2]

theorem hamiltonian_derivatives_zero_of_positive_ray
    (f : Complex -> Complex) (hf : AnalyticAt Complex f 0)
    (H : Nat) (C r : Real) (hC : 0 <= C) (hr : 0 < r)
    (hBound : forall t : Real, 0 < t -> t < r -> norm (f (t : Complex)) <= C * t ^ H) :
    forall k : Nat, k < H -> iteratedDeriv k f 0 = 0 :=
  (natCast_le_analyticOrderAt_iff_iteratedDeriv_eq_zero hf).mp
    (hamiltonian_analytic_order_of_positive_ray f hf H C r hC hr hBound)

end PrimeFactorOscillations

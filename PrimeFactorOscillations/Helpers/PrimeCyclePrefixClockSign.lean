/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.PrimeCyclePrefixApproximation
import PrimeFactorOscillations.Helpers.QuadraticProfileClockSign
import PrimeFactorOscillations.Mathlib.Algebra.Order.Floor.Interval

/-!
# Clock-sign transfer for ordered prime cycles

The canonical reference secant consumes the inverse-rank coefficient error.
Both clock signs and all denominator conditions survive, including along
moving floor ranks. No pointwise qualification of the transported weights
is assumed.
-/

set_option autoImplicit false
set_option Elab.async false

namespace PrimeFactorOscillations.PrimeCyclePrefix

open BombieriVinogradov.ComplexAnalysis

theorem exists_prefixProfile_clock_sign_transfer (f : PrimeCyclePrefix)
    (a b : Real) (ha : 0 < a) (hab : a <= b) :
    exists r0 N0 : Nat, exists C : Real,
      0 < r0 /\ 1 <= N0 /\ 0 <= C /\
      forall r : Nat, r0 <= r -> forall N : Nat, N0 <= N ->
      forall B L : Real,
      (forall u : Real, Set.Icc (min B L) (max B L) u ->
        0 < u /\ a <= (r : Real) / u /\ (r : Real) / u <= b) ->
      0 < Nat.factorialConvolution
        (fun j => (taylorCoefficient (f.complexPrefix N) 0 j).re) r B /\
      0 < Nat.factorialConvolution canonicalPrimeOddsLaw.realCoefficient r L /\
      (C / (N : Real) < L - B ->
        Nat.factorialConvolution canonicalPrimeOddsLaw.realCoefficient (r - 1) L /
            Nat.factorialConvolution canonicalPrimeOddsLaw.realCoefficient r L <
          Nat.factorialConvolution
              (fun j => (taylorCoefficient (f.complexPrefix N) 0 j).re) (r - 1) B /
            Nat.factorialConvolution
              (fun j => (taylorCoefficient (f.complexPrefix N) 0 j).re) r B) /\
      (L - B < -C / (N : Real) ->
        Nat.factorialConvolution
            (fun j => (taylorCoefficient (f.complexPrefix N) 0 j).re) (r - 1) B /
          Nat.factorialConvolution
            (fun j => (taylorCoefficient (f.complexPrefix N) 0 j).re) r B <
        Nat.factorialConvolution canonicalPrimeOddsLaw.realCoefficient (r - 1) L /
          Nat.factorialConvolution canonicalPrimeOddsLaw.realCoefficient r L) := by
  have hb : 0 <= b := ha.le.trans hab
  obtain hs := canonicalPrimeOddsLaw.exists_profile_reference_secant_bounds a b ha hab
  choose rS hrS hsecant using hs
  obtain he := f.exists_factorialConvolution_ratio_error b hb
  choose rP N0 K hrP hN0 hK herror using he
  let C := 2 * K / a ^ 2
  have hC : 0 <= C := by dsimp [C]; positivity
  refine Exists.intro (max rS rP) (Exists.intro N0 (Exists.intro C
    (And.intro (hrS.trans_le (le_max_left _ _)) (And.intro hN0 (And.intro hC ?_)))))
  intro r hr N hN B L hsegment
  have hrS' : rS <= r := (le_max_left _ _).trans hr
  have hrP' : rP <= r := (le_max_right _ _).trans hr
  have hrR : (0 : Real) < r := by exact_mod_cast hrS.trans_le hrS'
  have hNR : (0 : Real) < N := by exact_mod_cast lt_of_lt_of_le Nat.zero_lt_one (hN0.trans hN)
  have hB := hsegment B (And.intro (min_le_left _ _) (le_max_left _ _))
  have hL := hsegment L (And.intro (min_le_right _ _) (le_max_right _ _))
  have heB := herror r hrP' N hN B hB.1 hB.2.2
  have heL := herror r hrP' N hN L hL.1 hL.2.2
  obtain hq := hsecant r hrS' B L hsegment
  choose q hqlo hqhi hqeq using hq
  let R : Real -> Real := fun u =>
    Nat.factorialConvolution canonicalPrimeOddsLaw.realCoefficient (r - 1) u /
      Nat.factorialConvolution canonicalPrimeOddsLaw.realCoefficient r u
  let RN : Real := Nat.factorialConvolution
    (fun j => (taylorCoefficient (f.complexPrefix N) 0 j).re) (r - 1) B /
      Nat.factorialConvolution
        (fun j => (taylorCoefficient (f.complexPrefix N) 0 j).re) r B
  have herr : abs (RN - R B) <= K / ((r : Real) * (N : Real)) := heB.2.2
  change R B - R L = q * (L - B) at hqeq
  have hgain (w : Real) (hw : C / (N : Real) < w) :
      K / ((r : Real) * (N : Real)) < a ^ 2 / (2 * (r : Real)) * w := by
    have h := mul_lt_mul_of_pos_left hw (by positivity : 0 < a ^ 2 / (2 * (r : Real)))
    have hid : a ^ 2 / (2 * (r : Real)) * (C / (N : Real)) =
        K / ((r : Real) * (N : Real)) := by
      dsimp [C]
      field_simp
    rwa [hid] at h
  have hpositive : C / (N : Real) < L - B -> R L < RN := by
    intro hF
    have hFpos : 0 <= L - B := (div_nonneg hC hNR.le).trans hF.le
    have hqF := mul_le_mul_of_nonneg_right hqlo hFpos
    have hg := hgain (L - B) hF
    have hlow := (abs_le.mp herr).1
    linarith
  have hnegative : L - B < -C / (N : Real) -> RN < R L := by
    intro hF
    rw [neg_div] at hF
    have hF' : C / (N : Real) < -(L - B) := by linarith only [hF]
    have hFpos : 0 <= -(L - B) := (div_nonneg hC hNR.le).trans hF'.le
    have hqF := mul_le_mul_of_nonneg_right hqlo hFpos
    have hg := hgain (-(L - B)) hF'
    have hupp := (abs_le.mp herr).2
    nlinarith
  exact And.intro heB.1 (And.intro heL.2.1 (And.intro hpositive hnegative))

theorem exists_eventually_prefixProfile_moving_floor_sign (f : PrimeCyclePrefix)
    (alpha : Real) (ha : 0 < alpha) (B L : Nat -> Real)
    (hL : Filter.Tendsto L Filter.atTop Filter.atTop)
    (hBL : Filter.Tendsto (fun N => B N - L N) Filter.atTop (nhds 0)) :
    exists C : Real, 0 <= C /\ Filter.Eventually (fun N : Nat =>
      let r := Nat.floor (alpha * L N)
      let cN : Nat -> Real := fun j => (taylorCoefficient (f.complexPrefix N) 0 j).re
      let RP := Nat.factorialConvolution cN (r - 1) (B N) /
        Nat.factorialConvolution cN r (B N)
      let RR := Nat.factorialConvolution canonicalPrimeOddsLaw.realCoefficient (r - 1) (L N) /
        Nat.factorialConvolution canonicalPrimeOddsLaw.realCoefficient r (L N)
      0 < r /\ 0 < Nat.factorialConvolution cN r (B N) /\
        0 < Nat.factorialConvolution canonicalPrimeOddsLaw.realCoefficient r (L N) /\
        (C / (N : Real) < L N - B N -> RR < RP) /\
        (L N - B N < -C / (N : Real) -> RP < RR)) Filter.atTop := by
  have ha3 : 0 < alpha / 3 := by linarith
  have hab : alpha / 3 <= 2 * alpha := by linarith
  obtain hs := f.exists_prefixProfile_clock_sign_transfer
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

end PrimeFactorOscillations.PrimeCyclePrefix

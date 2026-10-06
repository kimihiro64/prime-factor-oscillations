/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.NicolasPowerPersistence
import PrimeFactorOscillations.Helpers.PrimeProfilePowerExcursions
import PrimeFactorOscillations.Helpers.TiltedCountRHUpper

/-!
# Uniform ratio excursions at the resolution of the tilt grid

If RH fails, for every fixed d <= 3/4, arbitrarily late intervals of length n^d have
actual-minus-reference coefficient ratio exceeding C / sqrt(n),
for every fixed C > 0 and uniformly across every fixed positive compact
rank band. Both coefficient denominators remain positive.

The proof combines the established Nicolas power persistence, the signed
uniform coefficient comparison, and elementary subpower growth of the
theta clock. It supplies the analytic detection margin before any
short-interval bounded-prime-pair theorem or finite cell selection is used.
It does not prove an independent upper bound for the signed counts.
-/

set_option autoImplicit false
set_option Elab.async false

noncomputable section

namespace PrimeFactorOscillations

open Filter Robin1984

theorem eventually_thetaClock_add_one_le_power
    (e D : Real) (he : 0 < e) (hD : 0 < D) :
    Filter.Eventually (fun x : Real =>
      Real.eulerMascheroniConstant + Real.log (Real.log (Chebyshev.theta x)) + 1 <=
        D * x ^ e) atTop := by
  have hLog := (isLittleO_log_rpow_atTop he).bound (by linarith : 0 < D / 2)
  have hPower := (tendsto_rpow_atTop he).eventually_ge_atTop
    ((Real.eulerMascheroniConstant + Real.log 2) / (D / 2))
  filter_upwards [hLog, hPower, eventually_theta_half_double,
    eventually_thetaClock_dyadic_width, eventually_ge_atTop (2 : Real)] with
    x hLogX hPowerX hTheta hWidth hx
  have hxPos : 0 < x := by linarith
  have hThetaPos : 0 < Chebyshev.theta x := by linarith [hWidth.1]
  have hLogThetaPos : 0 < Real.log (Chebyshev.theta x) :=
    Real.log_pos (by linarith [hWidth.1])
  have hLogClock := Real.log_le_sub_one_of_pos hLogThetaPos
  have hLogTheta := Real.log_le_log hThetaPos hTheta.2
  rw [Real.log_mul (by norm_num : Not ((2 : Real) = 0)) hxPos.ne'] at hLogTheta
  have hLogBound : Real.log x <= (D / 2) * x ^ e := by
    change norm (Real.log x) <= (D / 2) * norm (x ^ e) at hLogX
    rw [Real.norm_eq_abs, Real.norm_eq_abs,
      abs_of_nonneg (Real.rpow_nonneg hxPos.le _)] at hLogX
    exact (le_abs_self _).trans hLogX
  have hConst := mul_le_mul_of_nonneg_left hPowerX (by linarith : 0 <= D / 2)
  have hCancel : (D / 2) * ((Real.eulerMascheroniConstant + Real.log 2) / (D / 2)) =
      Real.eulerMascheroniConstant + Real.log 2 := by
    field_simp [hD.ne']
  rw [hCancel] at hConst
  linarith

theorem exists_densityRatio_uniform_mesh_excess_of_not_RH
    (hNotRH : Not RiemannHypothesis) (a B : Real)
    (ha : 0 < a) (haB : a <= B) (d : Real) (hd : d <= 3 / 4)
    (C X : Real) (hC : 0 < C) :
    exists n : Nat, X < (n : Real) /\ 6 <= n /\
      forall y : Real, (n : Real) <= y ->
        y <= n + (n : Real) ^ d ->
        let L := Real.eulerMascheroniConstant + Real.log (Real.log (Chebyshev.theta y))
        2 <= L /\
        forall r : Nat, a <= (r : Real) / L -> (r : Real) / L <= B ->
          0 < (PrimeFactorUnimodality.weightEsymm
            (PrimeFactorUnimodality.primesBelow (Nat.floor y + 1)) r : Real) /\
          0 < Nat.factorialConvolution primeProfileRealCoefficient r L /\
          C * (n : Real) ^ (-(1 / 2 : Real)) <
            (PrimeFactorUnimodality.densityRatio
              (PrimeFactorUnimodality.primesBelow (Nat.floor y + 1)) r : Real) -
            Nat.factorialConvolution primeProfileRealCoefficient (r - 1) L /
              Nat.factorialConvolution primeProfileRealCoefficient r L := by
  choose b hb hbHalf hWindows using exists_nicolasLog_power_intervals_of_not_RH hNotRH
  choose K hK hSigned using exists_eventually_densityRatio_signed_thetaClock_margin a B ha haB
  have hSmall := ((rpow_neg_one_isLittleO_rpow_neg
    (by linarith : b < 1)).const_mul_left (K / a)).bound (by linarith : 0 < a / 4)
  have hClock := eventually_thetaClock_add_one_le_power (1 / 2 - b) (a / (4 * C))
    (by linarith) (by positivity)
  choose Y hY using eventually_atTop.mp
    (hSigned.and (hSmall.and (hClock.and (eventually_thetaClock_dyadic_width.and
      (eventually_ge_atTop (2 : Real))))))
  choose n hnCut hnSix hF using hWindows d 1 (max X Y)
    (by linarith) (by norm_num)
  have hnX : X < (n : Real) := (le_max_left _ _).trans_lt hnCut
  have hnY : Y <= (n : Real) := (le_max_right _ _).trans hnCut.le
  have hnPos : (0 : Real) < n := by exact_mod_cast (by omega : 0 < n)
  have hnOne : (1 : Real) <= n := by exact_mod_cast (by omega : 1 <= n)
  have hAtN := hY (n : Real) hnY
  have hErrorN : K / (a * (n : Real)) <= (a / 4) * (n : Real) ^ (-b) := by
    have h := hAtN.2.1
    change norm ((K / a) * (n : Real) ^ (-(1 : Real))) <=
      (a / 4) * norm ((n : Real) ^ (-b)) at h
    rw [Real.norm_eq_abs, Real.norm_eq_abs,
      abs_of_nonneg (mul_nonneg (div_nonneg hK ha.le) (Real.rpow_nonneg hnPos.le _)),
      abs_of_nonneg (Real.rpow_nonneg hnPos.le _), Real.rpow_neg_one] at h
    convert h using 1 <;> ring
  have hWidth : (n : Real) ^ d <= n := by
    calc
      _ <= (n : Real) ^ (1 : Real) :=
        Real.rpow_le_rpow_of_exponent_le hnOne (by linarith)
      _ = _ := Real.rpow_one _
  refine Exists.intro n (And.intro hnX (And.intro hnSix ?_))
  intro y hny hy
  let L := Real.eulerMascheroniConstant + Real.log (Real.log (Chebyshev.theta y))
  have hyPos : 0 < y := hnPos.trans_le hny
  have hAtY := (hY y (hnY.trans hny)).1
  have hLTwo : 2 <= L := hAtY.2.1
  refine And.intro hLTwo ?_
  intro r hLow hHigh
  have hRank := hAtY.2.2 r hLow hHigh
  have hFn : (n : Real) ^ (-b) < nicolasLogMertensOscillation y := by
    simpa only [one_mul] using hF y hny hy
  have hFPos : 0 <= nicolasLogMertensOscillation y :=
    ((Real.rpow_pos_of_pos hnPos (-b)).trans hFn).le
  have hMargin := hRank.2.2.1 hFPos
  have hErr : K / (a * y) <= (a / 4) * (n : Real) ^ (-b) := by
    calc
      K / (a * y) <= K / (a * (n : Real)) :=
        div_le_div_of_nonneg_left hK (mul_pos ha hnPos)
          (mul_le_mul_of_nonneg_left hny ha.le)
      _ <= _ := hErrorN
  have hLCap : L <= (a / (4 * C)) * (n : Real) ^ (1 / 2 - b) := by
    have hDyadic := hAtN.2.2.2.1.2 y hny (by linarith)
    have hCap := hAtN.2.2.1
    dsimp only [L]
    linarith
  let delta := (PrimeFactorUnimodality.densityRatio
      (PrimeFactorUnimodality.primesBelow (Nat.floor y + 1)) r : Real) -
    Nat.factorialConvolution primeProfileRealCoefficient (r - 1) L /
      Nat.factorialConvolution primeProfileRealCoefficient r L
  have hSignal : (a / 4) * (n : Real) ^ (-b) < L * delta := by
    have hScaled := mul_lt_mul_of_pos_left hFn (by linarith : 0 < a / 2)
    change (a / 2) * nicolasLogMertensOscillation y - K / (a * y) <= L * delta at hMargin
    linarith
  have hPowerProduct : (a / (4 * C)) * (n : Real) ^ (1 / 2 - b) *
      (C * (n : Real) ^ (-(1 / 2 : Real))) = (a / 4) * (n : Real) ^ (-b) := by
    calc
      _ = (a / 4) * ((n : Real) ^ (1 / 2 - b) * (n : Real) ^ (-(1 / 2 : Real))) := by
        field_simp [hC.ne']
        <;> ring
      _ = _ := by
        rw [<- Real.rpow_add hnPos]
        congr 2
        ring
  have hTarget := mul_le_mul_of_nonneg_right hLCap
    (mul_nonneg hC.le (Real.rpow_nonneg hnPos.le (-(1 / 2 : Real))))
  rw [hPowerProduct] at hTarget
  refine And.intro hRank.1 (And.intro hRank.2.1 ?_)
  change C * (n : Real) ^ (-(1 / 2 : Real)) < delta
  by_contra hn
  have hCompare := mul_le_mul_of_nonneg_left (le_of_not_gt hn)
    (show 0 <= L by linarith)
  linarith

end PrimeFactorOscillations

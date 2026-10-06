/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.NicolasPowerPersistence

/-!
# Critical logarithmic-length persistence of positive Nicolas excursions

The window has length sqrt(A)/100 * x^(1-b/2)/sqrt(log(x)). The local
theta envelope is retained jointly with the integral and quadratic
losses. The coefficient 104 in the finite bound is absorbed by the chosen
window constant. All amplitudes and onsets remain explicitly quantified.
-/

set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace PrimeFactorOscillations
open Filter Robin1984

def nicolasCriticalWindowLength (eta b x : Real) : Real :=
  eta * x / (x ^ (b / 2) * Real.sqrt (Real.log x))

theorem eventually_nicolasCriticalWindow_bounds
    (B b eta : Real) (hB : 0 <= B) (hb : 0 < b) (he : 0 < eta) :
    Filter.Eventually (fun x : Real =>
      6 <= x /\ 0 < nicolasCriticalWindowLength eta b x /\
      B * x ^ (1 - b) <= nicolasCriticalWindowLength eta b x /\
      4 * nicolasCriticalWindowLength eta b x * Real.log x <= x / 2 /\
      nicolasCriticalWindowLength eta b x <= x /\
      (2 * (4 * nicolasCriticalWindowLength eta b x * Real.log x) *
          nicolasCriticalWindowLength eta b x +
        6 * (4 * nicolasCriticalWindowLength eta b x * Real.log x) ^ (2 : Nat)) /
          (x ^ (2 : Nat) * Real.log x) <=
        104 * eta ^ (2 : Nat) * x ^ (-b)) atTop := by
  have hSmall : Tendsto (fun x : Real => Real.sqrt (Real.log x) / x ^ (b / 2))
      atTop (nhds 0) := by
    simpa only [Real.sqrt_eq_rpow] using
      (isLittleO_log_rpow_rpow_atTop (1 / 2 : Real) (by linarith : 0 < b / 2)).tendsto_div_nhds_zero
  have hBSmall : Tendsto (fun x : Real => B *
      (Real.sqrt (Real.log x) / x ^ (b / 2))) atTop (nhds 0) := by
    simpa only [mul_zero] using hSmall.const_mul B
  have hMSmall : Tendsto (fun x : Real => (4 * eta) *
      (Real.sqrt (Real.log x) / x ^ (b / 2))) atTop (nhds 0) := by
    simpa only [mul_zero] using hSmall.const_mul (4 * eta)
  have hBScale := hBSmall.eventually_lt_const he
  have hMScale := hMSmall.eventually_lt_const (by norm_num : (0 : Real) < 1 / 2)
  filter_upwards [hBScale, hMScale, eventually_ge_atTop (6 : Real)] with x hbs hms hx
  have hx0 : 0 < x := by linarith
  have hl1 : 1 <= Real.log x :=
    ((Real.lt_log_iff_exp_lt hx0).mpr
      (Real.exp_one_lt_three.trans_le (by linarith))).le
  have hl : 0 < Real.log x := by linarith
  let P := x ^ (b / 2)
  let Q := Real.sqrt (Real.log x)
  let h := nicolasCriticalWindowLength eta b x
  have hp : 0 < P := Real.rpow_pos_of_pos hx0 _
  have hq : 0 < Q := Real.sqrt_pos.mpr hl
  have hqSquare : Q ^ (2 : Nat) = Real.log x := Real.sq_sqrt hl.le
  have hpSquare : P ^ (2 : Nat) = x ^ b := by
    dsimp [P]
    rw [pow_two, <- Real.rpow_add hx0]
    congr 1
    ring
  have hh : h = eta * x / (P * Q) := rfl
  have hh0 : 0 < h := by rw [hh]; positivity
  have hPower : x ^ (1 - b) = x / P ^ (2 : Nat) := by
    rw [hpSquare, Real.rpow_sub hx0, Real.rpow_one]
  have hBase : B * x ^ (1 - b) <= h := by
    have ht := mul_le_mul_of_nonneg_right hbs.le
      (show 0 <= x / (P * Q) by positivity)
    change (B * (Q / P)) * (x / (P * Q)) <= eta * (x / (P * Q)) at ht
    have hLeft : (B * (Q / P)) * (x / (P * Q)) = B * x ^ (1 - b) := by
      rw [hPower]
      field_simp
    have hRight : eta * (x / (P * Q)) = h := by rw [hh]; ring
    rwa [hLeft, hRight] at ht
  have hMIdentity : 4 * h * Real.log x = (4 * eta * (Q / P)) * x := by
    rw [hh, <- hqSquare]
    field_simp
  have hM : 4 * h * Real.log x <= x / 2 := by
    have ht := mul_le_mul_of_nonneg_right hms.le hx0.le
    change (4 * eta * (Q / P)) * x <= (1 / 2 : Real) * x at ht
    rw [hMIdentity]
    linarith
  have hhX : h <= x := by
    have ht := mul_le_mul_of_nonneg_left hl1 hh0.le
    nlinarith
  have hSquare : h ^ (2 : Nat) * Real.log x =
      eta ^ (2 : Nat) * x ^ (2 : Nat) * x ^ (-b) := by
    rw [hh, div_pow, mul_pow, mul_pow, <- hqSquare, hpSquare,
      Real.rpow_neg hx0.le]
    field_simp
  have hLossIdentity :
      (2 * (4 * h * Real.log x) * h + 6 * (4 * h * Real.log x) ^ (2 : Nat)) /
        (x ^ (2 : Nat) * Real.log x) =
        (8 / Real.log x + 96) * eta ^ (2 : Nat) * x ^ (-b) := by
    have hNum : 2 * (4 * h * Real.log x) * h + 6 * (4 * h * Real.log x) ^ (2 : Nat) =
        (h ^ (2 : Nat) * Real.log x) * (8 + 96 * Real.log x) := by ring
    rw [hNum, hSquare]
    field_simp
  have hInv : 1 / Real.log x <= 1 := by
    have ht := div_le_div_of_nonneg_left (by norm_num : (0 : Real) <= 1)
      (by norm_num : (0 : Real) < 1) hl1
    simpa only [div_one] using ht
  refine And.intro hx (And.intro hh0 (And.intro hBase (And.intro hM (And.intro hhX ?_))))
  change (2 * (4 * h * Real.log x) * h + 6 * (4 * h * Real.log x) ^ (2 : Nat)) /
      (x ^ (2 : Nat) * Real.log x) <= _
  rw [hLossIdentity]
  have hEight : 8 / Real.log x <= (8 : Real) := by
    calc
      _ = 8 * (1 / Real.log x) := by ring
      _ <= 8 * 1 := mul_le_mul_of_nonneg_left hInv (by norm_num)
      _ = _ := by norm_num
  have ht := mul_le_mul_of_nonneg_right
    (show 8 / Real.log x + 96 <= (104 : Real) by linarith only [hEight])
    (show 0 <= eta ^ (2 : Nat) * x ^ (-b) by positivity)
  simpa only [mul_assoc] using ht

theorem nicolasLog_critical_intervals_of_zero
    {rho : Complex} (hZero : riemannZeta rho = 0)
    (hHalf : (1 / 2 : Real) < rho.re) (hOne : rho.re < 1)
    {b : Real} (hLower : 1 - rho.re < b) (hbHalf : b <= 1 / 2)
    (A X : Real) (hA : 0 < A) :
    exists n : Nat, X < (n : Real) /\ 6 <= n /\
      forall y : Real, (n : Real) <= y ->
        y <= n + nicolasCriticalWindowLength (Real.sqrt A / 100) b n ->
          A * (n : Real) ^ (-b) < nicolasLogMertensOscillation y := by
  have hb : 0 < b := by linarith
  let eta := Real.sqrt A / 100
  have he : 0 < eta := div_pos (Real.sqrt_pos.mpr hA) (by norm_num)
  have hLossConst : 104 * eta ^ (2 : Nat) < A := by
    dsimp [eta]
    have hsq := Real.sq_sqrt hA.le
    nlinarith
  have hSmall := eventually_nicolasCriticalWindow_bounds (4 * A + 1) b eta (by positivity) hb he
  choose Y hY using eventually_atTop.mp hSmall
  choose N hN using exists_nat_gt (max X Y)
  choose j hj hjTwo hPeak hE hError using
    exists_nicolasK_power_peak_of_zero hZero hHalf hOne hLower hbHalf
      (2 * A) (by positivity) N
  have hjCast : (N : Real) <= j := by exact_mod_cast hj
  have hnX : X < ((j + 1 : Nat) : Real) := by
    simp only [Nat.cast_add, Nat.cast_one]
    linarith [le_max_left X Y]
  have hnY : Y <= ((j + 1 : Nat) : Real) := by
    simp only [Nat.cast_add, Nat.cast_one]
    linarith [le_max_right X Y]
  let x : Real := (j + 1 : Nat)
  let h := nicolasCriticalWindowLength eta b x
  let M := 4 * h * Real.log x
  have hData := hY x hnY
  have hx0 : 0 < x := by linarith [hData.1]
  have hLogHalf : 1 <= Real.log (x / 2) := by
    apply le_of_lt
    apply (Real.lt_log_iff_exp_lt (by linarith : 0 < x / 2)).mpr
    exact Real.exp_one_lt_three.trans_le (by linarith [hData.1])
  have hLog : 1 <= Real.log x :=
    hLogHalf.trans (Real.log_le_log (by positivity) (by linarith : x / 2 <= x))
  have hh0 : 0 < h := hData.2.1
  have hM : 0 <= M := by dsimp [M]; positivity
  have hnSix : 6 <= j + 1 := by
    exact_mod_cast (show (6 : Real) <= ((j + 1 : Nat) : Real) from hData.1)
  refine Exists.intro (j + 1) (And.intro hnX (And.intro hnSix ?_))
  intro y hyLower hyUpper
  have hControl : forall t : Real, x <= t -> t <= y -> abs (Chebyshev.theta t - t) <= M := by
    intro t htl htu
    have hEn : 0 <= nicolasThetaError x := by
      simpa only [x, Nat.cast_add, Nat.cast_one] using hE.le
    have ht := Chebyshev.theta_error_abs_le_of_nat_window (j + 1)
      (by omega) h t
      hLog hEn hData.2.1.le hData.2.2.2.2.1 htl (htu.trans hyUpper)
    change abs (Chebyshev.theta t - t) <= nicolasThetaError x + 3 * h * Real.log x at ht
    have hErr : nicolasThetaError x <= (4 * A + 1) * x ^ (1 - b) * Real.log x := by
      dsimp [x]
      simp only [Nat.cast_add, Nat.cast_one]
      convert hError using 1
      ring
    have hBase := mul_le_mul_of_nonneg_right hData.2.2.1 (by linarith : 0 <= Real.log x)
    change (4 * A + 1) * x ^ (1 - b) * Real.log x <= h * Real.log x at hBase
    dsimp [M]
    linarith
  have hBound := nicolasLog_interval_lower_bound x y M
    (by linarith [hData.1]) hLogHalf hyLower hM hData.2.2.2.1 hControl
  have hLoss : (2 * M * (y - x) + 6 * M ^ (2 : Nat)) / (x ^ (2 : Nat) * Real.log x) <=
      104 * eta ^ (2 : Nat) * x ^ (-b) := by
    apply le_trans ?_ hData.2.2.2.2.2
    apply div_le_div_of_nonneg_right ?_ (by positivity)
    have ht := mul_le_mul_of_nonneg_left (show y - x <= h by linarith only [hyUpper])
      (show 0 <= 2 * M by positivity)
    linarith
  have hPeakX : 2 * A * x ^ (-b) < nicolasK x := by
    simpa only [x, Nat.cast_add, Nat.cast_one] using hPeak
  have hLossStrict := mul_lt_mul_of_pos_right hLossConst (Real.rpow_pos_of_pos hx0 (-b))
  change A * x ^ (-b) < nicolasLogMertensOscillation y
  linarith


theorem nicolasCriticalWindowLength_eq_rpow
    (eta b x : Real) (hx : 0 < x) :
    nicolasCriticalWindowLength eta b x =
      eta * x ^ (1 - b / 2) / Real.sqrt (Real.log x) := by
  rw [nicolasCriticalWindowLength, Real.rpow_sub hx, Real.rpow_one]
  ring

theorem exists_nicolasLog_critical_intervals_of_not_RH
    (hNotRH : Not RiemannHypothesis) :
    exists b : Real, 0 < b /\ b < 1 / 2 /\
      forall A X : Real, 0 < A ->
        exists n : Nat, X < (n : Real) /\ 6 <= n /\
          forall y : Real, (n : Real) <= y ->
            y <= n + nicolasCriticalWindowLength (Real.sqrt A / 100) b n ->
              A * (n : Real) ^ (-b) < nicolasLogMertensOscillation y := by
  choose rho hZero hHalf hOne using
    exists_riemannZeta_zero_re_gt_half_of_not_riemannHypothesis hNotRH
  let b : Real := ((1 - rho.re) + 1 / 2) / 2
  have hb : 0 < b := by dsimp [b]; linarith
  have hbHalf : b < 1 / 2 := by dsimp [b]; linarith
  have hLower : 1 - rho.re < b := by dsimp [b]; linarith
  exact Exists.intro b (And.intro hb (And.intro hbHalf
    (fun A X hA => nicolasLog_critical_intervals_of_zero
      hZero hHalf hOne hLower hbHalf.le A X hA)))

end PrimeFactorOscillations

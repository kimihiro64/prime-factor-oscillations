/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.NicolasIntervalPersistence
import PrimeFactorOscillations.Helpers.NicolasNegativeLimit
import PrimeFactorOscillations.Helpers.NicolasPowerPeakSupply
import PrimeFactorOscillations.Mathlib.NumberTheory.Chebyshev.IntervalIncrement

/-!
# Positive power intervals forced by an off-line zeta zero

The exact finite theta envelope and its integral/quadratic losses become
negligible on every window of length x^d with d < 1 - b/2. Simultaneous
integer peaks therefore yield positive Nicolas excursions throughout entire
arbitrarily late intervals. The exponent precedes all amplitudes and cutoffs.
No prime-gap hypothesis or independent RH estimate enters this result.
-/

set_option autoImplicit false
set_option Elab.async false

noncomputable section

namespace PrimeFactorOscillations

open Filter Robin1984

def nicolasPersistenceEnvelope (B b d x : Real) : Real :=
  (B * x ^ (1 - b) + 3 * x ^ d) * Real.log x

def nicolasPersistenceLoss (B b d x : Real) : Real :=
  (2 * nicolasPersistenceEnvelope B b d x * x ^ d +
    6 * (nicolasPersistenceEnvelope B b d x) ^ (2 : Nat)) /
    (x ^ (2 : Nat) * Real.log x)

theorem nicolasPersistenceEnvelope_div (B b d x : Real) (hx : 0 < x) :
    nicolasPersistenceEnvelope B b d x / x =
      B * x ^ (-b) * Real.log x + 3 * x ^ (d - 1) * Real.log x := by
  have h1 : x ^ (1 - b) / x = x ^ (-b) := by
    calc
      _ = x ^ (1 - b) / x ^ (1 : Real) := by rw [Real.rpow_one]
      _ = _ := by rw [<- Real.rpow_sub hx]; congr 1; ring
  have h2 : x ^ d / x = x ^ (d - 1) := by
    calc
      _ = x ^ d / x ^ (1 : Real) := by rw [Real.rpow_one]
      _ = _ := by rw [<- Real.rpow_sub hx]
  calc
    _ = B * (x ^ (1 - b) / x) * Real.log x +
      3 * (x ^ d / x) * Real.log x := by
        unfold nicolasPersistenceEnvelope
        ring
    _ = _ := by rw [h1, h2]

theorem nicolasPersistenceLoss_normalize (B b d x : Real) (hx : 1 < x) :
    nicolasPersistenceLoss B b d x * x ^ b =
      2 * B * x ^ (d - 1) + 6 * x ^ (b + 2 * d - 2) +
        6 * B ^ (2 : Nat) * (x ^ (-b) * Real.log x) +
        36 * B * (x ^ (d - 1) * Real.log x) +
        54 * (x ^ (b + 2 * d - 2) * Real.log x) := by
  have hxPos : 0 < x := by linarith
  have hLog : Not (Real.log x = 0) := (Real.log_pos hx).ne'
  have hCross : x ^ (1 - b) * x ^ d * x ^ b / x ^ (2 : Nat) =
      x ^ (d - 1) := by
    rw [<- Real.rpow_natCast, <- Real.rpow_add hxPos, <- Real.rpow_add hxPos,
      <- Real.rpow_sub hxPos]
    congr 1
    ring
  have hFirst : (x ^ (1 - b)) ^ (2 : Nat) * x ^ b / x ^ (2 : Nat) =
      x ^ (-b) := by
    simp only [<- Real.rpow_natCast]
    rw [<- Real.rpow_mul hxPos.le, <- Real.rpow_add hxPos, <- Real.rpow_sub hxPos]
    congr 1
    ring
  have hSecond : (x ^ d) ^ (2 : Nat) * x ^ b / x ^ (2 : Nat) =
      x ^ (b + 2 * d - 2) := by
    simp only [<- Real.rpow_natCast]
    rw [<- Real.rpow_mul hxPos.le, <- Real.rpow_add hxPos, <- Real.rpow_sub hxPos]
    congr 1
    ring
  calc
    _ = (2 * B + 36 * B * Real.log x) *
          (x ^ (1 - b) * x ^ d * x ^ b / x ^ (2 : Nat)) +
        (6 + 54 * Real.log x) * ((x ^ d) ^ (2 : Nat) * x ^ b / x ^ (2 : Nat)) +
        (6 * B ^ (2 : Nat) * Real.log x) *
          ((x ^ (1 - b)) ^ (2 : Nat) * x ^ b / x ^ (2 : Nat)) := by
      unfold nicolasPersistenceLoss nicolasPersistenceEnvelope
      field_simp [hxPos.ne', hLog]
      ring
    _ = _ := by rw [hCross, hFirst, hSecond]; ring

theorem tendsto_nicolasPersistenceEnvelope_div (B b d : Real)
    (hb : 0 < b) (hd : d < 1) :
    Tendsto (fun x : Real => nicolasPersistenceEnvelope B b d x / x)
      atTop (nhds 0) := by
  have hLogPower : forall e : Real, e < 0 ->
      Tendsto (fun x : Real => x ^ e * Real.log x) atTop (nhds 0) := by
    intro e he
    have h := (isLittleO_log_rpow_atTop (by linarith : 0 < -e)).tendsto_div_nhds_zero
    apply h.congr'
    filter_upwards [eventually_gt_atTop (0 : Real)] with x hx
    rw [Real.rpow_neg hx.le]
    field_simp
  have h := ((hLogPower (-b) (by linarith)).const_mul B).add
    ((hLogPower (d - 1) (by linarith)).const_mul 3)
  have hZero : B * 0 + 3 * (0 : Real) = 0 := by ring
  rw [hZero] at h
  apply h.congr'
  filter_upwards [eventually_gt_atTop (0 : Real)] with x hx
  rw [nicolasPersistenceEnvelope_div B b d x hx]
  ring

theorem tendsto_nicolasPersistenceLoss_normalized (B b d : Real)
    (hb : 0 < b) (hd : d < 1 - b / 2) :
    Tendsto (fun x : Real => nicolasPersistenceLoss B b d x * x ^ b)
      atTop (nhds 0) := by
  have hdOne : d < 1 := by linarith
  have hTail : b + 2 * d - 2 < 0 := by linarith
  have hPower : forall e : Real, e < 0 ->
      Tendsto (fun x : Real => x ^ e) atTop (nhds 0) := by
    intro e he
    simpa only [neg_neg] using tendsto_rpow_neg_atTop (by linarith : 0 < -e)
  have hLogPower : forall e : Real, e < 0 ->
      Tendsto (fun x : Real => x ^ e * Real.log x) atTop (nhds 0) := by
    intro e he
    have h := (isLittleO_log_rpow_atTop (by linarith : 0 < -e)).tendsto_div_nhds_zero
    apply h.congr'
    filter_upwards [eventually_gt_atTop (0 : Real)] with x hx
    rw [Real.rpow_neg hx.le]
    field_simp
  have h := (((((hPower (d - 1) (by linarith)).const_mul (2 * B)).add
    ((hPower (b + 2 * d - 2) hTail).const_mul 6)).add
    ((hLogPower (-b) (by linarith)).const_mul (6 * B ^ (2 : Nat)))).add
    ((hLogPower (d - 1) (by linarith)).const_mul (36 * B))).add
    ((hLogPower (b + 2 * d - 2) hTail).const_mul 54)
  simp only [mul_zero, add_zero] at h
  apply h.congr'
  filter_upwards [eventually_gt_atTop (1 : Real)] with x hx
  exact (nicolasPersistenceLoss_normalize B b d x hx).symm

theorem eventually_nicolasPersistence_small (B b d A : Real)
    (hb : 0 < b) (hd : d < 1 - b / 2) (hA : 0 < A) :
    Filter.Eventually (fun x : Real =>
      6 <= x /\ nicolasPersistenceEnvelope B b d x <= x / 2 /\
      nicolasPersistenceLoss B b d x < A * x ^ (-b)) atTop := by
  have hEnvelope := (tendsto_nicolasPersistenceEnvelope_div B b d hb
    (by linarith)).eventually_lt_const (by norm_num : (0 : Real) < 1 / 2)
  have hLoss := (tendsto_nicolasPersistenceLoss_normalized B b d hb hd).eventually_lt_const hA
  filter_upwards [hEnvelope, hLoss, eventually_ge_atTop (6 : Real)] with x he hl hx
  have hxPos : 0 < x := by linarith
  have hProduct : x ^ b * x ^ (-b) = 1 := by
    rw [<- Real.rpow_add hxPos]
    simp
  refine And.intro hx (And.intro ?_ ?_)
  . have h := mul_lt_mul_of_pos_right he hxPos
    have hCancel : (nicolasPersistenceEnvelope B b d x / x) * x =
        nicolasPersistenceEnvelope B b d x := by field_simp [hxPos.ne']
    rw [hCancel] at h
    linarith
  . calc
      nicolasPersistenceLoss B b d x =
          (nicolasPersistenceLoss B b d x * x ^ b) * x ^ (-b) := by
        rw [mul_assoc, hProduct, mul_one]
      _ < A * x ^ (-b) :=
        mul_lt_mul_of_pos_right hl (Real.rpow_pos_of_pos hxPos _)

theorem nicolasLog_lower_on_nat_power_window
    (n : Nat) (hn : (6 : Real) <= n) (B b d A : Real)
    (hB : 0 <= B) (hd : d <= 1)
    (hE : 0 <= nicolasThetaError (n : Real))
    (hError : nicolasThetaError (n : Real) <=
      B * (n : Real) ^ (1 - b) * Real.log (n : Real))
    (hPeak : (2 * A) * (n : Real) ^ (-b) < nicolasK (n : Real))
    (hSmall : nicolasPersistenceEnvelope B b d (n : Real) <= (n : Real) / 2)
    (hLoss : nicolasPersistenceLoss B b d (n : Real) <
      A * (n : Real) ^ (-b))
    (y : Real) (hyLower : (n : Real) <= y)
    (hyUpper : y <= n + (n : Real) ^ d) :
    A * (n : Real) ^ (-b) < nicolasLogMertensOscillation y := by
  let x : Real := n
  let M : Real := nicolasPersistenceEnvelope B b d x
  have hxPos : 0 < x := by dsimp [x]; linarith
  have hxSix : 6 <= x := hn
  have hxOne : 1 <= x := by linarith
  have hLogHalf : 1 <= Real.log (x / 2) := by
    apply le_of_lt
    apply (Real.lt_log_iff_exp_lt (by positivity : 0 < x / 2)).mpr
    exact Real.exp_one_lt_three.trans_le (by linarith)
  have hLog : 1 <= Real.log x :=
    hLogHalf.trans (Real.log_le_log (by positivity) (by linarith : x / 2 <= x))
  have hLength : x ^ d <= x := by
    simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le hxOne hd
  have hM : 0 <= M := by
    dsimp [M, nicolasPersistenceEnvelope]
    positivity
  have hControl : forall t : Real, x <= t -> t <= y ->
      abs (Chebyshev.theta t - t) <= M := by
    intro t htLower htUpper
    have h := Chebyshev.theta_error_abs_le_of_nat_window n
      (by exact_mod_cast (show (3 : Real) <= n by linarith)) (x ^ d) t
      hLog hE (Real.rpow_nonneg hxPos.le _) hLength htLower
      (htUpper.trans hyUpper)
    apply h.trans
    change nicolasThetaError x + 3 * x ^ d * Real.log x <= M
    dsimp [M, nicolasPersistenceEnvelope]
    change nicolasThetaError x <= B * x ^ (1 - b) * Real.log x at hError
    nlinarith only [hError]
  have hLower := nicolasLog_interval_lower_bound x y M
    (by linarith) hLogHalf hyLower hM hSmall hControl
  have hLossCompare :
      (2 * M * (y - x) + 6 * M ^ (2 : Nat)) / (x ^ (2 : Nat) * Real.log x) <=
        nicolasPersistenceLoss B b d x := by
    unfold nicolasPersistenceLoss
    change (2 * M * (y - x) + 6 * M ^ (2 : Nat)) / (x ^ (2 : Nat) * Real.log x) <=
      (2 * M * x ^ d + 6 * M ^ (2 : Nat)) / (x ^ (2 : Nat) * Real.log x)
    apply div_le_div_of_nonneg_right ?_ (by positivity)
    have h := mul_le_mul_of_nonneg_left
      (show y - x <= x ^ d by linarith only [hyUpper])
      (show 0 <= 2 * M by positivity)
    linarith only [h]
  change 2 * A * x ^ (-b) < nicolasK x at hPeak
  change nicolasPersistenceLoss B b d x < A * x ^ (-b) at hLoss
  nlinarith only [hPeak, hLoss, hLossCompare, hLower]

/-- Every admissible off-line zero forces arbitrarily late positive intervals
of any fixed power length below the persistence threshold. -/
theorem nicolasLog_power_intervals_of_zero
    {rho : Complex} (hZero : riemannZeta rho = 0)
    (hHalf : (1 / 2 : Real) < rho.re) (hOne : rho.re < 1)
    {b : Real} (hLower : 1 - rho.re < b) (hbHalf : b <= 1 / 2)
    (d A X : Real) (hd : d < 1 - b / 2) (hA : 0 < A) :
    exists n : Nat, X < (n : Real) /\ 6 <= n /\
      forall y : Real, (n : Real) <= y -> y <= n + (n : Real) ^ d ->
        A * (n : Real) ^ (-b) < nicolasLogMertensOscillation y := by
  have hb : 0 < b := by linarith
  have hSmall := eventually_nicolasPersistence_small (4 * A + 1) b d A hb hd hA
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
  have hs := hY ((j + 1 : Nat) : Real) hnY
  refine Exists.intro (j + 1) (And.intro hnX (And.intro
    (by exact_mod_cast hs.1) ?_))
  intro y hyl hyu
  apply nicolasLog_lower_on_nat_power_window (j + 1) hs.1 (4 * A + 1) b d A
    (by positivity) (by linarith) ?_ ?_ ?_ hs.2.1 hs.2.2 y hyl hyu
  . simpa only [Nat.cast_add, Nat.cast_one] using hE.le
  . simp only [Nat.cast_add, Nat.cast_one]
    convert hError using 1
    ring
  . simpa only [Nat.cast_add, Nat.cast_one] using hPeak

/-- Under false RH, one exponent works for every admissible window power,
positive amplitude and endpoint cutoff. -/
theorem exists_nicolasLog_power_intervals_of_not_RH
    (hNotRH : Not RiemannHypothesis) :
    exists b : Real, 0 < b /\ b < 1 / 2 /\
      forall d A X : Real, d < 1 - b / 2 -> 0 < A ->
        exists n : Nat, X < (n : Real) /\ 6 <= n /\
          forall y : Real, (n : Real) <= y -> y <= n + (n : Real) ^ d ->
            A * (n : Real) ^ (-b) < nicolasLogMertensOscillation y := by
  choose rho hZero hHalf hOne using
    exists_riemannZeta_zero_re_gt_half_of_not_riemannHypothesis hNotRH
  let b : Real := ((1 - rho.re) + 1 / 2) / 2
  have hb : 0 < b := by dsimp [b]; linarith
  have hbHalf : b < 1 / 2 := by dsimp [b]; linarith
  have hLower : 1 - rho.re < b := by dsimp [b]; linarith
  exact Exists.intro b (And.intro hb (And.intro hbHalf
    (fun d A X hd hA => nicolasLog_power_intervals_of_zero
      hZero hHalf hOne hLower hbHalf.le d A X hd hA)))

end PrimeFactorOscillations

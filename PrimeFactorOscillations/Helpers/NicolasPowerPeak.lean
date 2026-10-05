/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.NicolasPeakSupply
import PrimeFactorOscillations.Helpers.NicolasPowerExcursions

/-!
# Power excursions of the corrected Nicolas logarithm

An actual discrete peak above a power profile controls the theta endpoint
error and its nonlinear log-log correction without assuming RH. Exact unit
rounding and the proved Landau integral excursions then give both signs,
with every amplitude, for the corrected finite-product logarithm at every
admissible zero-dependent exponent. These are centered-error excursions;
no fixed-rank raw ascent or improved prime-gap supply is asserted.
-/

set_option autoImplicit false
set_option Elab.async false

noncomputable section

namespace PrimeFactorOscillations

open MeasureTheory Set Robin1984 Filter

/-- A peak above a power profile bounds the actual theta error without RH. -/
theorem nicolasThetaError_bounds_of_power_peak
    (n : Nat) (hn : 2 <= n) (b A : Real) (hb : 0 < b) (hbOne : b <= 1) (hA : 0 < A)
    (hLeft : nicolasK (n : Real) - A * (n : Real) ^ (-b) <=
      nicolasK ((n : Real) + 1) - A * ((n : Real) + 1) ^ (-b))
    (hRight : nicolasK ((n : Real) + 2) - A * ((n : Real) + 2) ^ (-b) <=
      nicolasK ((n : Real) + 1) - A * ((n : Real) + 1) ^ (-b)) :
    0 < nicolasThetaError ((n : Real) + 1) /\
      nicolasThetaError ((n : Real) + 1) <=
        (2 * A + 1) * ((n : Real) + 1) ^ (1 - b) *
          Real.log ((n : Real) + 1) := by
  have hnTwo : (2 : Real) <= n := by exact_mod_cast hn
  have hnOne : 1 < (n : Real) := by linarith
  have hnPos : 0 < (n : Real) := by linarith
  let x : Real := (n : Real) + 1
  have hxPos : 0 < x := by dsimp [x]; linarith
  have hxOne : 1 < x := by dsimp [x]; linarith
  have hRatioOne : 1 <= x / (n : Real) := by
    have h : (n : Real) <= x := by dsimp [x]; linarith
    have hDivide := div_le_div_of_nonneg_right h hnPos.le
    simpa only [div_self hnPos.ne'] using hDivide
  have hRatioPower := Real.rpow_le_rpow_of_exponent_le hRatioOne hbOne
  rw [Real.div_rpow hxPos.le hnPos.le, Real.rpow_one] at hRatioPower
  have hnPowerPos : 0 < (n : Real) ^ b := Real.rpow_pos_of_pos hnPos _
  have hxPowerPos : 0 < x ^ b := Real.rpow_pos_of_pos hxPos _
  have hInvPower : (n : Real) ^ (-b) <= (x / (n : Real)) * x ^ (-b) := by
    have h := div_le_div_of_nonneg_right hRatioPower hxPowerPos.le
    rw [Real.rpow_neg hnPos.le, Real.rpow_neg hxPos.le]
    convert h using 1 <;> field_simp [hxPowerPos.ne', hnPowerPos.ne', hnPos.ne']
  have hRatioNormalize : (x / (n : Real)) * x ^ (-b) - x ^ (-b) =
      x ^ (-b) / (n : Real) := by
    dsimp [x]
    field_simp [hnPos.ne']
    ring
  have hDifference : (n : Real) ^ (-b) - x ^ (-b) <=
      x ^ (-b) / (n : Real) := by linarith only [hInvPower, hRatioNormalize]
  have hPower : x ^ (1 - b) = x * x ^ (-b) := by
    rw [sub_eq_add_neg, Real.rpow_add hxPos, Real.rpow_one]
  let B : Real := A * x ^ (1 - b)
  have hB : 0 <= B := by dsimp [B]; positivity
  have hNormalize : A * (x ^ (-b) / (n : Real)) =
      B / (x * (n : Real)) := by
    dsimp [B]
    rw [hPower]
    field_simp [hxPos.ne', hnPos.ne']
  have hDrop : A * (n : Real) ^ (-b) - A * x ^ (-b) <=
      B / (x * (n : Real)) := by
    have h := mul_le_mul_of_nonneg_left hDifference hA.le
    rw [hNormalize] at h
    nlinarith only [h]
  have hLeftIntegral : intervalIntegral (fun t : Real => (Chebyshev.theta t - t) *
      ((1 / Real.log t + 1 / (Real.log t) ^ 2) / t ^ 2))
      (n : Real) ((n : Real) + 1) volume <=
      B / (((n : Real) + 1) * (n : Real)) := by
    rw [<- nicolasK_sub_eq_intervalIntegral hnTwo (by linarith)]
    change nicolasK (n : Real) - nicolasK x <= B / (x * (n : Real))
    change nicolasK (n : Real) - A * (n : Real) ^ (-b) <=
      nicolasK x - A * x ^ (-b) at hLeft
    linarith only [hLeft, hDrop]
  have hStrictPower : ((n : Real) + 2) ^ (-b) < x ^ (-b) := by
    apply Real.rpow_lt_rpow_of_neg hxPos
    . dsimp [x]
      linarith
    . linarith
  have hPositiveDrop : 0 < A * (x ^ (-b) - ((n : Real) + 2) ^ (-b)) :=
    mul_pos hA (sub_pos.mpr hStrictPower)
  have hRightIntegral : 0 < intervalIntegral (fun t : Real => (Chebyshev.theta t - t) *
      ((1 / Real.log t + 1 / (Real.log t) ^ 2) / t ^ 2))
      ((n : Real) + 1) (((n : Real) + 1) + 1) volume := by
    rw [<- nicolasK_sub_eq_intervalIntegral (by linarith : (2 : Real) <= (n : Real) + 1)
      (by linarith)]
    rw [show (n : Real) + 1 + 1 = (n : Real) + 2 by ring]
    change nicolasK ((n : Real) + 2) - A * ((n : Real) + 2) ^ (-b) <=
      nicolasK x - A * x ^ (-b) at hRight
    change 0 < nicolasK x - nicolasK ((n : Real) + 2)
    nlinarith only [hRight, hPositiveDrop]
  have hErrorPos := Chebyshev.theta_error_pos_of_unit_integral_pos
    (n + 1) (by simp only [Nat.cast_add, Nat.cast_one]; linarith)
    (by simpa only [Nat.cast_add, Nat.cast_one] using hRightIntegral)
  have hErrorUpper := Chebyshev.theta_error_succ_le_of_unit_integral_le
    n hnOne B hB hLeftIntegral
  simp only [Nat.cast_add, Nat.cast_one] at hErrorPos hErrorUpper
  have hPowerOne : 1 <= x ^ (1 - b) := by
    simpa only [Real.one_rpow] using Real.rpow_le_rpow
      (by norm_num : (0 : Real) <= 1) hxOne.le (by linarith : 0 <= 1 - b)
  have hCoefficient : 2 * B + 1 <= (2 * A + 1) * x ^ (1 - b) := by
    dsimp [B]
    nlinarith only [hPowerOne]
  have hScaled := mul_le_mul_of_nonneg_right hCoefficient (Real.log_pos hxOne).le
  exact And.intro hErrorPos (hErrorUpper.trans hScaled)

/-- The finite Nicolas logarithm retains a quadratically smaller loss at a
power-profile peak. This uses no RH assumption. -/
theorem nicolasLog_lower_of_power_peak
    (n : Nat) (hn : 2 <= n) (b A : Real) (hb : 0 < b) (hbOne : b <= 1) (hA : 0 < A)
    (hLeft : nicolasK (n : Real) - A * (n : Real) ^ (-b) <=
      nicolasK ((n : Real) + 1) - A * ((n : Real) + 1) ^ (-b))
    (hRight : nicolasK ((n : Real) + 2) - A * ((n : Real) + 2) ^ (-b) <=
      nicolasK ((n : Real) + 1) - A * ((n : Real) + 1) ^ (-b)) :
    nicolasK ((n : Real) + 1) -
      (2 * A + 1) ^ (2 : Nat) *
        (Real.log ((n : Real) + 1) + 1) * ((n : Real) + 1) ^ (-2 * b) / 2 <=
      nicolasLogMertensOscillation ((n : Real) + 1) := by
  have hError := nicolasThetaError_bounds_of_power_peak n hn b A hb hbOne hA hLeft hRight
  have hnTwo : (2 : Real) <= n := by exact_mod_cast hn
  let x : Real := (n : Real) + 1
  have hxPos : 0 < x := by dsimp [x]; linarith
  have hLoss := Real.logLog_remainder_le_of_displacement_le_log x
    (nicolasThetaError x) ((2 * A + 1) * x ^ (1 - b))
    (by dsimp [x]; linarith) hError.1.le (by positivity) hError.2
  have hHeight : x + nicolasThetaError x = Chebyshev.theta x := by
    unfold nicolasThetaError
    ring
  rw [hHeight] at hLoss
  have hPower : (x ^ (1 - b)) ^ (2 : Nat) =
      x ^ (2 : Nat) * x ^ (-2 * b) := by
    rw [<- Real.rpow_natCast, <- Real.rpow_mul hxPos.le,
      <- Real.rpow_natCast, <- Real.rpow_add hxPos]
    congr 1
    ring
  have hNormalize : ((2 * A + 1) * x ^ (1 - b)) ^ (2 : Nat) *
      (Real.log x + 1) / (2 * x ^ (2 : Nat)) =
      (2 * A + 1) ^ (2 : Nat) * (Real.log x + 1) * x ^ (-2 * b) / 2 := by
    rw [mul_pow, hPower]
    field_simp [hxPos.ne']
  rw [hNormalize] at hLoss
  have hEuler := nicolasMertensSummandRemainder_nonneg x
  rw [nicolasLogMertensOscillation_eq_components (by linarith)]
  change nicolasK x -
    (2 * A + 1) ^ (2 : Nat) * (Real.log x + 1) * x ^ (-2 * b) / 2 <= _
  linarith only [hLoss, hEuler]


/-- Unbounded power excursions of the actual theta integral survive its
nonlinear endpoint correction. The source hypotheses concern that integral. -/
theorem nicolasLog_power_unbounded_of_K_integer_excursions
    (b : Real) (hb : 0 < b) (hbOne : b <= 1)
    (hPositive : forall A : Real, 0 < A -> forall N : Nat,
      exists n : Nat, N <= n /\ A * (n : Real) ^ (-b) < nicolasK (n : Real))
    (hNegative : forall N : Nat,
      exists n : Nat, N <= n /\ nicolasK (n : Real) < 0)
    (C : Real) (N : Nat) :
    exists m : Nat, N <= m /\
      C * (m : Real) ^ (-b) < nicolasLogMertensOscillation (m : Real) := by
  let A : Real := max C 0 + 1
  have hA : 0 < A := by dsimp [A]; linarith [le_max_right C 0]
  have hReserve : C + 1 <= A := by dsimp [A]; linarith [le_max_left C 0]
  let B : Real := 2 * A + 1
  let T : Real := B ^ (2 : Nat) * (2 / b + 1) / 2
  have hB : 0 < B := by dsimp [B]; linarith
  have hT : 0 < T := by dsimp [T]; positivity
  have hDecay : Tendsto (fun x : Real => x ^ (-(b / 2))) atTop (nhds 0) :=
    tendsto_rpow_neg_atTop (by linarith)
  have hSmall := hDecay.eventually_lt_const (inv_pos.mpr hT)
  have hLoss : Filter.Eventually (fun x : Real =>
      B ^ (2 : Nat) * (Real.log x + 1) * x ^ (-2 * b) / 2 < x ^ (-b)) atTop := by
    filter_upwards [hSmall, eventually_gt_atTop (1 : Real)] with x hSmallX hx
    have hxPos : 0 < x := by linarith
    have hLog := Real.log_le_rpow_div hxPos.le (by linarith : 0 < b / 2)
    have hHalfPower : 1 <= x ^ (b / 2) := by
      simpa only [Real.one_rpow] using Real.rpow_le_rpow
        (by norm_num : (0 : Real) <= 1) hx.le (by linarith : 0 <= b / 2)
    have hDiv : x ^ (b / 2) / (b / 2) = (2 / b) * x ^ (b / 2) := by ring
    rw [hDiv] at hLog
    have hLogBound : Real.log x + 1 <= (2 / b + 1) * x ^ (b / 2) := by
      nlinarith only [hLog, hHalfPower]
    have hProduct := mul_le_mul_of_nonneg_left hLogBound
      (show 0 <= B ^ (2 : Nat) * x ^ (-2 * b) / 2 by positivity)
    have hPowers : x ^ (b / 2) * x ^ (-2 * b) =
        x ^ (-(b / 2)) * x ^ (-b) := by
      rw [<- Real.rpow_add hxPos, <- Real.rpow_add hxPos]
      congr 1
      ring
    have hLossBound :
        B ^ (2 : Nat) * (Real.log x + 1) * x ^ (-2 * b) / 2 <=
          (T * x ^ (-(b / 2))) * x ^ (-b) := by
      calc
        _ <= B ^ (2 : Nat) * ((2 / b + 1) * x ^ (b / 2)) * x ^ (-2 * b) / 2 := by
          nlinarith only [hProduct]
        _ = T * (x ^ (b / 2) * x ^ (-2 * b)) := by dsimp [T]; ring
        _ = _ := by rw [hPowers]; ring
    have hTCancel : T * Inv.inv T = 1 := by field_simp [hT.ne']
    have hScaled := mul_lt_mul_of_pos_left hSmallX hT
    rw [hTCancel] at hScaled
    have hFinal := mul_lt_mul_of_pos_right hScaled (Real.rpow_pos_of_pos hxPos (-b))
    simpa only [one_mul] using hLossBound.trans_lt hFinal
  choose X hX using eventually_atTop.mp hLoss
  let g : Nat -> Real := fun n => nicolasK (n : Real) - A * (n : Real) ^ (-b)
  have hPos : forall L : Nat, exists n : Nat, L <= n /\ 0 < g n := by
    intro L
    choose n hn hk using hPositive A hA L
    exact Exists.intro n (And.intro hn (sub_pos.mpr hk))
  have hNeg : forall L : Nat, exists n : Nat, L <= n /\ g n < 0 := by
    intro L
    choose n hn hk using hNegative L
    have hNonneg : 0 <= A * (n : Real) ^ (-b) := by positivity
    exact Exists.intro n (And.intro hn (by dsimp [g]; linarith only [hk, hNonneg]))
  choose j hj using exists_nat_gt X
  choose n hn hnTwo hPeak hLeft hRight using
    Nat.exists_ge_pos_adjacent_max_of_unbounded_signs g hPos hNeg (max N j)
  have hN : N <= n := (le_max_left N j).trans hn
  have hjn : j <= n := (le_max_right N j).trans hn
  have hnReal : (2 : Real) <= n := by exact_mod_cast hnTwo
  have hjnReal : (j : Real) <= n := by exact_mod_cast hjn
  dsimp [g] at hPeak hLeft hRight
  simp only [Nat.cast_add, Nat.cast_one, Nat.cast_ofNat] at hPeak hLeft hRight
  let x : Real := (n : Real) + 1
  have hxPos : 0 < x := by dsimp [x]; linarith
  have hxLarge : X <= x := by dsimp [x]; linarith only [hj, hjnReal]
  have hLower := nicolasLog_lower_of_power_peak n hnTwo b A hb hbOne hA hLeft hRight
  have hLossX := hX x hxLarge
  change nicolasK x - B ^ (2 : Nat) * (Real.log x + 1) * x ^ (-2 * b) / 2 <=
    nicolasLogMertensOscillation x at hLower
  have hPeakReal : A * x ^ (-b) < nicolasK x := sub_pos.mp hPeak
  have hScaledReserve := mul_le_mul_of_nonneg_right hReserve
    (Real.rpow_pos_of_pos hxPos (-b)).le
  refine Exists.intro (n + 1) (And.intro (by omega) ?_)
  simp only [Nat.cast_add, Nat.cast_one]
  change C * x ^ (-b) < nicolasLogMertensOscillation x
  nlinarith only [hLower, hLossX, hPeakReal, hScaledReserve]


/-- Unit rounding preserves a power excursion of the actual theta integral. -/
theorem nicolasK_nat_gt_power_of_real
    (n : Nat) (hn : 3 <= n) (x b A : Real) (hb : 0 < b) (hbOne : b <= 1)
    (hA : 0 < A) (hLog : 1 <= Real.log (n : Real))
    (hLower : (n : Real) <= x) (hUpper : x <= (n : Real) + 1)
    (hSupply : (2 * A + 6) * x ^ (-b) < nicolasK x) :
    A * (n : Real) ^ (-b) < nicolasK (n : Real) := by
  have hnThree : (3 : Real) <= n := by exact_mod_cast hn
  have hnPos : 0 < (n : Real) := by linarith
  have hxPos : 0 < x := hnPos.trans_le hLower
  have hxDouble : x <= 2 * (n : Real) := by linarith
  have hPowerX := Real.rpow_le_rpow hxPos.le hxDouble hb.le
  rw [Real.mul_rpow (by norm_num : (0 : Real) <= 2) hnPos.le] at hPowerX
  have hTwoPower := Real.rpow_le_rpow_of_exponent_le
    (by norm_num : (1 : Real) <= 2) hbOne
  rw [Real.rpow_one] at hTwoPower
  have hnPowerPos : 0 < (n : Real) ^ b := Real.rpow_pos_of_pos hnPos _
  have hxPowerPos : 0 < x ^ b := Real.rpow_pos_of_pos hxPos _
  have hPower : x ^ b <= 2 * (n : Real) ^ b :=
    hPowerX.trans (mul_le_mul_of_nonneg_right hTwoPower hnPowerPos.le)
  have hInv := one_div_le_one_div_of_le hxPowerPos hPower
  have hScaledInv := mul_le_mul_of_nonneg_left hInv (by norm_num : (0 : Real) <= 2)
  have hCancel : 2 * (1 / (2 * (n : Real) ^ b)) = (n : Real) ^ (-b) := by
    rw [Real.rpow_neg hnPos.le]
    field_simp [hnPowerPos.ne']
  rw [hCancel] at hScaledInv
  have hPowerRatio : (n : Real) ^ (-b) <= 2 * x ^ (-b) := by
    simpa only [Real.rpow_neg hxPos.le, one_div] using hScaledInv
  have hReciprocal : 1 / (n : Real) <= (n : Real) ^ (-b) := by
    rw [one_div, <- Real.rpow_neg_one]
    exact Real.rpow_le_rpow_of_exponent_le (by linarith) (by linarith)
  have hRound := nicolasK_sub_abs_le_of_le_add_one
    (by linarith : (2 : Real) <= n) hLog hLower hUpper
  have hCompare := mul_le_mul_of_nonneg_left hPowerRatio
    (show 0 <= A + 3 by linarith)
  have hPositive : 0 < (n : Real) ^ (-b) := Real.rpow_pos_of_pos hnPos _
  simp only [div_eq_mul_inv, one_mul] at hReciprocal hRound
  nlinarith only [hCompare, hSupply, (abs_le.mp hRound).1, hReciprocal, hPositive]

/-- Each zero-dependent integral excursion transfers to the corrected finite
Nicolas logarithm, with both signs and every amplitude. -/
theorem nicolasLog_two_sided_power_excursions_of_zero
    {rho : Complex} (hZero : riemannZeta rho = 0)
    (hHalf : (1 / 2 : Real) < rho.re) (hOne : rho.re < 1)
    {b : Real} (hLower : 1 - rho.re < b) (hbHalf : b <= 1 / 2) :
    forall X A : Real,
      (exists x : Real, max X 3 < x /\ A * x ^ (-b) < nicolasLogMertensOscillation x) /\
      (exists x : Real, max X 3 < x /\ A * x ^ (-b) < -nicolasLogMertensOscillation x) := by
  have hb : 0 < b := by linarith
  have hbOne : b <= 1 := by linarith
  have hSource := nicolasK_two_sided_power_excursions_of_zero hZero hHalf hOne hLower hbHalf
  have hPositive : forall A : Real, 0 < A -> forall N : Nat,
      exists n : Nat, N <= n /\ A * (n : Real) ^ (-b) < nicolasK (n : Real) := by
    intro A hA N
    choose x hx hK using (hSource ((max N 3 : Nat) : Real) (2 * A + 6)).1
    have hxBase : ((max N 3 : Nat) : Real) <= x :=
      (le_max_left _ _).trans hx.le
    let n : Nat := Nat.floor x
    have hMin : max N 3 <= n := Nat.le_floor hxBase
    have hnThree : 3 <= n := (le_max_right N 3).trans hMin
    have hnThreeReal : (3 : Real) <= n := by exact_mod_cast hnThree
    have hnPos : 0 < (n : Real) := by linarith
    have hxThree : 3 < x := (le_max_right _ _).trans_lt hx
    have hxPos : 0 < x := by linarith
    have hLog : 1 <= Real.log (n : Real) :=
      ((Real.lt_log_iff_exp_lt hnPos).mpr
        (Real.exp_one_lt_three.trans_le hnThreeReal)).le
    refine Exists.intro n (And.intro ((le_max_left N 3).trans hMin) ?_)
    exact nicolasK_nat_gt_power_of_real n hnThree x b A hb hbOne hA hLog
      (Nat.floor_le hxPos.le) (Nat.lt_floor_add_one x).le hK
  have hNegative : forall N : Nat,
      exists n : Nat, N <= n /\ nicolasK (n : Real) < 0 := by
    intro N
    choose x hx hK using (hSource ((max N 3 : Nat) : Real) 6).2
    have hxBase : ((max N 3 : Nat) : Real) <= x :=
      (le_max_left _ _).trans hx.le
    have hxThree : 3 < x := (le_max_right _ _).trans_lt hx
    have hxPos : 0 < x := by linarith
    have hPower : 1 / x <= x ^ (-b) := by
      rw [one_div, <- Real.rpow_neg_one]
      exact Real.rpow_le_rpow_of_exponent_le (by linarith) (by linarith)
    have hKBound : nicolasK x < -6 / x := by
      rw [div_eq_mul_inv]
      simp only [div_eq_mul_inv, one_mul] at hPower
      nlinarith only [hK, hPower]
    have hScaled := mul_lt_mul_of_pos_left hKBound hxPos
    have hCancel : x * (-6 / x) = (-6 : Real) := by field_simp [hxPos.ne']
    rw [hCancel] at hScaled
    let n : Nat := Nat.floor x
    have hMin : max N 3 <= n := Nat.le_floor hxBase
    have hnThree : 3 <= n := (le_max_right N 3).trans hMin
    have hnThreeReal : (3 : Real) <= n := by exact_mod_cast hnThree
    have hnPos : 0 < (n : Real) := by linarith
    have hLog : 1 <= Real.log (n : Real) :=
      ((Real.lt_log_iff_exp_lt hnPos).mpr
        (Real.exp_one_lt_three.trans_le hnThreeReal)).le
    refine Exists.intro n (And.intro ((le_max_left N 3).trans hMin) ?_)
    exact nicolasK_nat_neg_of_real_scaled_lt n hnThree x hLog
      (Nat.floor_le hxPos.le) (Nat.lt_floor_add_one x).le (by linarith only [hScaled])
  intro X A
  constructor
  . choose N hN using exists_nat_gt (max X 3)
    choose m hm hValue using nicolasLog_power_unbounded_of_K_integer_excursions
      b hb hbOne hPositive hNegative A N
    have hNm : (N : Real) <= (m : Real) := by exact_mod_cast hm
    exact Exists.intro (m : Real) (And.intro (hN.trans_le hNm) hValue)
  . have hSmall := (four_div_isLittleO_rpow_neg (by linarith : b < 1)).bound
      (by norm_num : (0 : Real) < 1)
    choose Y hY using eventually_atTop.mp hSmall
    choose x hx hK using (hSource (max X Y) (A + 1)).2
    have hxThree : 3 < x := (le_max_right _ _).trans_lt hx
    have hxPos : 0 < x := by linarith
    have hxY : Y <= x := (le_max_right X Y).trans ((le_max_left _ _).trans hx.le)
    have hError := hY x hxY
    change norm (4 / x) <= 1 * norm (x ^ (-b)) at hError
    rw [Real.norm_eq_abs, Real.norm_eq_abs,
      abs_of_pos (by positivity : 0 < (4 : Real) / x),
      abs_of_pos (Real.rpow_pos_of_pos hxPos (-b)), one_mul] at hError
    have hUpper := nicolasLogMertensOscillation_le_K_add_four_div hxThree.le
    have hxX : X < x := ((le_max_left X Y).trans (le_max_left _ _)).trans_lt hx
    refine Exists.intro x (And.intro (max_lt hxX hxThree) ?_)
    nlinarith only [hK, hError, hUpper]

/-- False RH gives one positive exponent below one half for both signs of the
actual finite-product logarithm, with unbounded normalized amplitudes. -/
theorem exists_nicolasLog_two_sided_power_excursions_of_not_RH
    (hNotRH : Not RiemannHypothesis) :
    exists b : Real, 0 < b /\ b < 1 / 2 /\
      forall X A : Real,
        (exists x : Real, max X 3 < x /\ A * x ^ (-b) < nicolasLogMertensOscillation x) /\
        (exists x : Real, max X 3 < x /\ A * x ^ (-b) < -nicolasLogMertensOscillation x) := by
  choose rho hZero hHalf hOne using
    exists_riemannZeta_zero_re_gt_half_of_not_riemannHypothesis hNotRH
  let b : Real := ((1 - rho.re) + 1 / 2) / 2
  have hb : 0 < b := by dsimp [b]; linarith
  have hbHalf : b < 1 / 2 := by dsimp [b]; linarith
  have hLower : 1 - rho.re < b := by dsimp [b]; linarith
  exact Exists.intro b (And.intro hb (And.intro hbHalf
    (nicolasLog_two_sided_power_excursions_of_zero hZero hHalf hOne hLower hbHalf.le)))

end PrimeFactorOscillations

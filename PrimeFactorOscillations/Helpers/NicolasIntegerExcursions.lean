/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.NicolasPeakSupply
import PrimeFactorOscillations.Helpers.NicolasPositiveExcursion
import PrimeFactorOscillations.Mathlib.NumberTheory.Chebyshev.LogTail

/-!
# Actual integer excursions for the Nicolas peak argument

Combines the reflected Landau conclusion, the canonical negative-J theorem,
the already proved prime-power tail estimate, and unit-interval rounding.
-/

set_option autoImplicit false
set_option Elab.async false

namespace PrimeFactorOscillations

open Filter MeasureTheory Set Robin1984

noncomputable section

theorem nicolasK_scaled_positive_supply_of_not_RH
    (hNotRH : Not RiemannHypothesis) (C X : Real) :
    exists x : Real, X <= x /\ C < x * nicolasK x := by
  let A : Real := max C 0 + 9
  choose x hx hJ using
    nicolasJ_arbitrary_positive_half_excursions_of_not_RH hNotRH X A
  have hxThree : 3 <= x := (lt_of_le_of_lt (le_max_right X 3) hx).le
  have hxPos : 0 < x := lt_of_lt_of_le (by norm_num) hxThree
  have hxOne : 1 <= x := le_trans (by norm_num) hxThree
  have hKInt := nicolasThetaTail_integrableOn_Ioi_two.mono_set
    (Ioi_subset_Ioi (le_trans (by norm_num) hxThree))
  have hJInt := nicolasPsiTail_integrableOn_Ioi_three.mono_set
    (Ioi_subset_Ioi hxThree)
  have hIdentity := nicolasJ_eq_K_add_primePowerTail hKInt hJInt
  have hTail : nicolasPrimePowerTail x <= 8 * x ^ (-(1 / 2 : Real)) := by
    simpa only [nicolasPrimePowerTail, nicolasTailKernel] using
      (Chebyshev.primePowerLogTail_bounds hxThree).2
  have hK : (max C 0 + 1) * x ^ (-(1 / 2 : Real)) < nicolasK x := by
    dsimp [A] at hJ
    linarith
  have hPower : 1 / x <= x ^ (-(1 / 2 : Real)) := by
    rw [one_div, <- Real.rpow_neg_one]
    exact Real.rpow_le_rpow_of_exponent_le hxOne (by norm_num)
  have hReciprocal : (max C 0 + 1) / x < nicolasK x := by
    calc
      (max C 0 + 1) / x = (max C 0 + 1) * (1 / x) := by ring
      _ <= (max C 0 + 1) * x ^ (-(1 / 2 : Real)) :=
        mul_le_mul_of_nonneg_left hPower (by linarith [le_max_right C 0])
      _ < nicolasK x := hK
  have hScaled := mul_lt_mul_of_pos_left hReciprocal hxPos
  have hCancel : x * ((max C 0 + 1) / x) = max C 0 + 1 := by
    field_simp [hxPos.ne']
  rw [hCancel] at hScaled
  refine Exists.intro x (And.intro (le_trans (le_max_left X 3) hx.le) ?_)
  nlinarith [le_max_left C 0]

theorem nicolasK_scaled_negative_supply_of_not_RH
    (hNotRH : Not RiemannHypothesis) (X : Real) :
    exists x : Real, X <= x /\ x * nicolasK x < -5 := by
  choose b hb hbHalf hOmega using
    exists_nicolasJ_omegaMinus_of_not_riemannHypothesis hNotRH
  choose c hc hLarge using hOmega
  have hbOne : b < 1 := lt_trans hbHalf (by norm_num)
  have hSmall := (rpow_neg_one_isLittleO_rpow_neg hbOne).bound
    (by positivity : 0 < c / 6)
  choose Y hY using eventually_atTop.mp hSmall
  choose x hx hJ using hLarge (max (max X 3) Y)
  change c * x ^ (-b) <= -nicolasJ x at hJ
  have hxThree : 3 <= x :=
    le_trans (le_trans (le_max_right X 3) (le_max_left (max X 3) Y)) hx
  have hxPos : 0 < x := lt_of_lt_of_le (by norm_num) hxThree
  have hPowPos : 0 < x ^ (-b) := Real.rpow_pos_of_pos hxPos _
  have hInvPos : 0 < x ^ (-(1 : Real)) := Real.rpow_pos_of_pos hxPos _
  have hError := hY x (le_trans (le_max_right (max X 3) Y) hx)
  change norm (x ^ (-(1 : Real))) <= (c / 6) * norm (x ^ (-b)) at hError
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos hInvPos,
    abs_of_pos hPowPos, Real.rpow_neg_one] at hError
  have hSix : 6 / x <= c * x ^ (-b) := by
    rw [div_eq_mul_inv]
    linarith
  have hKInt := nicolasThetaTail_integrableOn_Ioi_two.mono_set
    (Ioi_subset_Ioi (le_trans (by norm_num) hxThree))
  have hJInt := nicolasPsiTail_integrableOn_Ioi_three.mono_set
    (Ioi_subset_Ioi hxThree)
  have hKLe := nicolasK_le_J (le_trans (by norm_num) hxThree) hKInt hJInt
  have hBound : nicolasK x <= -6 / x := by
    rw [neg_div]
    linarith
  have hScaled := mul_le_mul_of_nonneg_left hBound hxPos.le
  have hCancel : x * (-6 / x) = (-6 : Real) := by field_simp [hxPos.ne']
  rw [hCancel] at hScaled
  refine Exists.intro x (And.intro
    (le_trans (le_trans (le_max_left X 3) (le_max_left (max X 3) Y)) hx) ?_)
  linarith

theorem nicolasK_integer_excursions_of_not_RH
    (hNotRH : Not RiemannHypothesis) :
    (forall A : Real, 0 < A -> forall N : Nat,
      exists n : Nat, N <= n /\ A / (n : Real) < nicolasK (n : Real)) /\
    (forall N : Nat, exists n : Nat, N <= n /\ nicolasK (n : Real) < 0) := by
  constructor
  . intro A hA N
    choose x hx hSupply using nicolasK_scaled_positive_supply_of_not_RH
      hNotRH (2 * A + 5) ((max N 3 : Nat) : Real)
    let n : Nat := Nat.floor x
    have hMin : max N 3 <= n := Nat.le_floor hx
    have hnThree : 3 <= n := le_trans (le_max_right N 3) hMin
    have hnThreeReal : (3 : Real) <= (n : Real) := by exact_mod_cast hnThree
    have hnPos : 0 < (n : Real) := by linarith
    have hxPos : 0 < x := by
      have hThree : (3 : Real) <= ((max N 3 : Nat) : Real) := by
        exact_mod_cast le_max_right N 3
      linarith
    have hLog : 1 <= Real.log (n : Real) :=
      ((Real.lt_log_iff_exp_lt hnPos).mpr
        (lt_of_lt_of_le Real.exp_one_lt_three hnThreeReal)).le
    refine Exists.intro n (And.intro (le_trans (le_max_left N 3) hMin) ?_)
    exact nicolasK_nat_gt_div_of_real_scaled_gt n hnThree x A hA.le hLog
      (Nat.floor_le hxPos.le) (Nat.lt_floor_add_one x).le hSupply
  . intro N
    choose x hx hSupply using nicolasK_scaled_negative_supply_of_not_RH
      hNotRH ((max N 3 : Nat) : Real)
    let n : Nat := Nat.floor x
    have hMin : max N 3 <= n := Nat.le_floor hx
    have hnThree : 3 <= n := le_trans (le_max_right N 3) hMin
    have hnThreeReal : (3 : Real) <= (n : Real) := by exact_mod_cast hnThree
    have hnPos : 0 < (n : Real) := by linarith
    have hxPos : 0 < x := by
      have hThree : (3 : Real) <= ((max N 3 : Nat) : Real) := by
        exact_mod_cast le_max_right N 3
      linarith
    have hLog : 1 <= Real.log (n : Real) :=
      ((Real.lt_log_iff_exp_lt hnPos).mpr
        (lt_of_lt_of_le Real.exp_one_lt_three hnThreeReal)).le
    refine Exists.intro n (And.intro (le_trans (le_max_left N 3) hMin) ?_)
    exact nicolasK_nat_neg_of_real_scaled_lt n hnThree x hLog
      (Nat.floor_le hxPos.le) (Nat.lt_floor_add_one x).le hSupply

theorem nicolasLog_scaled_unbounded_of_not_RH
    (hNotRH : Not RiemannHypothesis) (C : Real) (N : Nat) :
    exists m : Nat, N <= m /\
      C < (m : Real) * nicolasLogMertensOscillation (m : Real) := by
  have hSupply := nicolasK_integer_excursions_of_not_RH hNotRH
  exact nicolasLog_scaled_unbounded_of_K_integer_excursions
    hSupply.1 hSupply.2 C N

end

end PrimeFactorOscillations

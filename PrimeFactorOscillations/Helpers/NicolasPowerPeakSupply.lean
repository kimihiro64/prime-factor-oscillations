/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.NicolasPowerPeak

/-!
# Simultaneous power peaks for Nicolas interval persistence

The actual Landau excursions produce arbitrarily late integer peaks with
both a positive theta-tail value and controlled theta error at the same
endpoint. The exponent precedes all amplitudes and cutoffs. These initial
data feed positive-interval and local-count converses; no RH or prime-gap
improvement follows merely from the peak selection.
-/

set_option autoImplicit false
set_option Elab.async false

noncomputable section

namespace PrimeFactorOscillations

open Filter Robin1984

theorem nicolasK_integer_power_excursions_of_zero
    {rho : Complex} (hZero : riemannZeta rho = 0)
    (hHalf : (1 / 2 : Real) < rho.re) (hOne : rho.re < 1)
    {b : Real} (hLower : 1 - rho.re < b) (hbHalf : b <= 1 / 2) :
    (forall A : Real, 0 < A -> forall N : Nat,
      exists n : Nat, N <= n /\ A * (n : Real) ^ (-b) < nicolasK (n : Real)) /\
    (forall N : Nat, exists n : Nat, N <= n /\ nicolasK (n : Real) < 0) := by
  have hb : 0 < b := by linarith
  have hbOne : b <= 1 := by linarith
  have hSource := nicolasK_two_sided_power_excursions_of_zero
    hZero hHalf hOne hLower hbHalf
  constructor
  . intro A hA N
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
  . intro N
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

/-- The positive tail and its small theta error occur at the SAME arbitrarily
late integer endpoint. This supplies the initial data for interval persistence. -/
theorem exists_nicolasK_power_peak_of_zero
    {rho : Complex} (hZero : riemannZeta rho = 0)
    (hHalf : (1 / 2 : Real) < rho.re) (hOne : rho.re < 1)
    {b : Real} (hLower : 1 - rho.re < b) (hbHalf : b <= 1 / 2)
    (A : Real) (hA : 0 < A) (N : Nat) :
    exists n : Nat, N <= n /\ 2 <= n /\
      A * ((n : Real) + 1) ^ (-b) < nicolasK ((n : Real) + 1) /\
      0 < nicolasThetaError ((n : Real) + 1) /\
      nicolasThetaError ((n : Real) + 1) <=
        (2 * A + 1) * ((n : Real) + 1) ^ (1 - b) *
          Real.log ((n : Real) + 1) := by
  have hs := nicolasK_integer_power_excursions_of_zero hZero hHalf hOne hLower hbHalf
  let g : Nat -> Real := fun n => nicolasK (n : Real) - A * (n : Real) ^ (-b)
  have hPos : forall L : Nat, exists n : Nat, L <= n /\ 0 < g n := by
    intro L
    choose n hn hk using hs.1 A hA L
    exact Exists.intro n (And.intro hn (sub_pos.mpr hk))
  have hNeg : forall L : Nat, exists n : Nat, L <= n /\ g n < 0 := by
    intro L
    choose n hn hk using hs.2 L
    have hp : 0 <= A * (n : Real) ^ (-b) := by positivity
    exact Exists.intro n (And.intro hn (by dsimp [g]; linarith only [hk, hp]))
  choose n hn hnTwo hPeak hLeft hRight using
    Nat.exists_ge_pos_adjacent_max_of_unbounded_signs g hPos hNeg N
  dsimp [g] at hPeak hLeft hRight
  simp only [Nat.cast_add, Nat.cast_one, Nat.cast_ofNat] at hPeak hLeft hRight
  have hError := nicolasThetaError_bounds_of_power_peak n hnTwo b A
    (by linarith) (by linarith) hA hLeft hRight
  exact Exists.intro n (And.intro hn (And.intro hnTwo
    (And.intro (sub_pos.mp hPeak) hError)))

/-- One exponent works for every amplitude and every late cutoff. -/
theorem exists_nicolasK_power_peak_exponent_of_not_RH
    (hNotRH : Not RiemannHypothesis) :
    exists b : Real, 0 < b /\ b < 1 / 2 /\
      forall A : Real, 0 < A -> forall N : Nat,
        exists n : Nat, N <= n /\ 2 <= n /\
          A * ((n : Real) + 1) ^ (-b) < nicolasK ((n : Real) + 1) /\
          0 < nicolasThetaError ((n : Real) + 1) /\
          nicolasThetaError ((n : Real) + 1) <=
            (2 * A + 1) * ((n : Real) + 1) ^ (1 - b) *
              Real.log ((n : Real) + 1) := by
  choose rho hZero hHalf hOne using
    exists_riemannZeta_zero_re_gt_half_of_not_riemannHypothesis hNotRH
  let b : Real := ((1 - rho.re) + 1 / 2) / 2
  have hb : 0 < b := by dsimp [b]; linarith
  have hbHalf : b < 1 / 2 := by dsimp [b]; linarith
  have hbLower : 1 - rho.re < b := by dsimp [b]; linarith
  exact Exists.intro b (And.intro hb (And.intro hbHalf
    (fun A hA N => exists_nicolasK_power_peak_of_zero
      hZero hHalf hOne hbLower hbHalf.le A hA N)))

end PrimeFactorOscillations

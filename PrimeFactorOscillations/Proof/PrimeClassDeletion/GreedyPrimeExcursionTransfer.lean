/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.NicolasPowerExcursions
import PrimeFactorOscillations.Proof.PrimeClassDeletion.GreedyPrimePowerTransfer

/-!
# Actual positive-excursion exclusion through the signed deletion integral

The independent eventual count estimate bounds the full correction.
The native unconditional zero response supplies a larger positive amplitude.
No RH-dependent reconstruction is used.
-/

set_option autoImplicit false
set_option Elab.async false

open Filter
open PrimeFactorOscillations.PrimeClassSampling
open Robin1984

namespace PrimeFactorOscillations.PrimeClassDeletion

theorem greedyDeletedPrimeClass_zero_exclusion_via_integral
    (a C X0 : Real) (haHalf : (1 / 2 : Real) <= a) (ha : a < 1) (hC : 0 <= C)
    (hCount : forall t : Real, X0 <= t ->
      ((primeClassPrefix greedyDeletedPrimeClass (Nat.floor t)).card : Real) <= C * t ^ a)
    {rho : Complex} (hAbove : a < rho.re) (hBelow : rho.re < 1) :
    Not (riemannZeta rho = 0) := by
  intro hZero
  let b : Real := ((1 - rho.re) + (1 - a)) / 2
  let D : Real := (2 * C) / (1 - a)
  let Y : Real := max X0 (max 2 (Real.exp 1))
  have hLower : 1 - rho.re < b := by dsimp only [b]; linarith only [hAbove]
  have hbHalf : b <= 1 / 2 := by dsimp only [b]; linarith only [haHalf, hAbove]
  have hHalf : (1 / 2 : Real) < rho.re := haHalf.trans_lt hAbove
  have hD : 0 <= D := div_nonneg (by linarith only [hC]) (by linarith only [ha])
  choose x hx hSignal using
    (nicolasK_two_sided_power_excursions_of_zero hZero hHalf hBelow hLower hbHalf Y (D + 1)).1
  have hYx : Y < x := (le_max_left Y 3).trans_lt hx
  have hXx : X0 <= x := (le_max_left X0 _).trans hYx.le
  have hx2 : 2 <= x :=
    ((le_max_left 2 (Real.exp 1)).trans (le_max_right X0 _)).trans hYx.le
  have hx0 : 0 < x := by linarith only [hx2]
  have hxExp : Real.exp 1 < x :=
    ((le_max_right 2 (Real.exp 1)).trans (le_max_right X0 _)).trans_lt hYx
  have hLog : 1 <= Real.log x := ((Real.lt_log_iff_exp_lt hx0).mpr hxExp).le
  have hBound := (greedyPrimeNicolasIntegral_power_transfer a C x ha hC hx2 hLog
    (fun t ht => hCount t (hXx.trans ht))).2
  have hPaid : (2 * C) * x ^ (a - 1) / (1 - a) = D * x ^ (a - 1) := by
    dsimp only [D]
    ring
  rw [hPaid] at hBound
  have hCap := greedyPrimeNicolasIntegral_nonpos x hx2
  have hK : nicolasK x <= D * x ^ (a - 1) := by linarith only [hBound, hCap]
  have hPower : x ^ (a - 1) <= x ^ (-b) :=
    Real.rpow_le_rpow_of_exponent_le (by linarith only [hx2])
      (by dsimp only [b]; linarith only [hAbove])
  have hUpper : nicolasK x <= D * x ^ (-b) :=
    hK.trans (mul_le_mul_of_nonneg_left hPower hD)
  have hPositive : 0 < x ^ (-b) := Real.rpow_pos_of_pos hx0 _
  nlinarith only [hSignal, hUpper, hPositive]

end PrimeFactorOscillations.PrimeClassDeletion

/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.NicolasPowerExcursions
import PrimeFactorOscillations.Proof.PrimeClassDeletion.GreedyPrimePowerTransfer
import PrimeFactorOscillations.Proof.PrimeClassDeletion.GreedyPrimeStripCriterion

/-!
# Actual positive-excursion exclusion through the signed deletion integral

The independent eventual count estimate bounds the full correction.
The native unconditional zero response supplies a larger positive amplitude.
No RH-dependent reconstruction is used. The existing uniform strip count
also supplies the full forward mass and count estimates at real cutoffs.
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

theorem greedyDeletedPrimeClass_strip_eventually_mass_and_count
    (eta kappa : Real) (hEtaHalf : (1 / 2 : Real) <= eta) (hEtaOne : eta < 1)
    (hGap : eta < kappa)
    (hUpper : forall p : RiemannXiDivisorZeroIndex,
      (riemannXiDivisorZeroValue p).re <= eta) :
    Filter.Eventually (fun x : Real => And
      (primeClassThetaReal greedyDeletedPrimeClass x <=
        x ^ kappa * (Real.log x) ^ 2)
      (((primeClassPrefix greedyDeletedPrimeClass (Nat.floor x)).card : Real) <=
        x ^ kappa * Real.log x)) atTop := by
  have hNat := greedyDeletedPrimeClass_eventually_power_count_of_zero_strip eta
    hEtaHalf hEtaOne hUpper (kappa - eta) (sub_pos.mpr hGap)
  rw [show eta + (kappa - eta) = kappa by ring] at hNat
  choose N hN using eventually_atTop.mp hNat
  have hk : 0 <= kappa := by linarith only [hEtaHalf, hGap]
  filter_upwards [eventually_ge_atTop (max ((N : Real) + 4) (Real.exp 1))] with x hx
  have hxN : (N : Real) + 4 <= x :=
    (le_max_left ((N : Real) + 4) (Real.exp 1)).trans hx
  have hx4 : 4 <= x := by
    linarith only [hxN, (Nat.cast_nonneg N : (0 : Real) <= (N : Real))]
  have hx0 : 0 < x := by linarith only [hx4]
  have hFloor : N <= Nat.floor x := Nat.le_floor (by linarith only [hxN])
  have hLog : 1 <= Real.log x := by
    have h := Real.log_le_log (Real.exp_pos 1)
      ((le_max_right ((N : Real) + 4) (Real.exp 1)).trans hx)
    simpa only [Real.log_exp] using h
  have hLog0 : 0 <= Real.log x := by linarith only [hLog]
  have hCount : ((primeClassPrefix greedyDeletedPrimeClass (Nat.floor x)).card : Real) <=
      x ^ kappa :=
    (hN (Nat.floor x) hFloor).trans
      (Real.rpow_le_rpow (Nat.cast_nonneg _) (Nat.floor_le hx0.le) hk)
  have hPower0 : 0 <= x ^ kappa := Real.rpow_nonneg hx0.le kappa
  have hCountLog : ((primeClassPrefix greedyDeletedPrimeClass (Nat.floor x)).card : Real) *
      Real.log x <= x ^ kappa * Real.log x :=
    mul_le_mul_of_nonneg_right hCount hLog0
  have hMass := primeClassThetaReal_le_count_mul_log greedyDeletedPrimeClass x
    (by linarith only [hx4])
  have hLogSquare : Real.log x <= (Real.log x) ^ 2 := by nlinarith only [hLog]
  have hMassBound := hMass.trans
    (hCountLog.trans (mul_le_mul_of_nonneg_left hLogSquare hPower0))
  have hCountBound : ((primeClassPrefix greedyDeletedPrimeClass (Nat.floor x)).card : Real) <=
      x ^ kappa * Real.log x := by
    have h := mul_le_mul_of_nonneg_left hLog hPower0
    rw [mul_one] at h
    exact hCount.trans h
  exact And.intro hMassBound hCountBound

end PrimeFactorOscillations.PrimeClassDeletion

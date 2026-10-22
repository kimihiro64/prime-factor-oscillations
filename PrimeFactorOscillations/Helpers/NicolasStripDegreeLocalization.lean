/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.NicolasDegreeLocalization
import PrimeFactorOscillations.Helpers.NicolasStripDegreeError

/-!
# Pointwise psi localization under an arbitrary upper zero strip

The exact two-endpoint signed integral sandwich is localized at degree
ceil(sqrt(x))+1. Both endpoints, the full geometric width, and the
fractional degree allowance are retained uniformly in every real x.
-/

set_option autoImplicit false
set_option Elab.async false

noncomputable section

namespace PrimeFactorOscillations

open Robin1984

private theorem strip_degree_band_pointwise
    (eta : Real) (hEta : 0 <= eta)
    {n : Nat} (hn : 2 <= n) (D : Real) (hD : 0 <= D)
    (hError : forall y : Real, 2 <= y -> 1 <= Real.log y ->
      abs (robinPsiWeightedErrorIntegral n y) <=
        D * y ^ eta * nicolasDegreeMass n y)
    {a b : Real} (ha : 2 <= a) (hL : 1 <= Real.log a)
    (hab : a <= b) (hPower : 2 * a ^ n <= b ^ n) :
    And (Chebyshev.psi a <= b + 3 * D * b ^ eta)
      (a - 3 * D * b ^ eta <= Chebyshev.psi b) := by
  let T : Real := D * b ^ eta
  let ma : Real := nicolasDegreeMass n a
  let mb : Real := nicolasDegreeMass n b
  have haOne : 1 < a := by linarith only [ha]
  have hb : 2 <= b := ha.trans hab
  have hbOne : 1 < b := haOne.trans_le hab
  have hLb : 1 <= Real.log b :=
    hL.trans (Real.log_le_log (by linarith only [ha]) hab)
  have hma : 0 < ma := nicolasDegreeMass_pos n haOne
  have hmb : 0 < mb := nicolasDegreeMass_pos n hbOne
  have hHalf : mb <= ma / 2 := nicolasDegreeMass_halving haOne hab hPower
  have hRange : 0 < ma - mb := by linarith only [hma, hHalf]
  have hT : 0 <= T := by dsimp only [T]; positivity
  have hA0 := hError a ha hL
  have hB : abs (robinPsiWeightedErrorIntegral n b) <= T * mb := hError b hb hLb
  have hA : abs (robinPsiWeightedErrorIntegral n a) <= T * ma := by
    have hPow := Real.rpow_le_rpow (by linarith only [ha] : 0 <= a) hab hEta
    have hScale := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hPow hD) hma.le
    exact hA0.trans hScale
  have hBand := nicolasDegreeError_band_sandwich hn haOne hab
  change And ((Chebyshev.psi a - b) * (ma - mb) <=
      robinPsiWeightedErrorIntegral n a - robinPsiWeightedErrorIntegral n b)
    (robinPsiWeightedErrorIntegral n a - robinPsiWeightedErrorIntegral n b <=
      (Chebyshev.psi b - a) * (ma - mb)) at hBand
  have hPlus : ma + mb <= 3 * (ma - mb) := by linarith only [hHalf]
  have hAllowance := mul_le_mul_of_nonneg_left hPlus hT
  have hLower : -(3 * T) * (ma - mb) <=
      robinPsiWeightedErrorIntegral n a - robinPsiWeightedErrorIntegral n b := by
    have hAe := (abs_le.mp hA).1
    have hBe := (abs_le.mp hB).2
    nlinarith only [hAe, hBe, hAllowance]
  have hUpper : robinPsiWeightedErrorIntegral n a - robinPsiWeightedErrorIntegral n b <=
      (3 * T) * (ma - mb) := by
    have hAe := (abs_le.mp hA).2
    have hBe := (abs_le.mp hB).1
    nlinarith only [hAe, hBe, hAllowance]
  have hLeft := le_of_mul_le_mul_right (hBand.1.trans hUpper) hRange
  have hRight := le_of_mul_le_mul_right (hLower.trans hBand.2) hRange
  dsimp only [T] at hLeft hRight
  exact And.intro (by linarith only [hLeft]) (by linarith only [hRight])

theorem abs_nicolasPsiError_le_stripDegree
    (eta : Real) (hEta : 0 <= eta) (hEtaOne : eta <= 1)
    {n : Nat} (hn : 2 <= n) (D : Real) (hD : 0 <= D)
    (hError : forall y : Real, 2 <= y -> 1 <= Real.log y ->
      abs (robinPsiWeightedErrorIntegral n y) <=
        D * y ^ eta * nicolasDegreeMass n y)
    {x : Real} (hx : 4 <= x) (hL : 1 <= Real.log (x / 2)) :
    abs (Chebyshev.psi x - x) <= x / ((n : Real) - 1) + 6 * D * x ^ eta := by
  let a : Real := x * ((n : Real) - 1) / (n : Real)
  let b : Real := x * (n : Real) / ((n : Real) - 1)
  have hN : (2 : Real) <= (n : Real) := by exact_mod_cast hn
  have hNp : (0 : Real) < (n : Real) := by linarith only [hN]
  have hd : 0 < (n : Real) - 1 := by linarith only [hN]
  have hxPos : 0 < x := by linarith only [hx]
  have haEq : a * (n : Real) = x * ((n : Real) - 1) := by
    dsimp only [a]
    field_simp
  have hbEq : b * ((n : Real) - 1) = x * (n : Real) := by
    dsimp only [b]
    field_simp
  have haHalf : x / 2 <= a := by
    have h := mul_nonneg hxPos.le (sub_nonneg.mpr hN)
    have hProd : x / 2 * (n : Real) <= a * (n : Real) := by
      nlinarith only [haEq, h]
    exact le_of_mul_le_mul_right hProd hNp
  have hax : a <= x := by
    have hProd : a * (n : Real) <= x * (n : Real) := by
      nlinarith only [haEq, hxPos]
    exact le_of_mul_le_mul_right hProd hNp
  have hxb : x <= b := by
    have hProd : x * ((n : Real) - 1) <= b * ((n : Real) - 1) := by
      nlinarith only [hbEq, hxPos]
    exact le_of_mul_le_mul_right hProd hd
  have hbx : b <= 2 * x := by
    have h := mul_nonneg hxPos.le (sub_nonneg.mpr hN)
    have hProd : b * ((n : Real) - 1) <= (2 * x) * ((n : Real) - 1) := by
      nlinarith only [hbEq, h]
    exact le_of_mul_le_mul_right hProd hd
  have haTwo : 2 <= a := by linarith only [haHalf, hx]
  have hLa : 1 <= Real.log a :=
    hL.trans (Real.log_le_log (by linarith only [hx] : 0 < x / 2) haHalf)
  have hLx : 1 <= Real.log x :=
    hL.trans (Real.log_le_log (by linarith only [hx] : 0 < x / 2)
      (by linarith only [hxPos] : x / 2 <= x))
  have hScaledA : a * (n : Real) / ((n : Real) - 1) = x := by
    rw [haEq]
    field_simp
  have hLower := (strip_degree_band_pointwise eta hEta hn D hD hError haTwo hLa hax
    (by simpa only [hScaledA] using
      nicolasDegree_dilation_power hn (by linarith only [haTwo] : 0 <= a))).2
  have hUpper := (strip_degree_band_pointwise eta hEta hn D hD hError
    (by linarith only [hx] : 2 <= x) hLx hxb
      (nicolasDegree_dilation_power hn hxPos.le)).1
  have hTwoPower : (2 : Real) ^ eta <= 2 := by
    simpa only [Real.rpow_one] using
      Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : Real) <= 2) hEtaOne
  have hbNonneg : 0 <= b := hxPos.le.trans hxb
  have hPower : b ^ eta <= 2 * x ^ eta := by
    calc
      _ <= (2 * x) ^ eta := Real.rpow_le_rpow hbNonneg hbx hEta
      _ = (2 : Real) ^ eta * x ^ eta := Real.mul_rpow (by norm_num) hxPos.le
      _ <= _ := mul_le_mul_of_nonneg_right hTwoPower (Real.rpow_nonneg hxPos.le eta)
  have hScaledPower := mul_le_mul_of_nonneg_left hPower
    (show 0 <= 3 * D by positivity)
  have hDiffA : x - a = x / (n : Real) := by
    dsimp only [a]
    field_simp
    ring
  have hDiffB : b - x = x / ((n : Real) - 1) := by
    dsimp only [b]
    field_simp
    ring
  have hInv := one_div_le_one_div_of_le hd (show (n : Real) - 1 <= n by linarith)
  have hFractions : x / (n : Real) <= x / ((n : Real) - 1) := by
    simpa only [div_eq_mul_inv, one_mul] using mul_le_mul_of_nonneg_left hInv hxPos.le
  have hPowerNonneg : 0 <= D * x ^ eta := by positivity
  change a - 3 * D * x ^ eta <= Chebyshev.psi x at hLower
  change Chebyshev.psi x <= b + 3 * D * b ^ eta at hUpper
  apply abs_le.mpr
  constructor <;> nlinarith only [hLower, hUpper, hScaledPower,
    hDiffA, hDiffB, hFractions, hPowerNonneg]

theorem exists_nicolasPsiError_le_strip_rpow
    (eta delta : Real) (hEtaHalf : (1 / 2 : Real) <= eta) (hEtaOne : eta < 1)
    (hd : 0 < delta) (hdOne : delta <= 1)
    (hUpper : forall p : RiemannXiDivisorZeroIndex,
      (riemannXiDivisorZeroValue p).re <= eta) :
    Exists fun C : Real => And (0 < C) (forall x : Real, 4 <= x ->
      1 <= Real.log (x / 2) ->
        abs (Chebyshev.psi x - x) <= C * x ^ (eta + delta / 2)) := by
  have hEta : 0 <= eta := by linarith only [hEtaHalf]
  choose D hD hError using exists_nicolasStripDegreeError_bound
    eta delta hEta hEtaOne hd hdOne hUpper
  apply Exists.intro (1 + 12 * D)
  apply And.intro (by linarith only [hD])
  intro x hx hL
  let q : Real := Real.sqrt x
  let n : Nat := Nat.ceil q + 1
  have hxPos : 0 < x := by linarith only [hx]
  have hqPos : 0 < q := Real.sqrt_pos.mpr hxPos
  have hqTwo : 2 <= q := by
    dsimp only [q]
    exact (Real.le_sqrt (by norm_num) hxPos.le).mpr (by linarith only [hx])
  have hqSq : q ^ (2 : Nat) = x := Real.sq_sqrt hxPos.le
  have hCeil : q <= (Nat.ceil q : Real) := Nat.le_ceil q
  have hCeilHi : (Nat.ceil q : Real) < q + 1 := Nat.ceil_lt_add_one hqPos.le
  have hnEq : (n : Real) = (Nat.ceil q : Real) + 1 := by
    dsimp only [n]
    norm_cast
  have hn : 2 <= n := by
    have h : (2 : Real) <= (n : Real) := by linarith only [hCeil, hnEq, hqTwo]
    exact_mod_cast h
  have hnLower : q <= (n : Real) - 1 := by linarith only [hCeil, hnEq]
  have hnUpper : (n : Real) <= 2 * q := by linarith only [hCeilHi, hnEq, hqTwo]
  have hFirst : x / ((n : Real) - 1) <= q := by
    have hDen : 0 < (n : Real) - 1 := by linarith only [hnLower, hqPos]
    have hProd : x <= q * ((n : Real) - 1) := by
      nlinarith only [mul_le_mul_of_nonneg_left hnLower hqPos.le, hqSq]
    calc
      _ <= (q * ((n : Real) - 1)) / ((n : Real) - 1) :=
        div_le_div_of_nonneg_right hProd hDen.le
      _ = q := by field_simp [hDen.ne']
  have hFixed : forall y : Real, 2 <= y -> 1 <= Real.log y ->
      abs (robinPsiWeightedErrorIntegral n y) <=
        (D * (n : Real) ^ delta) * y ^ eta * nicolasDegreeMass n y := by
    intro y hy hLy
    have hyPos : 0 < y := by linarith only [hy]
    have hFactor : y ^ (eta - (n : Real)) * Inv.inv (Real.log y) =
        y ^ eta * nicolasDegreeMass n y := by
      dsimp only [nicolasDegreeMass]
      rw [sub_eq_add_neg, Real.rpow_add hyPos]
      ring
    have h := hError n hn y hy hLy
    rw [hFactor] at h
    simpa only [mul_assoc] using h
  have hPoint := abs_nicolasPsiError_le_stripDegree eta hEta hEtaOne.le hn
    (D * (n : Real) ^ delta) (by positivity) hFixed hx hL
  have hTwoPower : (2 : Real) ^ delta <= 2 := by
    simpa only [Real.rpow_one] using
      Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : Real) <= 2) hdOne
  have hQPower : q ^ delta = x ^ (delta / 2) := by
    dsimp only [q]
    rw [Real.sqrt_eq_rpow, <- Real.rpow_mul hxPos.le]
    congr 1
    ring
  have hDegree : (n : Real) ^ delta <= 2 * x ^ (delta / 2) := by
    calc
      _ <= (2 * q) ^ delta :=
        Real.rpow_le_rpow (Nat.cast_nonneg n) hnUpper hd.le
      _ = (2 : Real) ^ delta * q ^ delta :=
        Real.mul_rpow (by norm_num) hqPos.le
      _ <= 2 * q ^ delta :=
        mul_le_mul_of_nonneg_right hTwoPower (Real.rpow_nonneg hqPos.le delta)
      _ = _ := by rw [hQPower]
  have hRoot : q <= x ^ (eta + delta / 2) := by
    dsimp only [q]
    rw [Real.sqrt_eq_rpow]
    exact Real.rpow_le_rpow_of_exponent_le (by linarith only [hx])
      (by linarith only [hEtaHalf, hd])
  have hScaled := mul_le_mul_of_nonneg_left hDegree
    (show 0 <= 6 * D * x ^ eta by positivity)
  have hSecond : 6 * (D * (n : Real) ^ delta) * x ^ eta <=
      12 * D * x ^ (eta + delta / 2) := by
    calc
      _ = (6 * D * x ^ eta) * (n : Real) ^ delta := by ring
      _ <= (6 * D * x ^ eta) * (2 * x ^ (delta / 2)) := hScaled
      _ = 12 * D * (x ^ eta * x ^ (delta / 2)) := by ring
      _ = _ := by rw [<- Real.rpow_add hxPos]
  nlinarith only [hPoint, hFirst, hRoot, hSecond]

end PrimeFactorOscillations

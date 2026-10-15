/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.NicolasDegreeLocalization

/-!
# Short-band localization for the actual weighted prime-count error

The degree-two cutoff loses only a factor proportional to the reciprocal
band width. Both endpoints and their signed errors are retained.
-/

set_option autoImplicit false
set_option Elab.async false

namespace PrimeFactorOscillations

open Robin1984

theorem nicolasDegreeMass_two_short_band
    {x H : Real} (hx : 1 < x) (hH : 0 <= H) (hHx : H <= x) :
    H <= 2 * x ^ 3 * Real.log x *
      (nicolasDegreeMass 2 x - nicolasDegreeMass 2 (x + H)) := by
  have hxPos : 0 < x := by linarith only [hx]
  have hbPos : 0 < x + H := by linarith only [hxPos, hH]
  have hLogPos : 0 < Real.log x := Real.log_pos hx
  have hLog : Real.log x <= Real.log (x + H) :=
    Real.log_le_log hxPos (by linarith only [hH])
  have hInv : Inv.inv ((x + H) ^ 2 * Real.log (x + H)) <=
      Inv.inv ((x + H) ^ 2 * Real.log x) := by
    have h := one_div_le_one_div_of_le
      (mul_pos (sq_pos_of_pos hbPos) hLogPos)
      (mul_le_mul_of_nonneg_left hLog (sq_nonneg (x + H)))
    simpa only [one_div] using h
  have hCoeff : 0 <= 2 * x ^ 3 * Real.log x := by positivity
  have hPoly : 0 <= H * (3 * x ^ 2 - H ^ 2) := by
    have hDiff := mul_nonneg (sub_nonneg.mpr hHx) (add_nonneg hxPos.le hH)
    exact mul_nonneg hH (by nlinarith only [hDiff, sq_nonneg x])
  have hIdentity :
      2 * x ^ 3 * Real.log x *
        (Inv.inv (x ^ 2 * Real.log x) -
          Inv.inv ((x + H) ^ 2 * Real.log x)) =
        2 * x * H * (2 * x + H) / (x + H) ^ 2 := by
    field_simp
    ring
  have hLower : H <= 2 * x * H * (2 * x + H) / (x + H) ^ 2 := by
    have hCross : H * (x + H) ^ 2 <= 2 * x * H * (2 * x + H) := by
      nlinarith only [hPoly]
    have hCancel : (x + H) ^ 2 * Inv.inv ((x + H) ^ 2) = 1 := by
      field_simp
    have hMul := mul_le_mul_of_nonneg_right hCross
      (inv_nonneg.mpr (sq_nonneg (x + H)))
    simpa only [mul_assoc, hCancel, mul_one, div_eq_mul_inv] using hMul
  rw [nicolasDegreeMass_eq_inv 2 hxPos,
    nicolasDegreeMass_eq_inv 2 hbPos]
  calc
    _ <= 2 * x * H * (2 * x + H) / (x + H) ^ 2 := hLower
    _ = 2 * x ^ 3 * Real.log x *
        (Inv.inv (x ^ 2 * Real.log x) -
          Inv.inv ((x + H) ^ 2 * Real.log x)) := hIdentity.symm
    _ <= _ := mul_le_mul_of_nonneg_left (sub_le_sub_left hInv _) hCoeff

/-- Both signed endpoint deviations are controlled by the same complete band. -/
theorem nicolasDegree_two_short_band_pointwise
    {a H R : Real} (ha : 1 < a) (hH : 0 <= H) (hHa : H <= a)
    (hR : 0 <= R)
    (hEa : abs (robinPsiWeightedErrorIntegral 2 a) <= R)
    (hEb : abs (robinPsiWeightedErrorIntegral 2 (a + H)) <= R) :
    (Chebyshev.psi a - (a + H)) * H <= 4 * a ^ 3 * Real.log a * R /\
      (a - Chebyshev.psi (a + H)) * H <= 4 * a ^ 3 * Real.log a * R := by
  let D := nicolasDegreeMass 2 a - nicolasDegreeMass 2 (a + H)
  let K := 2 * a ^ 3 * Real.log a
  have hK : 0 <= K := by
    have haPos : 0 < a := by linarith only [ha]
    have hLogPos : 0 < Real.log a := Real.log_pos ha
    dsimp [K]
    positivity
  have hMass : H <= K * D := nicolasDegreeMass_two_short_band ha hH hHa
  have hBand := nicolasDegreeError_band_sandwich
    (by norm_num : 2 <= (2 : Nat)) ha (by linarith only [hH] : a <= a + H)
  have hUpper : (Chebyshev.psi a - (a + H)) * D <= 2 * R := by
    have hA := (abs_le.mp hEa).2
    have hB := (abs_le.mp hEb).1
    have hBandUpper := hBand.1
    change (Chebyshev.psi a - (a + H)) * D <= _ at hBandUpper
    linarith only [hBandUpper, hA, hB]
  have hLower : (a - Chebyshev.psi (a + H)) * D <= 2 * R := by
    have hA := (abs_le.mp hEa).1
    have hB := (abs_le.mp hEb).2
    have hBandLower := hBand.2
    change _ <= (Chebyshev.psi (a + H) - a) * D at hBandLower
    nlinarith only [hBandLower, hA, hB]
  have hPacket : forall q : Real, q * D <= 2 * R ->
      q * H <= K * (2 * R) := by
    intro q hq
    by_cases hSign : 0 <= q
    . have hMul := mul_le_mul_of_nonneg_left hMass hSign
      have hEnd := mul_le_mul_of_nonneg_left hq hK
      nlinarith only [hMul, hEnd]
    . have hProduct := mul_nonpos_of_nonpos_of_nonneg (le_of_not_ge hSign) hH
      exact hProduct.trans (mul_nonneg hK (by positivity))
  constructor
  . have h := hPacket _ hUpper
    dsimp [K] at h
    nlinarith only [h]
  . have h := hPacket _ hLower
    dsimp [K] at h
    nlinarith only [h]

/-- A two-sided interval gives pointwise control without an RH premise. -/
theorem nicolasDegree_two_local_error
    {x H R : Real} (ha : 1 < x - H) (hH : 0 <= H) (h2H : 2 * H <= x)
    (hR : 0 <= R)
    (hEa : abs (robinPsiWeightedErrorIntegral 2 (x - H)) <= R)
    (hEx : abs (robinPsiWeightedErrorIntegral 2 x) <= R)
    (hEb : abs (robinPsiWeightedErrorIntegral 2 (x + H)) <= R) :
    abs (Chebyshev.psi x - x) * H <= H ^ 2 + 4 * x ^ 3 * Real.log x * R := by
  have hx : 1 < x := by linarith only [ha, hH]
  have hxPos : 0 < x := by linarith only [hx]
  have haPos : 0 < x - H := by linarith only [ha]
  have hHx : H <= x := by linarith only [h2H, hH]
  have hUpper := nicolasDegree_two_short_band_pointwise hx hH hHx hR hEx hEb
  have hLower := nicolasDegree_two_short_band_pointwise ha hH
    (by linarith only [h2H] : H <= x - H) hR hEa
    (by simpa only [sub_add_cancel] using hEx)
  have hLogA : 0 < Real.log (x - H) := Real.log_pos ha
  have hLog : Real.log (x - H) <= Real.log x :=
    Real.log_le_log haPos (by linarith only [hH])
  have hPow : (x - H) ^ 3 <= x ^ 3 := by
    have hProduct : 0 <= H * (x ^ 2 + x * (x - H) + (x - H) ^ 2) := by
      exact mul_nonneg hH (by positivity)
    nlinarith only [hProduct]
  have hCoeff : 4 * (x - H) ^ 3 * Real.log (x - H) * R <=
      4 * x ^ 3 * Real.log x * R := by
    have h := mul_le_mul hPow hLog hLogA.le (by positivity : 0 <= x ^ 3)
    have hFour := mul_le_mul_of_nonneg_left h (by norm_num : (0 : Real) <= 4)
    have hFinal := mul_le_mul_of_nonneg_right hFour hR
    simpa only [mul_assoc] using hFinal
  have hLowRaw := hLower.2
  simp only [sub_add_cancel] at hLowRaw
  have hLow := hLowRaw.trans hCoeff
  have hAbs : abs ((Chebyshev.psi x - x) * H) <=
      H ^ 2 + 4 * x ^ 3 * Real.log x * R := by
    apply abs_le.mpr
    constructor
    . nlinarith only [hLow]
    . nlinarith only [hUpper.1]
  simpa only [abs_mul, abs_of_nonneg hH] using hAbs

end PrimeFactorOscillations

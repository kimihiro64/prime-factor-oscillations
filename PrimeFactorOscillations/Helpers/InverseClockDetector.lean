/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.PrimeClockComparison

/-!
# Inverse Clock Detector

Quantitative error control for an existing local inverse of the reference clock.
-/

set_option autoImplicit false
set_option Elab.async false

noncomputable section
namespace PrimeFactorOscillations.InverseClockDetector

theorem inverse_error (R Phi r N L B K a : Real)
    (hr : 0 < r) (hN : 0 < N) (hL : 0 < L) (ha : 0 < a)
    (hK : 0 <= K) (hrK : 2 * K <= r) (hLower : a <= r / L)
    (hRoot : R = Phi)
    (hCompare : abs (R - Phi - r / L ^ 2 * (L - B)) <=
      K * (abs (L - B) / L ^ 2 + 1 / (r * N))) :
    abs (L - B) <= (2 * K / a ^ 2) / N := by
  let d := abs (L - B)
  have hd : 0 <= d := abs_nonneg _
  have hlin : r / L ^ 2 * d <= K * (d / L ^ 2 + 1 / (r * N)) := by
    simpa only [hRoot, sub_self, zero_sub, abs_neg, abs_mul,
      abs_of_nonneg (div_nonneg hr.le (sq_nonneg L)), d] using hCompare
  have hmul := mul_le_mul_of_nonneg_right hlin (sq_nonneg L)
  have hscaled : r * d <= K * d + K * L ^ 2 / (r * N) := by
    convert hmul using 1 <;> field_simp [hL.ne', hr.ne', hN.ne'] <;> ring
  have hmul2 := mul_le_mul_of_nonneg_right hscaled (mul_pos hr hN).le
  have hscaled2 : r ^ 2 * N * d <= K * r * N * d + K * L ^ 2 := by
    convert hmul2 using 1 <;> field_simp [hr.ne', hN.ne'] <;> ring
  have hsmall := mul_le_mul_of_nonneg_right hrK
    (mul_nonneg (mul_nonneg hr.le hN.le) hd)
  have htotal : r ^ 2 * N * d <= 2 * K * L ^ 2 := by
    nlinarith only [hscaled2, hsmall]
  have hband0 := mul_le_mul_of_nonneg_right hLower hL.le
  have hband : a * L <= r := by
    convert hband0 using 1 <;> field_simp [hL.ne']
  have hsq : a ^ 2 * L ^ 2 <= r ^ 2 := by
    nlinarith [mul_nonneg ha.le hL.le]
  have hsqmul := mul_le_mul_of_nonneg_right hsq (mul_nonneg hN.le hd)
  have htotal2 : (a ^ 2 * N * d) * L ^ 2 <= (2 * K) * L ^ 2 := by
    nlinarith only [hsqmul, htotal]
  have htotal3 : a ^ 2 * N * d <= 2 * K :=
    _root_.le_of_mul_le_mul_right htotal2 (sq_pos_of_pos hL)
  have hcancel : ((2 * K / a ^ 2) / N) * (a ^ 2 * N) = 2 * K := by
    field_simp [ha.ne', hN.ne']
  have hfinal : abs (L - B) * (a ^ 2 * N) <=
      ((2 * K / a ^ 2) / N) * (a ^ 2 * N) := by
    rw [hcancel]
    change d * (a ^ 2 * N) <= 2 * K
    nlinarith only [htotal3]
  exact _root_.le_of_mul_le_mul_right hfinal (mul_pos (sq_pos_of_pos ha) hN)

end PrimeFactorOscillations.InverseClockDetector

namespace PrimeFactorOscillations.PrimeClockLaw

theorem exists_reference_inverse_accuracy (law : PrimeClockLaw)
    (a : Real) (ha : 0 < a) (b : Real) (hb : 0 < b) :
    exists r0 N0 : Nat, exists C : Real,
      0 < r0 /\ 1 <= N0 /\ 0 <= C /\
      forall r : Nat, r0 <= r -> forall N : Nat, N0 <= N ->
      forall L : Real, 2 <= L -> abs (law.arithmeticClock N - L) <= 1 ->
        a <= (r : Real) / L -> (r : Real) / L <= b ->
        law.densityRatio N r = law.referenceRatio r L ->
        abs (L - law.arithmeticClock N) <= C / (N : Real) := by
  choose r1 N0 K hr1 hN0 hK hCompare using law.exists_densityRatio_linearization b hb
  choose R hR using exists_nat_gt (2 * K)
  refine Exists.intro (max r1 R) (Exists.intro N0 (Exists.intro (2 * K / a ^ 2)
    (And.intro (hr1.trans_le (le_max_left _ _))
      (And.intro hN0 (And.intro (by positivity) ?_)))))
  intro r hr N hN L hL hNear hLower hUpper hRoot
  have hr1r : r1 <= r := (le_max_left _ _).trans hr
  have hRr : R <= r := (le_max_right _ _).trans hr
  have hrPos : (0 : Real) < r := by exact_mod_cast (hr1.trans_le hr1r)
  have hNPos : (0 : Real) < N := by
    exact_mod_cast (Nat.zero_lt_one.trans_le (hN0.trans hN))
  have hrK : 2 * K <= (r : Real) :=
    hR.le.trans (by exact_mod_cast hRr)
  have hData := hCompare r hr1r N hN L hL hNear hUpper
  exact InverseClockDetector.inverse_error
    (law.densityRatio N r) (law.referenceRatio r L) (r : Real) (N : Real)
    L (law.arithmeticClock N) K a hrPos hNPos (by linarith) ha hK hrK hLower
    hRoot hData.2.2


end PrimeFactorOscillations.PrimeClockLaw

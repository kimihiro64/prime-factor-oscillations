/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.HamiltonianPrimeCutoffSelection
import PrimeFactorOscillations.Helpers.HamiltonianRationalModelNorm

/-! # The complete arithmetic-plus-spectral error on one physical scale

All five arithmetic error contributions and the Gram correction are
bounded together by one logarithmic-over-square-root-cutoff scale.
The signed rational main operator and its two exceptional modes remain
outside this error budget.
-/

set_option autoImplicit false
set_option Elab.async false

noncomputable section

namespace PrimeFactorOscillations.LPF

theorem hamiltonian_prime_operator_scalar_budget
    (H K C m n q ell a b : Real)
    (hH : 0 <= H) (hK : 0 <= K) (hC : 0 <= C)
    (hm : 1 <= m) (hn : 0 < n) (hq : 1 <= q) (hEll : 1 <= ell)
    (ha : 0 <= a) (hb : 0 <= b) (hMN : m <= 4 * n)
    (hFifth : q ^ 5 <= m) (hMajor : q ^ 4 * a <= m)
    (hMinor : b * q <= m ^ 2) :
    max
      (H + K * q ^ 2 * Real.sqrt q * a * ell ^ 2 + 4 * q ^ 3)
      (Real.sqrt (C * (m ^ 2 / q + b) * ell ^ 10) + q * m / (2 * q ^ 2)) / n +
        2 * q ^ 4 / n <=
      (4 * (H + K + 5 + Real.sqrt (2 * C)) + 8) * ell ^ 5 / Real.sqrt q := by
  let s := Real.sqrt q
  let U := m * ell ^ 5 / s
  let A := H + K + 5 + Real.sqrt (2 * C)
  let rad := C * (m ^ 2 / q + b) * ell ^ 10
  have hq0 : 0 < q := by linarith only [hq]
  have hm0 : 0 <= m := by linarith only [hm]
  have hEll0 : 0 <= ell := by linarith only [hEll]
  have hs : 0 < s := Real.sqrt_pos.mpr hq0
  have hsSquare : s ^ 2 = q := Real.sq_sqrt hq0.le
  have hsQ : s <= q := by
    have hSquare : q <= q ^ 2 := by nlinarith only [hq]
    nlinarith only [hsSquare, hSquare, hs, hq]
  have hP (x : Real) (hx : 1 <= x) (i j : Nat) (hij : i <= j) :
      x ^ i <= x ^ j := by
    calc
      _ = x ^ (i : Real) := (Real.rpow_natCast _ _).symm
      _ <= x ^ (j : Real) := Real.rpow_le_rpow_of_exponent_le hx (by exact_mod_cast hij)
      _ = _ := Real.rpow_natCast _ _
  have hQ35 : q ^ 3 <= q ^ 5 := hP q hq 3 5 (by decide)
  have hQ34 : q ^ 3 <= q ^ 4 := hP q hq 3 4 (by decide)
  have hQ45 : q ^ 4 <= q ^ 5 := hP q hq 4 5 (by decide)
  have hQM : q <= m := by
    simpa only [pow_one] using (hP q hq 1 5 (by decide)).trans hFifth
  have hEll5 : 1 <= ell ^ 5 := by
    simpa only [one_pow] using wick_nonnegative_power_le 1 ell (by norm_num) hEll 5
  have hEll25 : ell ^ 2 <= ell ^ 5 := hP ell hEll 2 5 (by decide)
  have hMell : m <= m * ell ^ 5 := by
    have h := mul_le_mul_of_nonneg_left hEll5 hm0
    simpa only [mul_one] using h
  have hToU (v c : Real) (h : v * s <= c * m * ell ^ 5) : v <= c * U := by
    calc
      _ = (v * s) / s := by field_simp
      _ <= (c * m * ell ^ 5) / s := div_le_div_of_nonneg_right h hs.le
      _ = _ := by dsimp [U]; ring
  have hU : 1 <= U := by
    have h := hToU 1 1 (by simpa only [one_mul] using hsQ.trans (hQM.trans hMell))
    simpa only [one_mul] using h
  have hHead : H <= H * U := by
    simpa only [mul_one] using mul_le_mul_of_nonneg_left hU hH
  have hQ3A : q ^ 3 * a <= m :=
    (mul_le_mul_of_nonneg_right hQ34 ha).trans hMajor
  have hMajorCross : (q ^ 2 * s * a * ell ^ 2) * s <= m * ell ^ 5 := by
    calc
      _ = (q ^ 2 * a * ell ^ 2) * s ^ 2 := by ring
      _ = (q ^ 3 * a) * ell ^ 2 := by rw [hsSquare]; ring
      _ <= _ := mul_le_mul hQ3A hEll25 (sq_nonneg _) hm0
  have hMajorUnit : q ^ 2 * s * a * ell ^ 2 <= U := by
    simpa only [one_mul] using hToU _ 1 (by simpa only [one_mul] using hMajorCross)
  have hMajorBound : K * q ^ 2 * s * a * ell ^ 2 <= K * U := by
    have h := mul_le_mul_of_nonneg_left hMajorUnit hK
    nlinarith only [h]
  have hQ3S : q ^ 3 * s <= m :=
    (mul_le_mul_of_nonneg_left hsQ (by positivity : 0 <= q ^ 3)).trans
      (by simpa only [<- pow_succ] using hQ45.trans hFifth)
  have hOff : 4 * q ^ 3 <= 4 * U := by
    apply hToU
    nlinarith only [hQ3S, hMell]
  have hQ4S : q ^ 4 * s <= m := by
    have h := mul_le_mul_of_nonneg_left hsQ (by positivity : 0 <= q ^ 4)
    exact h.trans (by simpa only [<- pow_succ] using hFifth)
  have hGram : q ^ 4 <= U := by
    simpa only [one_mul] using hToU _ 1
      (by simpa only [one_mul] using hQ4S.trans hMell)
  have hRatio : s / q <= 1 := by
    calc
      _ <= q / q := div_le_div_of_nonneg_right hsQ hq0.le
      _ = _ := by field_simp
  have hFarCross : (q * m / (2 * q ^ 2)) * s <= m * ell ^ 5 := by
    calc
      _ = (m / 2) * (s / q) := by field_simp <;> ring
      _ <= (m / 2) * 1 := mul_le_mul_of_nonneg_left hRatio (by positivity)
      _ <= m := by linarith only [hm]
      _ <= _ := hMell
  have hFar : q * m / (2 * q ^ 2) <= U := by
    simpa only [one_mul] using hToU _ 1 (by simpa only [one_mul] using hFarCross)
  have hRad : 0 <= rad := by dsimp [rad]; positivity
  have hInner : rad * q <= 2 * C * m ^ 2 * ell ^ 10 := by
    calc
      _ = C * (m ^ 2 + b * q) * ell ^ 10 := by dsimp [rad]; field_simp <;> ring
      _ <= C * (2 * m ^ 2) * ell ^ 10 := by
        apply mul_le_mul_of_nonneg_right _ (by positivity)
        exact mul_le_mul_of_nonneg_left (by linarith only [hMinor]) hC
      _ = _ := by ring
  have hRootSquare : Real.sqrt rad ^ 2 = rad := Real.sq_sqrt hRad
  have hCSquare : Real.sqrt (2 * C) ^ 2 = 2 * C := Real.sq_sqrt (by positivity)
  have hCrossSquare :
      (Real.sqrt rad * s) ^ 2 <= (Real.sqrt (2 * C) * m * ell ^ 5) ^ 2 := by
    simp only [mul_pow, hRootSquare, hsSquare, hCSquare]
    convert hInner using 1 <;> ring
  have hCross : Real.sqrt rad * s <= Real.sqrt (2 * C) * m * ell ^ 5 := by
    have hLeft : 0 <= Real.sqrt rad * s := by positivity
    have hRight : 0 <= Real.sqrt (2 * C) * m * ell ^ 5 := by positivity
    nlinarith only [hCrossSquare, hLeft, hRight]
  have hRoot : Real.sqrt rad <= Real.sqrt (2 * C) * U := hToU _ _ hCross
  have hU0 : 0 <= U := by linarith only [hU]
  have hRootU : 0 <= Real.sqrt (2 * C) * U := by positivity
  have hHU : 0 <= H * U := mul_nonneg hH hU0
  have hKU : 0 <= K * U := mul_nonneg hK hU0
  have hE : max (H + K * q ^ 2 * s * a * ell ^ 2 + 4 * q ^ 3)
      (Real.sqrt rad + q * m / (2 * q ^ 2)) <= A * U := by
    apply max_le
    . dsimp [A]
      nlinarith only [hHead, hMajorBound, hOff, hRootU, hU0]
    . dsimp [A]
      nlinarith only [hRoot, hFar, hHU, hKU, hU0]
  have hMNBound : m / n <= 4 := by
    calc
      _ <= (4 * n) / n := div_le_div_of_nonneg_right hMN hn.le
      _ = _ := by field_simp
  have hRatioNN : 0 <= ell ^ 5 / s := by positivity
  have hA : 0 <= A := by dsimp [A]; positivity
  have hMain : max (H + K * q ^ 2 * s * a * ell ^ 2 + 4 * q ^ 3)
      (Real.sqrt rad + q * m / (2 * q ^ 2)) / n <= 4 * A * (ell ^ 5 / s) := by
    calc
      _ <= (A * U) / n := div_le_div_of_nonneg_right hE hn.le
      _ = (A * (ell ^ 5 / s)) * (m / n) := by dsimp [U]; ring
      _ <= (A * (ell ^ 5 / s)) * 4 :=
        mul_le_mul_of_nonneg_left hMNBound (mul_nonneg hA hRatioNN)
      _ = _ := by ring
  have hGramBound : 2 * q ^ 4 / n <= 8 * (ell ^ 5 / s) := by
    calc
      _ <= 2 * U / n :=
        div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hGram (by norm_num)) hn.le
      _ = (2 * (ell ^ 5 / s)) * (m / n) := by dsimp [U]; ring
      _ <= (2 * (ell ^ 5 / s)) * 4 :=
        mul_le_mul_of_nonneg_left hMNBound (by positivity)
      _ = _ := by ring
  change max (H + K * q ^ 2 * s * a * ell ^ 2 + 4 * q ^ 3)
      (Real.sqrt rad + q * m / (2 * q ^ 2)) / n + 2 * q ^ 4 / n <=
        (4 * A + 8) * ell ^ 5 / s
  calc
    _ <= 4 * A * (ell ^ 5 / s) + 8 * (ell ^ 5 / s) := add_le_add hMain hGramBound
    _ = _ := by ring

end PrimeFactorOscillations.LPF

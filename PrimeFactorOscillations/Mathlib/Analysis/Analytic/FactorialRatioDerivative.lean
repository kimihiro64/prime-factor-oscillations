/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import PrimeFactorOscillations.Mathlib.Analysis.Analytic.FactorialPolynomial

/-!
# Derivatives of adjacent factorial-convolution ratios

The exact derivative retains the normalized denominator. Bounds on that
denominator and its first two derivatives give an explicit uniform slope error.
-/

set_option autoImplicit false
set_option Elab.async false

namespace Nat

theorem hasDerivAt_factorialConvolution_ratio
    (c : Nat -> Real) (r : Nat) (hr : 0 < r) (u : Real) (hu : Not (u = 0))
    (hA : Not (normalizedDescFactorialPolynomial c r ((r : Real) / u) = 0)) :
    HasDerivAt (fun v : Real => factorialConvolution c (r - 1) v / factorialConvolution c r v)
      (-(r : Real) / u ^ 2 +
        (2 * ((r : Real) / u) *
          (deriv (normalizedDescFactorialPolynomial c r) ((r : Real) / u) /
            normalizedDescFactorialPolynomial c r ((r : Real) / u)) +
          ((r : Real) / u) ^ 2 *
            (deriv (deriv (normalizedDescFactorialPolynomial c r)) ((r : Real) / u) /
              normalizedDescFactorialPolynomial c r ((r : Real) / u) -
              (deriv (normalizedDescFactorialPolynomial c r) ((r : Real) / u) /
                normalizedDescFactorialPolynomial c r ((r : Real) / u)) ^ 2)) / u ^ 2) u := by
  let A := normalizedDescFactorialPolynomial c r
  let t := (r : Real) / u
  have hr0 : Not ((r : Real) = 0) := by exact_mod_cast Nat.ne_of_gt hr
  have hInv : HasDerivAt (fun v : Real => (r : Real) / v) (-(r : Real) / u ^ 2) u := by
    simpa using (hasDerivAt_const u (r : Real)).fun_div (hasDerivAt_id u) hu
  have hAd : HasDerivAt A (deriv A t) t :=
    (hasDerivAt_normalizedDescFactorialPolynomial c r t).differentiableAt.hasDerivAt
  have hAdd : HasDerivAt (deriv A) (deriv (deriv A) t) t :=
    (hasDerivAt_deriv_normalizedDescFactorialPolynomial c r t).differentiableAt.hasDerivAt
  have hAc := hAd.comp u hInv
  have hDc := hAdd.comp u hInv
  have hFull := hInv.sub (((hInv.pow 2).div_const (r : Real)).mul
    (hDc.fun_div hAc hA))
  have hNe := hAc.continuousAt.tendsto.eventually (eventually_ne_nhds hA)
  have heq : Filter.EventuallyEq (nhds u)
      (fun v : Real => factorialConvolution c (r - 1) v / factorialConvolution c r v)
      (fun v : Real => (r : Real) / v - (((r : Real) / v) ^ 2 / r) *
        (deriv A ((r : Real) / v) / A ((r : Real) / v))) := by
    apply ((eventually_ne_nhds hu).and hNe).mono
    intro v hv
    simpa only [A, mul_div_assoc] using
      factorialConvolution_ratio_eq_normalized_logDeriv c r hr v hv.1 hv.2
  convert hFull.congr_of_eventuallyEq heq using 1
  dsimp [A, t]
  field_simp
  ring

theorem deriv_factorialConvolution_ratio
    (c : Nat -> Real) (r : Nat) (hr : 0 < r) (u : Real) (hu : Not (u = 0))
    (hA : Not (normalizedDescFactorialPolynomial c r ((r : Real) / u) = 0)) :
    deriv (fun v : Real => factorialConvolution c (r - 1) v / factorialConvolution c r v) u =
      -(r : Real) / u ^ 2 +
        (2 * ((r : Real) / u) *
          (deriv (normalizedDescFactorialPolynomial c r) ((r : Real) / u) /
            normalizedDescFactorialPolynomial c r ((r : Real) / u)) +
          ((r : Real) / u) ^ 2 *
            (deriv (deriv (normalizedDescFactorialPolynomial c r)) ((r : Real) / u) /
              normalizedDescFactorialPolynomial c r ((r : Real) / u) -
              (deriv (normalizedDescFactorialPolynomial c r) ((r : Real) / u) /
                normalizedDescFactorialPolynomial c r ((r : Real) / u)) ^ 2)) / u ^ 2 :=
  (hasDerivAt_factorialConvolution_ratio c r hr u hu hA).deriv

theorem abs_deriv_factorialConvolution_ratio_add_le
    (c : Nat -> Real) (r : Nat) (hr : 0 < r) (u b d M : Real)
    (hu : 0 < u) (htb : (r : Real) / u <= b) (hd : 0 < d) (hM : 0 <= M)
    (hA : d <= normalizedDescFactorialPolynomial c r ((r : Real) / u))
    (hD : abs (deriv (normalizedDescFactorialPolynomial c r) ((r : Real) / u)) <= M)
    (hDD : abs (deriv (deriv (normalizedDescFactorialPolynomial c r)) ((r : Real) / u)) <= M) :
    abs (deriv (fun v : Real => factorialConvolution c (r - 1) v / factorialConvolution c r v) u +
      (r : Real) / u ^ 2) <=
        (2 * b * (M / d) + b ^ 2 * (M / d + (M / d) ^ 2)) / u ^ 2 := by
  let A := normalizedDescFactorialPolynomial c r
  let t := (r : Real) / u
  let q := deriv A t / A t
  let s := deriv (deriv A) t / A t
  let Q := M / d
  have ht : 0 <= t := div_nonneg (Nat.cast_nonneg r) hu.le
  have hb : 0 <= b := ht.trans htb
  have hQ : 0 <= Q := div_nonneg hM hd.le
  have hApos : 0 < A t := hd.trans_le hA
  have hq : abs q <= Q := by
    dsimp [q, Q]
    rw [abs_div, abs_of_pos hApos]
    exact (div_le_div_of_nonneg_right hD hApos.le).trans
      (div_le_div_of_nonneg_left hM hd hA)
  have hs : abs s <= Q := by
    dsimp [s, Q]
    rw [abs_div, abs_of_pos hApos]
    exact (div_le_div_of_nonneg_right hDD hApos.le).trans
      (div_le_div_of_nonneg_left hM hd hA)
  have hsub : abs (s - q ^ 2) <= Q + Q ^ 2 := by
    calc
      abs (s - q ^ 2) <= abs s + abs (q ^ 2) := abs_sub _ _
      _ <= Q + Q ^ 2 := by rw [abs_pow]; gcongr
  have hnum : abs (2 * t * q + t ^ 2 * (s - q ^ 2)) <=
      2 * b * Q + b ^ 2 * (Q + Q ^ 2) := by
    calc
      abs (2 * t * q + t ^ 2 * (s - q ^ 2)) <=
          abs (2 * t * q) + abs (t ^ 2 * (s - q ^ 2)) := by
        simpa only [Real.norm_eq_abs] using norm_add_le (2 * t * q) (t ^ 2 * (s - q ^ 2))
      _ = 2 * t * abs q + t ^ 2 * abs (s - q ^ 2) := by
        rw [abs_mul (2 * t) q, abs_mul (t ^ 2) (s - q ^ 2),
          abs_of_nonneg (by positivity : 0 <= 2 * t),
          abs_of_nonneg (sq_nonneg t)]
      _ <= 2 * b * Q + b ^ 2 * (Q + Q ^ 2) := by
        gcongr
  have hExact := deriv_factorialConvolution_ratio c r hr u hu.ne' hApos.ne'
  change deriv (fun v : Real => factorialConvolution c (r - 1) v / factorialConvolution c r v) u =
    -(r : Real) / u ^ 2 + (2 * t * q + t ^ 2 * (s - q ^ 2)) / u ^ 2 at hExact
  rw [hExact]
  have hCancel : -(r : Real) / u ^ 2 + (2 * t * q + t ^ 2 * (s - q ^ 2)) / u ^ 2 +
      (r : Real) / u ^ 2 = (2 * t * q + t ^ 2 * (s - q ^ 2)) / u ^ 2 := by ring
  rw [hCancel, abs_div, abs_of_nonneg (sq_nonneg u)]
  exact div_le_div_of_nonneg_right hnum (sq_nonneg u)

end Nat


/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/

import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# PerturbedQRHGeometry

Maintained extraction of completed detector/packet proof components.
All original theorem hypotheses and retained proof bodies are preserved.
This module alone asserts no improved zero-free boundary.
-/

set_option autoImplicit false
set_option Elab.async false

/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/

/-!
# Uniform endpoint certificate for a small QRH geometry perturbation

This proves the rational endpoint and the complete rescaled low consumer.
It proves no new zero-free strip: the analytic adapters, including their
principal continuation below 7/8, are separate mathematical obligations.
The balanced row exponent is the original source count at kappa = 3/4.
-/


noncomputable section
namespace PrimeFactorOscillations.PerturbedQRHGeometry

def polyP (y : Real) : Real := (7 + 18 * y + 8 * y ^ 2) / 9

def polyD (y : Real) : Real := (37 + 34 * y) / 18

def crossingJ (delta y : Real) : Real :=
  (5 / 6 - delta) * polyD y + delta * polyP y

def balancedRow (delta y : Real) : Real :=
  1 - delta + (5 / 6 - delta) * delta * polyP y / (2 * crossingJ delta y)

def baseEnergy (delta y R : Real) : Real :=
  -1 / 48 + 2 * delta / 3 + (1 / 2 - y) * delta / 6 - 13 / 16 * (1 - R)

def highEndpoint (eps delta y R : Real) : Real :=
  (1 + delta) / 2 - (7 / 8 - eps / 4) +
    (13 / 16 + 3 * eps / 2) * (17 / 50 - 1 / 6) -
    (1 + delta) / 2 * (23 / 48 - eps / 2) -
    (1 / 6 + eps) / 2 + (1 / 2 - y) * delta * (1 / 6 + eps) +
    (13 / 16 + 3 * eps / 2) * (R + delta / 2 - 17 / 50)

theorem crossing_bounds (delta y : Real)
    (hd0 : 0 <= delta) (hd1 : delta <= 5 / 6)
    (hy0 : 0 <= y) (hy1 : y <= 1 / 2) :
    And (35 / 54 <= crossingJ delta y) (crossingJ delta y <= 5 / 2) := by
  have hP0 : 7 / 9 <= polyP y := by
    dsimp [polyP]
    nlinarith [sq_nonneg y]
  have hP1 : polyP y <= 2 := by
    dsimp [polyP]
    nlinarith [mul_nonneg hy0 (show 0 <= 1 / 2 - y by linarith)]
  have hD0 : 7 / 9 <= polyD y := by dsimp [polyD]; linarith
  have hD1 : polyD y <= 3 := by dsimp [polyD]; linarith
  have hdiff : 0 <= 5 / 6 - delta := by linarith
  constructor
  . dsimp [crossingJ]
    nlinarith [mul_nonneg hdiff (sub_nonneg.mpr hD0),
      mul_nonneg hd0 (sub_nonneg.mpr hP0)]
  . dsimp [crossingJ]
    nlinarith [mul_nonneg hdiff (sub_nonneg.mpr hD1),
      mul_nonneg hd0 (sub_nonneg.mpr hP1)]

theorem endpoint_identity (delta y : Real)
    (hJ : Not (crossingJ delta y = 0)) :
    10368 * (51 + 41 * y) * crossingJ delta y *
        (-baseEnergy delta y (balancedRow delta y)) =
      (3 + 5 * y) * ((4 * (51 + 41 * y) * delta - 79) ^ 2 + 49) +
      4 * y * (4 * (51 + 41 * y) * delta *
        ((1 + 3 * y) * (15 + 32 * y) * delta + 9 - 13 * y) +
        265 + 3485 * y) := by
  unfold baseEnergy balancedRow
  field_simp
  dsimp [crossingJ, polyP, polyD]
  ring

theorem original_endpoint_margin (delta y : Real)
    (hd0 : 0 <= delta) (hd1 : delta <= 5 / 6)
    (hy0 : 0 <= y) (hy1 : y <= 1 / 2) :
    baseEnergy delta y (balancedRow delta y) <= -49 / 440640 := by
  have hbounds := crossing_bounds delta y hd0 hd1 hy0 hy1
  have hJ : 0 < crossingJ delta y := by linarith [hbounds.1]
  have hv : 0 < 51 + 41 * y := by linarith
  have hpoly : 0 <=
      4 * y * (4 * (51 + 41 * y) * delta *
        ((1 + 3 * y) * (15 + 32 * y) * delta + 9 - 13 * y) +
        265 + 3485 * y) := by
    have hbracket : 0 <=
        (1 + 3 * y) * (15 + 32 * y) * delta + 9 - 13 * y := by
      have hprod : 0 <= (1 + 3 * y) * (15 + 32 * y) * delta := by positivity
      linarith
    positivity
  have hsquare : 0 <= (3 + 5 * y) *
      (4 * (51 + 41 * y) * delta - 79) ^ 2 := by positivity
  have hidentity := endpoint_identity delta y (ne_of_gt hJ)
  have hscaled :
      (51 + 41 * y) * 49 <= (51 + 41 * y) *
        (176256 * crossingJ delta y *
          (-baseEnergy delta y (balancedRow delta y))) := by
    nlinarith [hpoly, hsquare]
  have hmain : 49 <= 176256 * crossingJ delta y *
      (-baseEnergy delta y (balancedRow delta y)) := by
    by_contra h
    have hneg : 176256 * crossingJ delta y *
        (-baseEnergy delta y (balancedRow delta y)) - 49 < 0 := by linarith
    have hbad := mul_neg_of_pos_of_neg hv hneg
    nlinarith [hscaled]
  have hsign : 0 <= -baseEnergy delta y (balancedRow delta y) := by
    by_contra h
    have hnonpos : -baseEnergy delta y (balancedRow delta y) <= 0 :=
      le_of_not_ge h
    have hprod := mul_nonpos_of_nonneg_of_nonpos (le_of_lt hJ) hnonpos
    nlinarith
  have hupper := mul_nonneg
    (show 0 <= 5 / 2 - crossingJ delta y by linarith [hbounds.2]) hsign
  nlinarith

theorem balanced_row_upper (delta y : Real)
    (hd0 : 0 <= delta) (hd1 : delta <= 5 / 6)
    (hy0 : 0 <= y) (hy1 : y <= 1 / 2) :
    balancedRow delta y <= 17 / 12 := by
  have hbounds := crossing_bounds delta y hd0 hd1 hy0 hy1
  have hJ : 0 < crossingJ delta y := by linarith [hbounds.1]
  have hdiff : 0 <= 5 / 6 - delta := by linarith
  have hD : 0 <= polyD y := by dsimp [polyD]; linarith
  have hJpart : 0 <= crossingJ delta y - delta * polyP y := by
    dsimp [crossingJ]
    nlinarith [mul_nonneg hdiff hD]
  have hterm : (5 / 6 - delta) * delta * polyP y /
      (2 * crossingJ delta y) <= (5 / 6 - delta) / 2 := by
    have hcancel : 2 * crossingJ delta y *
        ((5 / 6 - delta) * delta * polyP y / (2 * crossingJ delta y)) =
        (5 / 6 - delta) * delta * polyP y := by
      field_simp
    have hcompare : (5 / 6 - delta) * delta * polyP y <=
        2 * crossingJ delta y * ((5 / 6 - delta) / 2) := by
      nlinarith [mul_nonneg hdiff hJpart]
    by_contra h
    have hpos : 0 < (5 / 6 - delta) * delta * polyP y /
        (2 * crossingJ delta y) - (5 / 6 - delta) / 2 := by linarith
    have hbad := mul_pos (by positivity : 0 < 2 * crossingJ delta y) hpos
    nlinarith [hcancel, hcompare]
  dsimp [balancedRow]
  linarith

theorem endpoint_sensitivity (eps delta y R : Real) :
    highEndpoint eps delta y R =
      baseEnergy delta y R +
        eps * (3 * R / 2 + delta + (1 / 2 - y) * delta - 1 / 4) := by
  dsimp [highEndpoint, baseEnergy]
  ring

theorem perturbed_endpoint_margin (eps delta y : Real)
    (he0 : 0 <= eps) (he1 : eps <= 1 / 100000)
    (hd0 : 0 <= delta) (hd1 : delta <= 5 / 6)
    (hy0 : 0 <= y) (hy1 : y <= 1 / 2) :
    highEndpoint eps delta y (balancedRow delta y) <= -11 / 160000 := by
  have hbase := original_endpoint_margin delta y hd0 hd1 hy0 hy1
  have hrow := balanced_row_upper delta y hd0 hd1 hy0 hy1
  have hcoeff :
      3 * balancedRow delta y / 2 + delta + (1 / 2 - y) * delta - 1 / 4 <=
        25 / 8 := by
    nlinarith [mul_nonneg hy0 hd0]
  have hcost := mul_le_mul_of_nonneg_left hcoeff he0
  rw [endpoint_sensitivity]
  linarith

theorem complete_low_consumer (ell d : Real)
    (hell : ell <= 1 / 5) (hd : 0 <= d) :
    -d + max 0 ((5 * ell + d - 1) / 4) / 2 <= 0 := by
  by_cases h : (5 * ell + d - 1) / 4 <= 0
  . rw [max_eq_left h]
    linarith
  . have h' : 0 <= (5 * ell + d - 1) / 4 := le_of_lt (lt_of_not_ge h)
    rw [max_eq_right h']
    linarith

theorem signal_and_low (eps : Real) :
    And ((17 / 48 - eps / 2) / 2 - 1 +
      (13 / 16 + 3 * eps / 2) / 6 = (-11 / 16 : Real))
      ((17 / 48 - eps / 2) / 2 + (1 / 8 : Real) / 12 =
        (7 / 8 - eps / 4) - 11 / 16) := by
  constructor <;> ring

end PrimeFactorOscillations.PerturbedQRHGeometry


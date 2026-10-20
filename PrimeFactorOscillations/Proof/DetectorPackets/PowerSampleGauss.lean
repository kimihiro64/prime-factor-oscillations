/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/

import OAI.NumberTheory.DirichletL.Detector.Gauss

/-!
# PowerSampleGauss

Maintained extraction of completed detector/packet proof components.
All original theorem hypotheses and retained proof bodies are preserved.
This module alone asserts no improved zero-free boundary.
-/

set_option autoImplicit false
set_option Elab.async false

namespace OAI.SevenEighths.ProbePowerGauss

open scoped BigOperators Classical
noncomputable section
open ProbeGauss

variable {F : Type*} [Field F] [Fintype F]

theorem frequency_power_scale (chi : MulChar F Complex)
    (psi : AddChar F Complex) (h r : F) {d : Nat}
    (hr : Not (r = 0)) :
    frequencyGauss chi psi (h * r ^ d) =
      (chi ^ (-1 : Int)) (r ^ d) * frequencyGauss chi psi h := by
  have he := frequencyGauss_nonzero chi (psi.mulShift h) (pow_ne_zero d hr)
  simpa only [frequencyGauss, AddChar.mulShift_apply, gaussSum, mul_assoc,
    zpow_neg_one] using he

theorem scaled_power_correlation (chi xi : MulChar F Complex)
    (psi : AddChar F Complex) (h : F) {d : Nat} (hd : 0 < d) :
    (Finset.univ.sum fun r : F =>
      xi r ^ d * frequencyGauss chi psi (h * r ^ d)) =
      frequencyGauss chi psi h *
        (if (xi * chi ^ (-1 : Int)) ^ d = 1
          then (Fintype.card (Units F) : Complex) else 0) := by
  have hd0 : Not (d = 0) := Nat.ne_of_gt hd
  have ht (r : F) :
      xi r ^ d * frequencyGauss chi psi (h * r ^ d) =
        frequencyGauss chi psi h * ((xi * chi ^ (-1 : Int)) ^ d) r := by
    by_cases hr : r = 0
    case pos =>
      subst r
      rw [MulChar.map_zero, zero_pow hd0, zero_mul, MulChar.map_zero, mul_zero]
    case neg =>
      rw [frequency_power_scale chi psi h r hr, map_pow,
        MulChar.pow_apply' _ hd0, MulChar.mul_apply]
      ring
  simp_rw [ht]
  rw [<- Finset.mul_sum]
  congr 1
  by_cases he : (xi * chi ^ (-1 : Int)) ^ d = 1
  case pos =>
    rw [if_pos he, he]
    exact MulChar.sum_one_eq_card_units
  case neg =>
    rw [if_neg he]
    exact MulChar.sum_eq_zero_of_ne_one he

theorem power_frequency_term (chi xi : MulChar F Complex)
    (psi : AddChar F Complex) {d : Nat} (hd : 0 < d) (r : F) :
    xi r ^ d * frequencyGauss chi psi (-(r ^ d)) =
      frequencyGauss chi psi (-1) * ((xi * chi ^ (-1 : Int)) ^ d) r := by
  have hd0 : Not (d = 0) := Nat.ne_of_gt hd
  by_cases hr : r = 0
  case pos =>
    subst r
    rw [MulChar.map_zero, zero_pow hd0, zero_mul, MulChar.map_zero, mul_zero]
  case neg =>
    rw [frequencyGauss_nonzero chi psi (neg_ne_zero.mpr (pow_ne_zero d hr)),
      frequencyGauss_nonzero chi psi (neg_ne_zero.mpr one_ne_zero)]
    rw [show -(r ^ d) = (-1) * r ^ d by ring, map_mul, map_pow]
    rw [MulChar.pow_apply' _ hd0, MulChar.mul_apply]
    simp only [zpow_neg_one]
    ring

theorem power_fourier (chi xi : MulChar F Complex)
    (psi psiFourier : AddChar F Complex) {d : Nat} (hd : 0 < d) (h : F) :
    (Finset.univ.sum fun r : F =>
      (xi r ^ d * frequencyGauss chi psi (-(r ^ d))) *
        psiFourier (h * r)) =
      frequencyGauss chi psi (-1) *
        frequencyGauss ((xi * chi ^ (-1 : Int)) ^ d) psiFourier h := by
  simp_rw [power_frequency_term chi xi psi hd, mul_assoc]
  rw [<- Finset.mul_sum]
  rfl

theorem power_correlation (chi xi : MulChar F Complex)
    (psi : AddChar F Complex) {d : Nat} (hd : 0 < d) :
    (Finset.univ.sum fun r : F =>
      xi r ^ d * frequencyGauss chi psi (-(r ^ d))) =
      frequencyGauss chi psi (-1) *
        (if (xi * chi ^ (-1 : Int)) ^ d = 1
          then (Fintype.card (Units F) : Complex) else 0) := by
  simp_rw [power_frequency_term chi xi psi hd]
  rw [<- Finset.mul_sum]
  congr 1
  by_cases h : (xi * chi ^ (-1 : Int)) ^ d = 1
  case pos =>
    rw [if_pos h, h]
    exact MulChar.sum_one_eq_card_units
  case neg =>
    rw [if_neg h]
    exact MulChar.sum_eq_zero_of_ne_one h

theorem sextic_fourth_resonance (rho : MulChar F Complex)
    (h6 : rho ^ 6 = 1) :
    rho ^ 4 = 1 <-> rho ^ 2 = 1 := by
  constructor
  case mp =>
    intro h4
    have he : rho ^ 6 = rho ^ 4 * rho ^ 2 := by
      rw [<- pow_add]
    rw [h6, h4, one_mul] at he
    exact he.symm
  case mpr =>
    intro h2
    calc
      rho ^ 4 = (rho ^ 2) ^ 2 := by rw [<- pow_mul]
      _ = 1 := by rw [h2, one_pow]

theorem fourth_correlation (chi xi : MulChar F Complex)
    (psi : AddChar F Complex)
    (h6 : (xi * chi ^ (-1 : Int)) ^ 6 = 1) :
    (Finset.univ.sum fun r : F =>
      xi r ^ 4 * frequencyGauss chi psi (-(r ^ 4))) =
      frequencyGauss chi psi (-1) *
        (if (xi * chi ^ (-1 : Int)) ^ 2 = 1
          then (Fintype.card (Units F) : Complex) else 0) := by
  rw [power_correlation chi xi psi (by decide : 0 < 4)]
  rw [sextic_fourth_resonance _ h6]

theorem diagonal_correlation (chi : MulChar F Complex)
    (psi : AddChar F Complex) {d : Nat} (hd : 0 < d) :
    (Finset.univ.sum fun r : F =>
      chi r ^ d * frequencyGauss chi psi (-(r ^ d))) =
      frequencyGauss chi psi (-1) *
        (Fintype.card (Units F) : Complex) := by
  rw [power_correlation chi chi psi hd]
  simp only [zpow_neg_one, mul_inv_cancel, one_pow, ite_true]

end
end OAI.SevenEighths.ProbePowerGauss

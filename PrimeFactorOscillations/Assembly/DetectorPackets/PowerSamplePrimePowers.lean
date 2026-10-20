/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/

import OAI.NumberTheory.DirichletL.Detector.PrimePower
import PrimeFactorOscillations.Proof.DetectorPackets.PowerSampleGauss

/-!
# PowerSamplePrimePowers

Maintained extraction of completed detector/packet proof components.
All original theorem hypotheses and retained proof bodies are preserved.
This module alone asserts no improved zero-free boundary.
-/

set_option autoImplicit false
set_option Elab.async false

namespace OAI.SevenEighths.ProbePowerGauss

open scoped BigOperators Classical
noncomputable section
open ActualEisensteinCubic ProbePrimePower ProbeGauss GaussianShiftedPartition CubicEisenstein

local notation "O" => ActualEisensteinCubic.O
local notation "Res" p => HasQuotient.Quotient O (Ideal.span {p})

theorem lifted_power_correlation (p : O) (hp : Not (p = 0))
    [(Ideal.span {p} : Ideal O).IsMaximal]
    (chi xi : MulChar (Res p) Complex) (n : Nat) (h : O)
    {d : Nat} (hd : 0 < d) :
    (tsum fun r : Res p =>
      xi r ^ d * primePowerGauss p hp chi n
        (p ^ n * (h * representative p r ^ d))) =
      (Ideal.absNorm (Ideal.span {p}) : Complex) ^ n * primeGauss p hp chi h *
        (if (xi * chi ^ (-1 : Int)) ^ d = 1
          then (Nat.card (Units (Res p)) : Complex) else 0) := by
  let : Field (Res p) := Ideal.Quotient.field _
  let : Finite (Res p) := ConcreteTraceCRT.finite_quotient_span hp
  let : Fintype (Res p) := Fintype.ofFinite _
  have hfreq (a : O) :
      primeGauss p hp chi a =
        frequencyGauss chi (quotientTrace p hp) (Ideal.Quotient.mk _ a) := by
    rw [primeGauss, tsum_fintype]
    rfl
  simp_rw [primePowerGauss_lift, hfreq, map_mul, map_pow, representative_spec]
  rw [tsum_fintype]
  calc
    _ = (Ideal.absNorm (Ideal.span {p}) : Complex) ^ n *
        (Finset.univ.sum fun r : Res p =>
          xi r ^ d * frequencyGauss chi (quotientTrace p hp)
            (Ideal.Quotient.mk _ h * r ^ d)) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro r _
      ring
    _ = _ := by
      rw [scaled_power_correlation chi xi (quotientTrace p hp) _ hd,
        Nat.card_eq_fintype_card]
      ring

theorem power_correlation_off_support (p : O) (hp : Prime p)
    [(Ideal.span {p} : Ideal O).IsMaximal]
    (chi xi : MulChar (Res p) Complex) {n v d : Nat}
    (hv : v < n) (hd : 0 < d) :
    (tsum fun r : Res p =>
      xi r ^ d * primePowerGauss p hp.ne_zero chi n
        (-(p ^ v * representative p r ^ d))) = 0 := by
  calc
    _ = tsum (fun _ : Res p => (0 : Complex)) := by
      apply tsum_congr
      intro r
      by_cases hr : r = 0
      case pos =>
        subst r
        rw [MulChar.map_zero, zero_pow (Nat.ne_of_gt hd), zero_mul]
      case neg =>
        have hrep : Not (Dvd.dvd p (representative p r)) := by
          intro hpr
          have hz : Ideal.Quotient.mk (Ideal.span {p}) (representative p r) = 0 :=
            Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton.mpr hpr)
          rw [representative_spec] at hz
          exact hr hz
        have hoff : Not (Dvd.dvd (p ^ n) (-(p ^ v * representative p r ^ d))) := by
          intro hn
          have hm := dvd_neg.mp hn
          have hsucc : Dvd.dvd (p ^ (v + 1)) (p ^ v * representative p r ^ d) :=
            (pow_dvd_pow p (by omega : v + 1 <= n)).trans hm
          rw [pow_succ] at hsucc
          have hpr := (mul_dvd_mul_iff_left (pow_ne_zero v hp.ne_zero)).mp hsucc
          exact hrep (hp.dvd_of_dvd_pow hpr)
        rw [primePowerGauss_zero_off_support p hp.ne_zero chi n _ hoff, mul_zero]
    _ = 0 := tsum_zero

theorem lifted_nonprincipal_extra_valuation (p : O) (hp : Not (p = 0))
    [(Ideal.span {p} : Ideal O).IsMaximal]
    (chi xi : MulChar (Res p) Complex) (hchi : Not (chi = 1))
    (n j d : Nat) (hj : 0 < j) :
    (tsum fun r : Res p =>
      xi r ^ d * primePowerGauss p hp chi n
        (p ^ n * (-(p ^ j * representative p r ^ d)))) = 0 := by
  calc
    _ = tsum (fun _ : Res p => (0 : Complex)) := by
      apply tsum_congr
      intro r
      rw [primePowerGauss_nonprincipal_extra_divisibility p hp chi hchi]
      exact mul_zero _
      exact dvd_neg.mpr ((dvd_pow_self p (Nat.ne_of_gt hj)).mul_right _)
    _ = 0 := tsum_zero

end
end OAI.SevenEighths.ProbePowerGauss

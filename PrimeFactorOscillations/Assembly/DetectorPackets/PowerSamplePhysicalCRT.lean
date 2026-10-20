/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/

import OAI.NumberTheory.DirichletL.Detector.PhysicalCRT
import PrimeFactorOscillations.Assembly.DetectorPackets.PowerSampleJointFourier

/-!
# PowerSamplePhysicalCRT

Maintained extraction of completed detector/packet proof components.
All original theorem hypotheses and retained proof bodies are preserved.
This module alone asserts no improved zero-free boundary.
-/

set_option autoImplicit false
set_option Elab.async false

set_option maxHeartbeats 2200000

noncomputable section
namespace OAI.SevenEighths.ProbePowerGauss
open scoped Classical BigOperators
open ActualEisensteinCubic ConcreteTraceCRT CubicEisenstein CanonicalRowCompletion
open GaussianShiftedPartition CanonicalQuadraticSieve
open CenteredMomentCommonSupport CenteredMomentFourier CenteredMomentSupportedCorrelation
open ProbePhysical
local notation "O" => ActualEisensteinCubic.O

def powerPhysicalFourier (d : Nat) (A s : O)
    (hA : Not (A = 0)) (hs : Not (s = 0)) (H : O) : Complex :=
  elementFourier (A * s) (mul_ne_zero hA hs)
    (fun r => idealRowHom (r ^ d) (Ideal.span {A}) *
      sexticGauss s hs (-(r ^ d))) H

theorem moving_power_mk (d : Nat) (A s : O) (hs : Not (s = 0)) (r : O) :
    movingQuotient A s hs ((Ideal.Quotient.mk (Ideal.span {A * s}) r) ^ d) =
      idealRowHom (r ^ d) (Ideal.span {A}) * sexticGauss s hs (-(r ^ d)) := by
  rw [<-map_pow, movingQuotient_mk]

theorem moving_power_unit_scale (d : Nat) (A s : O)
    (hs : Supported (Ideal.span {s})) (b : O) (hcop : IsCoprime b s)
    (x : Residue (A * s)) :
    movingQuotient A s (supportedElement_ne_zero s hs)
      ((Ideal.Quotient.mk (Ideal.span {A * s}) b * x) ^ d) =
    (idealRowHom (b ^ d) (Ideal.span {A}) *
      (idealRowHom (b ^ d) (Ideal.span {s})) ^ (-1 : Int)) *
        movingQuotient A s (supportedElement_ne_zero s hs) (x ^ d) := by
  rw [mul_pow, <-map_pow, movingQuotient_unit_scale A s hs (b ^ d) hcop.pow_left,
    zpow_neg_one]

theorem powerPhysicalFourier_eq_sum (d : Nat) (A s : O)
    (hA : Not (A = 0)) (hs : Not (s = 0))
    [Fintype (Residue (A * s))] (H : O) :
    powerPhysicalFourier d A s hA hs H =
      Finset.univ.sum (fun x : Residue (A * s) =>
        movingQuotient A s hs (x ^ d) *
          quotientTrace (A * s) (mul_ne_zero hA hs)
            (Ideal.Quotient.mk (Ideal.span {A * s}) H * x)) := by
  unfold powerPhysicalFourier elementFourier
  rw [tsum_fintype]
  apply Finset.sum_congr rfl
  intro x hx
  congr 1
  simpa only [representative_spec] using
    (moving_power_mk d A s hs (representative (A * s) x)).symm

theorem powerPhysicalFourier_product (d : Nat) (A B s t : O)
    (hA : Not (A = 0)) (hB : Not (B = 0))
    (hs : Supported (Ideal.span {s})) (ht : Supported (Ideal.span {t}))
    (hcop : IsCoprime (A * s) (B * t)) (H : O) :
    powerPhysicalFourier d (A * B) (s * t) (mul_ne_zero hA hB)
      (mul_ne_zero (supportedElement_ne_zero s hs) (supportedElement_ne_zero t ht)) H =
    (idealRowHom t (Ideal.span {s}) * idealRowHom s (Ideal.span {t})) *
      (idealRowHom ((B * t) ^ d) (Ideal.span {A}) *
        (idealRowHom ((B * t) ^ d) (Ideal.span {s})) ^ (-1 : Int)) *
      (idealRowHom ((A * s) ^ d) (Ideal.span {B}) *
        (idealRowHom ((A * s) ^ d) (Ideal.span {t})) ^ (-1 : Int)) *
      powerPhysicalFourier d A s hA (supportedElement_ne_zero s hs) H *
      powerPhysicalFourier d B t hB (supportedElement_ne_zero t ht) H := by
  have hst : IsCoprime s t := hcop.of_mul_left_right.of_mul_right_right
  have hc1 : IsCoprime (B * t) s := hcop.of_mul_left_right.symm
  have hc2 : IsCoprime (A * s) t := hcop.of_mul_right_right
  have hAs := mul_ne_zero hA (supportedElement_ne_zero s hs)
  have hBt := mul_ne_zero hB (supportedElement_ne_zero t ht)
  let := finite_quotient_span hAs
  let := finite_quotient_span hBt
  let := finite_quotient_span (mul_ne_zero hAs hBt)
  let : Fintype (Residue (A * s)) := Fintype.ofFinite _
  let : Fintype (Residue (B * t)) := Fintype.ofFinite _
  let : Fintype (Residue ((A * s) * (B * t))) := Fintype.ofFinite _
  have he := coprime_function_fourier (A * s) (B * t) hAs hBt hcop
    (fun x => movingQuotient A s (supportedElement_ne_zero s hs) (x ^ d))
    (fun x => movingQuotient B t (supportedElement_ne_zero t ht) (x ^ d))
    (Ideal.Quotient.mk (Ideal.span {(A * s) * (B * t)}) H)
  simp only [frequencyReduction_mk] at he
  simp_rw [moving_power_unit_scale d A s hs (B * t) hc1,
    moving_power_unit_scale d B t ht (A * s) hc2, mul_assoc] at he
  simp only [<-Finset.mul_sum] at he
  have hexpand : elementFourier ((A * s) * (B * t)) (mul_ne_zero hAs hBt)
      (fun r =>
        (idealRowHom (r ^ d) (Ideal.span {A}) *
          sexticGauss s (supportedElement_ne_zero s hs) (-(r ^ d))) *
        (idealRowHom (r ^ d) (Ideal.span {B}) *
          sexticGauss t (supportedElement_ne_zero t ht) (-(r ^ d)))) H =
      (idealRowHom ((B * t) ^ d) (Ideal.span {A}) *
        (idealRowHom ((B * t) ^ d) (Ideal.span {s})) ^ (-1 : Int)) *
      (idealRowHom ((A * s) ^ d) (Ideal.span {B}) *
        (idealRowHom ((A * s) ^ d) (Ideal.span {t})) ^ (-1 : Int)) *
      powerPhysicalFourier d A s hA (supportedElement_ne_zero s hs) H *
      powerPhysicalFourier d B t hB (supportedElement_ne_zero t ht) H := by
    unfold elementFourier
    rw [tsum_fintype]
    calc
      _ = Finset.univ.sum (fun x : Residue ((A * s) * (B * t)) =>
          movingQuotient A s (supportedElement_ne_zero s hs)
            ((frequencyReduction (A * s) ((A * s) * (B * t))
              (dvd_mul_right _ _) x) ^ d) *
          movingQuotient B t (supportedElement_ne_zero t ht)
            ((frequencyReduction (B * t) ((A * s) * (B * t))
              (dvd_mul_left _ _) x) ^ d) *
          quotientTrace ((A * s) * (B * t)) (mul_ne_zero hAs hBt)
            (Ideal.Quotient.mk (Ideal.span {(A * s) * (B * t)}) H * x)) := by
        apply Finset.sum_congr rfl
        intro x hx
        have hm := representative_spec ((A * s) * (B * t)) x
        have hred1 : frequencyReduction (A * s) ((A * s) * (B * t))
            (dvd_mul_right _ _) x =
            Ideal.Quotient.mk (Ideal.span {A * s})
              (representative ((A * s) * (B * t)) x) := by
          conv_lhs => rw [<-hm]
          rfl
        have hred2 : frequencyReduction (B * t) ((A * s) * (B * t))
            (dvd_mul_left _ _) x =
            Ideal.Quotient.mk (Ideal.span {B * t})
              (representative ((A * s) * (B * t)) x) := by
          conv_lhs => rw [<-hm]
          rfl
        rw [hred1, hred2, moving_power_mk, moving_power_mk]
      _ = _ := by
        simpa only [mul_assoc] using he
      _ = _ := by
        rw [powerPhysicalFourier_eq_sum d A s hA (supportedElement_ne_zero s hs) H,
          powerPhysicalFourier_eq_sum d B t hB (supportedElement_ne_zero t ht) H]
        ring
  unfold powerPhysicalFourier
  rw [elementFourier_congr ((A * B) * (s * t)) ((A * s) * (B * t)) _
    (mul_ne_zero hAs hBt) _ H (by ring)]
  simp_rw [bareMoving_product A B s t hs ht hst]
  rw [elementFourier_const_mul, hexpand]
  simp only [powerPhysicalFourier, mul_assoc]

open EisensteinSchwartzPoisson

theorem power_row_poisson (d : Nat) (A s : O)
    (hA : Not (A = 0)) (hs : Not (s = 0))
    (W : Real -> Complex) (hWc : HasCompactSupport W)
    (hWs : ContDiff Real ((Top.top : ENat) : WithTop ENat) W)
    (K : Real) (hK : 0 < K) :
    (tsum fun r : O =>
      (idealRowHom (r ^ d) (Ideal.span {A}) * sexticGauss s hs (-(r ^ d))) *
        W (elementNorm r / K)) =
      ((K / elementNorm (A * s) : Real) : Complex) *
        tsum (fun H : O => powerPhysicalFourier d A s hA hs H *
          paperRadialFourier W (K * elementNorm H / elementNorm (A * s))) := by
  have hc := mul_ne_zero hA hs
  let := finite_quotient_span hc
  let : Fintype (Residue (A * s)) := Fintype.ofFinite _
  have ht := EisensteinSchwartzPoisson.actual_compact_radial_paper_poisson_trace
    W hWc hWs K hK (A * s) hc (fun x => movingQuotient A s hs (x ^ d))
  change (tsum fun r : O =>
    movingQuotient A s hs ((Ideal.Quotient.mk (Ideal.span {A * s}) r) ^ d) *
      W (norm (eisEmbedding r) ^ 2 / K)) =
    (K / norm (eisEmbedding (A * s)) ^ 2 : Real) *
      tsum (fun H : O =>
        (Finset.univ.sum (fun x : Residue (A * s) =>
          movingQuotient A s hs (x ^ d) *
            quotientTrace (A * s) hc
              (Ideal.Quotient.mk (Ideal.span {A * s}) H * x))) *
          paperRadialFourier W
            (K * norm (eisEmbedding H) ^ 2 / norm (eisEmbedding (A * s)) ^ 2)) at ht
  simp_rw [moving_power_mk, eisEmbedding_norm_sq_eq_absNorm_span,
    <-powerPhysicalFourier_eq_sum d A s hA hs] at ht
  exact ht

end OAI.SevenEighths.ProbePowerGauss

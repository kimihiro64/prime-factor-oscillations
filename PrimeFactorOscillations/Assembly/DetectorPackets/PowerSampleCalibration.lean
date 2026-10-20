/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/

import PrimeFactorOscillations.Assembly.DetectorPackets.PowerSamplePhysicalCRT

/-!
# PowerSampleCalibration

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
open ProbePhysical EisensteinSchwartzPoisson
local notation "O" => ActualEisensteinCubic.O

def calibrationPowerGauss (d : Nat) (C : CalibrationData) (H : O) : Complex :=
  tsum fun x : Residue C.generator =>
    C.residue (x ^ d) * quotientTrace C.generator C.generator_ne_zero
      (Ideal.Quotient.mk (Ideal.span {C.generator}) H * x)

def calibratedPowerQuotient (d : Nat) (C : CalibrationData) (A s : O)
    (hs : Not (s = 0)) (x : Residue (C.generator * (A * s))) : Complex :=
  C.residue ((frequencyReduction C.generator (C.generator * (A * s))
    (dvd_mul_right _ _) x) ^ d) *
  movingQuotient A s hs
    ((frequencyReduction (A * s) (C.generator * (A * s))
      (dvd_mul_left _ _) x) ^ d)

def calibratedPowerFourier (d : Nat) (C : CalibrationData) (A s : O)
    (hA : Not (A = 0)) (hs : Not (s = 0)) (H : O) : Complex :=
  tsum fun x : Residue (C.generator * (A * s)) =>
    calibratedPowerQuotient d C A s hs x *
      quotientTrace (C.generator * (A * s))
        (mul_ne_zero C.generator_ne_zero (mul_ne_zero hA hs))
        (Ideal.Quotient.mk (Ideal.span {C.generator * (A * s)}) H * x)

theorem calibrated_power_mk (d : Nat) (C : CalibrationData) (A s : O)
    (hs : Not (s = 0)) (r : O) :
    calibratedPowerQuotient d C A s hs
      (Ideal.Quotient.mk (Ideal.span {C.generator * (A * s)}) r) =
    C.residueMonoid (r ^ d) *
      (idealRowHom (r ^ d) (Ideal.span {A}) * sexticGauss s hs (-(r ^ d))) := by
  unfold calibratedPowerQuotient
  simp only [frequencyReduction_mk, moving_power_mk]
  rfl

theorem calibrated_power_fourier_factor (d : Nat) (C : CalibrationData)
    (A s : O) (hA : Not (A = 0)) (hs : Supported (Ideal.span {s}))
    (hcop : IsCoprime C.generator (A * s)) (H : O) :
    calibratedPowerFourier d C A s hA (supportedElement_ne_zero s hs) H =
    C.residueMonoid ((A * s) ^ d) *
      (idealRowHom (C.generator ^ d) (Ideal.span {A}) *
        (idealRowHom (C.generator ^ d) (Ideal.span {s})) ^ (-1 : Int)) *
      calibrationPowerGauss d C H *
      powerPhysicalFourier d A s hA (supportedElement_ne_zero s hs) H := by
  have hAs := mul_ne_zero hA (supportedElement_ne_zero s hs)
  let := finite_quotient_span C.generator_ne_zero
  let := finite_quotient_span hAs
  let := finite_quotient_span (mul_ne_zero C.generator_ne_zero hAs)
  let : Fintype (Residue C.generator) := Fintype.ofFinite _
  let : Fintype (Residue (A * s)) := Fintype.ofFinite _
  let : Fintype (Residue (C.generator * (A * s))) := Fintype.ofFinite _
  have he := coprime_function_fourier C.generator (A * s)
    C.generator_ne_zero hAs hcop (fun x => C.residue (x ^ d))
    (fun x => movingQuotient A s (supportedElement_ne_zero s hs) (x ^ d))
    (Ideal.Quotient.mk (Ideal.span {C.generator * (A * s)}) H)
  simp only [frequencyReduction_mk] at he
  have hc (x : Residue C.generator) :
      C.residue ((Ideal.Quotient.mk (Ideal.span {C.generator}) (A * s) * x) ^ d) =
      C.residueMonoid ((A * s) ^ d) * C.residue (x ^ d) := by
    rw [mul_pow, map_mul]
    rfl
  simp_rw [hc, moving_power_unit_scale d A s hs C.generator
    hcop.of_mul_right_right, mul_assoc] at he
  simp only [<-Finset.mul_sum] at he
  unfold calibratedPowerFourier calibratedPowerQuotient
  rw [tsum_fintype]
  simp only [mul_assoc]
  rw [he]
  rw [powerPhysicalFourier_eq_sum d A s hA (supportedElement_ne_zero s hs) H]
  unfold calibrationPowerGauss
  rw [tsum_fintype]
  ring

theorem calibrated_power_row_poisson (d : Nat) (C : CalibrationData) (A s : O)
    (hA : Not (A = 0)) (hs : Not (s = 0))
    (W : Real -> Complex) (hWc : HasCompactSupport W)
    (hWs : ContDiff Real ((Top.top : ENat) : WithTop ENat) W)
    (K : Real) (hK : 0 < K) :
    (tsum fun r : O =>
      (C.residueMonoid (r ^ d) *
        (idealRowHom (r ^ d) (Ideal.span {A}) * sexticGauss s hs (-(r ^ d)))) *
          W (elementNorm r / K)) =
    ((K / elementNorm (C.generator * (A * s)) : Real) : Complex) *
      tsum (fun H : O => calibratedPowerFourier d C A s hA hs H *
        paperRadialFourier W
          (K * elementNorm H / elementNorm (C.generator * (A * s)))) := by
  have hb := mul_ne_zero C.generator_ne_zero (mul_ne_zero hA hs)
  let := finite_quotient_span hb
  let : Fintype (Residue (C.generator * (A * s))) := Fintype.ofFinite _
  have ht := EisensteinSchwartzPoisson.actual_compact_radial_paper_poisson_trace
    W hWc hWs K hK (C.generator * (A * s)) hb
    (calibratedPowerQuotient d C A s hs)
  change (tsum fun r : O =>
    calibratedPowerQuotient d C A s hs
      (Ideal.Quotient.mk (Ideal.span {C.generator * (A * s)}) r) *
      W (norm (eisEmbedding r) ^ 2 / K)) =
    (K / norm (eisEmbedding (C.generator * (A * s))) ^ 2 : Real) *
      tsum (fun H : O =>
        (Finset.univ.sum (fun x : Residue (C.generator * (A * s)) =>
          calibratedPowerQuotient d C A s hs x *
            quotientTrace (C.generator * (A * s)) hb
              (Ideal.Quotient.mk (Ideal.span {C.generator * (A * s)}) H * x))) *
          paperRadialFourier W
            (K * norm (eisEmbedding H) ^ 2 /
              norm (eisEmbedding (C.generator * (A * s))) ^ 2)) at ht
  simp_rw [calibrated_power_mk, eisEmbedding_norm_sq_eq_absNorm_span] at ht
  simpa only [calibratedPowerFourier, tsum_fintype, elementNorm] using ht

end OAI.SevenEighths.ProbePowerGauss


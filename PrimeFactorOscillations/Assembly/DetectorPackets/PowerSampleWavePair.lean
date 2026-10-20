/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/

import PrimeFactorOscillations.Assembly.DetectorPackets.PowerSampleCalibration
import PrimeFactorOscillations.Assembly.DetectorPackets.PowerSampleWaveKernel

/-!
# PowerSampleWavePair

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
open ActualEisensteinCubic ConcretePrimeRowBridge CubicEisenstein
open ProbeGauss ProbePrimePower ProbeEuler ProbePhysical
local notation "O" => ActualEisensteinCubic.O
local notation "Res" p => HasQuotient.Quotient O (Ideal.span {p})

theorem sextic_second_fourth_conjugate {F : Type*} [Field F] [Fintype F]
    (chi : MulChar F Complex) (h6 : chi ^ 6 = 1) (h : F) :
    star ((chi ^ 4) h) = (chi ^ 2) h := by
  have hi : (chi ^ 4) ^ (-1 : Int) = chi ^ 2 := by
    rw [zpow_neg_one]
    apply inv_eq_of_mul_eq_one_right
    rw [<-pow_add]
    exact h6
  calc
    _ = ((chi ^ 4) ^ (-1 : Int)) h := by
      simpa only [zpow_neg_one] using MulChar.star_apply' (chi ^ 4) h
    _ = _ := by rw [hi]

theorem inverse_cubic_wave_product (p : O) (hp : Prime p)
    [(Ideal.span {p} : Ideal O).IsMaximal]
    (hg : Not (Membership.mem (Ideal.span {p}) goodLambda))
    (hc : Not (ringChar (Res p) = 2))
    (hprimary : Dvd.dvd (goodLambda ^ 2) (p - 1)) (h : O) :
    -(primeGauss p hp.ne_zero
        (CompletedGauss.actualSextic (Ideal.span {p}) hg ^ 4) h) /
      (primeGauss p hp.ne_zero
        (CompletedGauss.actualSextic (Ideal.span {p}) hg) 1 *
          (Ideal.absNorm (Ideal.span {p}) : Complex)) =
    star (FiniteGaussPhase.angularFactor p * MixedGaussConversion.localG p hp.ne_zero hg *
      (CompletedGauss.actualSextic (Ideal.span {p}) hg ^ 4)
        (Ideal.Quotient.mk (Ideal.span {p}) h)) /
      (Ideal.absNorm (Ideal.span {p}) : Complex) := by
  letI : Field (Res p) := Ideal.Quotient.field _
  letI : Fintype (Res p) := Fintype.ofFinite _
  let chi := CompletedGauss.actualSextic (Ideal.span {p}) hg
  let A := FiniteGaussPhase.angularFactor p * MixedGaussConversion.localG p hp.ne_zero hg
  let Q : Complex := Ideal.absNorm (Ideal.span {p})
  let root : Complex := Real.sqrt (Ideal.absNorm (Ideal.span {p}) : Real)
  have hsig : localGamma p hp.ne_zero hg 1 * localGamma p hp.ne_zero hg 2 = -A := by
    simpa only [A, neg_mul] using localGamma_one_two_signal p hp.ne_zero hg hc hprimary
  have hn1 := localGamma_norm_one p hp.ne_zero hg hc 1 (by decide) (by decide)
  have hn2 := localGamma_norm_one p hp.ne_zero hg hc 2 (by decide) (by decide)
  have h1 : Not (localGamma p hp.ne_zero hg 1 = 0) :=
    norm_ne_zero_iff.mp (by rw [hn1]; exact one_ne_zero)
  have h2 : Not (localGamma p hp.ne_zero hg 2 = 0) :=
    norm_ne_zero_iff.mp (by rw [hn2]; exact one_ne_zero)
  have hAnorm : norm A = 1 := by
    have he := congrArg norm hsig
    simpa only [norm_mul, norm_neg, hn1, hn2, one_mul] using he.symm
  have hAi : A ^ (-1 : Int) = star A := by
    simpa only [zpow_neg_one, starRingEnd_apply] using Complex.inv_eq_conj hAnorm
  have hqpos : 0 < (Ideal.absNorm (Ideal.span {p}) : Real) := by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr
      (Ideal.span_singleton_eq_bot.not.mpr hp.ne_zero))
  have hQ : Not (Q = 0) := by
    change Not ((Ideal.absNorm (Ideal.span {p}) : Complex) = 0)
    exact_mod_cast hqpos.ne'
  have hr : Not (root = 0) := by
    change Not ((Real.sqrt (Ideal.absNorm (Ideal.span {p}) : Real) : Complex) = 0)
    exact_mod_cast (Real.sqrt_pos.mpr hqpos).ne'
  have hraw : primeGauss p hp.ne_zero chi 1 =
      localGamma p hp.ne_zero hg 1 * root := firstGauss_eq_gamma_sqrt p hp hg
  have hi := inverse_cubic_fourier_product p hp.ne_zero hg hc h
  have hi' : localGamma p hp.ne_zero hg 2 *
      primeGauss p hp.ne_zero (chi ^ 4) h =
      (chi ^ 2) (Ideal.Quotient.mk (Ideal.span {p}) h) * root := by
    apply (div_eq_iff hr).mp
    simpa only [mul_div_assoc] using hi
  change -(primeGauss p hp.ne_zero (chi ^ 4) h) /
      (primeGauss p hp.ne_zero chi 1 * Q) =
    star (A * (chi ^ 4) (Ideal.Quotient.mk (Ideal.span {p}) h)) / Q
  rw [star_mul, sextic_second_fourth_conjugate chi (actualSextic_six _ hg hc)]
  rw [<-hAi, hraw, zpow_neg_one]
  have hA : Not (A = 0) := norm_ne_zero_iff.mp (by rw [hAnorm]; exact one_ne_zero)
  calc
    _ = -(localGamma p hp.ne_zero hg 2 *
          primeGauss p hp.ne_zero (chi ^ 4) h) /
        ((localGamma p hp.ne_zero hg 1 * localGamma p hp.ne_zero hg 2) * root * Q) := by
      field_simp
      <;> ring
    _ = _ := by
      rw [hi', hsig]
      field_simp
      <;> ring

theorem actual_fourth_cubic_wave_pair (p : O) (hp : Prime p)
    [(Ideal.span {p} : Ideal O).IsMaximal]
    (hg : Not (Membership.mem (Ideal.span {p}) goodLambda))
    (hc : Not (ringChar (Res p) = 2))
    (hprimary : Dvd.dvd (goodLambda ^ 2) (p - 1))
    (eta X W : Complex) (h : O) :
    let chi := CompletedGauss.actualSextic (Ideal.span {p}) hg
    let Q : Complex := Ideal.absNorm (Ideal.span {p})
    let B : Complex := FiniteGaussPhase.angularFactor p *
      MixedGaussConversion.localG p hp.ne_zero hg *
        (chi ^ 4) (Ideal.Quotient.mk (Ideal.span {p}) h)
    (-eta * X / primeGauss p hp.ne_zero chi 1) *
        primeGauss p hp.ne_zero (chi ^ 4) h / Q +
      W * primeGauss p hp.ne_zero chi (-1) *
        primeGauss p hp.ne_zero (chi ^ 2) h / Q =
      eta * X * star B / Q - W * chi (-1) * B := by
  dsimp only
  have hi := inverse_cubic_wave_product p hp hg hc hprimary h
  have hs := source_cubic_fourier_product p hp.ne_zero hg hc hprimary h
  calc
    _ = eta * X *
        (-(primeGauss p hp.ne_zero
          (CompletedGauss.actualSextic (Ideal.span {p}) hg ^ 4) h) /
          (primeGauss p hp.ne_zero
            (CompletedGauss.actualSextic (Ideal.span {p}) hg) 1 *
              (Ideal.absNorm (Ideal.span {p}) : Complex))) +
      W * (primeGauss p hp.ne_zero
          (CompletedGauss.actualSextic (Ideal.span {p}) hg) (-1) *
        primeGauss p hp.ne_zero
          (CompletedGauss.actualSextic (Ideal.span {p}) hg ^ 2) h /
            (Ideal.absNorm (Ideal.span {p}) : Complex)) := by ring
    _ = _ := by
      rw [hi, hs]
      ring

end OAI.SevenEighths.ProbePowerGauss


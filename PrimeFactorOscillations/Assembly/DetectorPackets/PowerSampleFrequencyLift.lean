/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/

import OAI.NumberTheory.DirichletL.Detector.PhysicalFourier
import PrimeFactorOscillations.Assembly.DetectorPackets.PowerSampleWavePair

/-!
# PowerSampleFrequencyLift

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
open ActualEisensteinCubic CubicEisenstein ProbeGauss ProbePrimePower ProbePhysical
local notation "O" => ActualEisensteinCubic.O
local notation "Res" p => HasQuotient.Quotient O (Ideal.span {p})

local instance quotientField (p : O) [(Ideal.span {p} : Ideal O).IsMaximal] :
    Field (Res p) := Ideal.Quotient.field _
local instance quotientFintype (p : O) [(Ideal.span {p} : Ideal O).IsMaximal] :
    Fintype (Res p) := Fintype.ofFinite _

def liftedFourthPrimeFourier (p : O) (hp : Not (p = 0))
    [(Ideal.span {p} : Ideal O).IsMaximal]
    (chi : MulChar (Res p) Complex) (n e l k : Nat) (H : O) : Complex :=
  conductorFourier p (p ^ n) hp (pow_ne_zero _ hp)
    (fun r => chi r ^ (4 * (e + 3 * l)) *
      frequencyGauss chi (quotientTrace p hp) (-(r ^ 4)) ^ k) H

theorem liftedFourthPrimeFourier_lift (p : O) (hp : Not (p = 0))
    [(Ideal.span {p} : Ideal O).IsMaximal]
    (chi : MulChar (Res p) Complex) (n e l k : Nat) (h : O) :
    liftedFourthPrimeFourier p hp chi n e l k (p ^ n * h) =
      (Ideal.absNorm (Ideal.span {p}) : Complex) ^ (n + 1) *
        fourthPrimeFourier chi (quotientTrace p hp) e l k
          (Ideal.Quotient.mk (Ideal.span {p}) h) := by
  have hcard : Fintype.card (Res p) = Ideal.absNorm (Ideal.span {p}) := by
    rw [<-Nat.card_eq_fintype_card]
    rfl
  have hq : Not ((Ideal.absNorm (Ideal.span {p}) : Complex) = 0) := by
    exact_mod_cast Ideal.absNorm_eq_zero_iff.not.mpr
      (Ideal.span_singleton_eq_bot.not.mpr hp)
  have hn : Ideal.absNorm (Ideal.span {p ^ n}) = Ideal.absNorm (Ideal.span {p}) ^ n := by
    rw [<-Ideal.span_singleton_pow, map_pow]
  unfold liftedFourthPrimeFourier
  rw [conductorFourier_lift, hn, Nat.cast_pow, tsum_fintype]
  unfold fourthPrimeFourier
  rw [hcard, pow_succ]
  field_simp
  <;> simp only [mul_comm]
  <;> ring

theorem liftedFourthPrimeFourier_off_support (p : O) (hp : Not (p = 0))
    [(Ideal.span {p} : Ideal O).IsMaximal]
    (chi : MulChar (Res p) Complex) (n e l k : Nat) (H : O)
    (hdiv : Not (Dvd.dvd (p ^ n) H)) :
    liftedFourthPrimeFourier p hp chi n e l k H = 0 := by
  by_contra he
  exact hdiv (conductorFourier_support p (p ^ n) hp (pow_ne_zero _ hp) _ H he)

theorem liftedFourthPrimeFourier_coprime_vanish (p : O) (hp : Not (p = 0))
    [(Ideal.span {p} : Ideal O).IsMaximal]
    (chi : MulChar (Res p) Complex) (n e l k : Nat) (H : O)
    (hn : 0 < n) (hH : Not (Dvd.dvd p H)) :
    liftedFourthPrimeFourier p hp chi n e l k H = 0 := by
  apply liftedFourthPrimeFourier_off_support p hp chi n e l k H
  intro hd
  exact hH ((dvd_pow_self p (Nat.ne_of_gt hn)).trans hd)

end OAI.SevenEighths.ProbePowerGauss


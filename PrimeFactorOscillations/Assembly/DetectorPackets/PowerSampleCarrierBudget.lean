/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/

import PrimeFactorOscillations.Assembly.DetectorPackets.PowerSampleCarrierNorm

/-!
# PowerSampleCarrierBudget

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
open ActualEisensteinCubic ConcreteTraceCRT CubicEisenstein ConcretePrimeRowBridge
open GaussianShiftedPartition ProbeGauss ProbePrimePower ProbePhysical ProbeEuler
local notation "O" => ActualEisensteinCubic.O
local notation "Res" p => HasQuotient.Quotient O (Ideal.span {p})

local instance budgetCarrierField (p : O) [(Ideal.span {p} : Ideal O).IsMaximal] :
    Field (Res p) := Ideal.Quotient.field _
local instance budgetCarrierFintype (p : O) [(Ideal.span {p} : Ideal O).IsMaximal] :
    Fintype (Res p) := Fintype.ofFinite _

def fourthCarrierState (p : O) (hp : Prime p)
    [(Ideal.span {p} : Ideal O).IsMaximal]
    (hg : Not (Membership.mem (Ideal.span {p}) goodLambda))
    (eta a C X W : Complex) (e l k : Nat) (H : O) : Complex :=
  let chi := CompletedGauss.actualSextic (Ideal.span {p}) hg
  weightedScalar (Ideal.absNorm (Ideal.span {p}) : Complex) eta a
    (primeGauss p hp.ne_zero chi 1) C (chi (-1)) X W 1
    (fourthCarrierLocalFourier p hp.ne_zero chi e l k H) e l k 0

theorem fourthCarrierBase_norm (p : O) (hp : Prime p)
    [(Ideal.span {p} : Ideal O).IsMaximal]
    (hg : Not (Membership.mem (Ideal.span {p}) goodLambda))
    (hc : Not (ringChar (Res p) = 2))
    (eta a C X W : Complex) (hC : norm C <= 1) (l : Nat) (H : O) :
    norm (fourthCarrierState p hp hg eta a C X W 0 l 0 H) <=
      norm (a * X ^ 3 / (Ideal.absNorm (Ideal.span {p}) : Complex)) ^ l := by
  let chi := CompletedGauss.actualSextic (Ideal.span {p}) hg
  have hPhi : norm (fourthCarrierLocalFourier p hp.ne_zero chi 0 l 0 H) <= 1 := by
    by_cases hl : l = 0
    case pos =>
      subst l
      simp only [fourthCarrierLocalFourier, Nat.mul_zero, Nat.zero_add, ite_true, norm_one, le_refl]
    case neg =>
      apply fourthCarrierLocalFourier_norm_of_primitive p hp.ne_zero chi 0 l 0 (by omega)
        1 (by norm_num)
      intro h
      rw [fourthPrimeFourier_no_source chi (actualSextic_six _ hg hc)
        (quotientTrace p hp.ne_zero) 0 l (by decide)]
      simp only [ite_true, if_neg hl]
      have hcard : Fintype.card (Res p) = Ideal.absNorm (Ideal.span {p}) := by
        rw [<-Nat.card_eq_fintype_card]
        rfl
      rw [hcard]
      exact principal_frequency_average_norm_le p hp.ne_zero h
  have hphase := localCubePhase_norm_le_one C (chi (-1)) hC
    (FiniteRayExpansion.norm_char_le_one _ _) 0 l 0
  unfold fourthCarrierState weightedScalar
  dsimp only
  simp only [pow_zero, one_mul, mul_one]
  rw [norm_mul, norm_mul, norm_pow]
  have hinner := (mul_le_of_le_one_left (norm_nonneg
    (fourthCarrierLocalFourier p hp.ne_zero chi 0 l 0 H)) hphase).trans hPhi
  simpa only [mul_assoc] using mul_le_of_le_one_right
    (pow_nonneg (norm_nonneg
      (a * X ^ 3 / (Ideal.absNorm (Ideal.span {p}) : Complex))) l) hinner

theorem fourthCarrierShared_norm (p : O) (hp : Prime p)
    [(Ideal.span {p} : Ideal O).IsMaximal]
    (hg : Not (Membership.mem (Ideal.span {p}) goodLambda))
    (hc : Not (ringChar (Res p) = 2))
    (eta a C X W : Complex) (hC : norm C <= 1) (l : Nat) (H : O) :
    norm (fourthCarrierState p hp hg eta a C X W 1 l 1 H) <=
      norm (a * X ^ 3 / (Ideal.absNorm (Ideal.span {p}) : Complex)) ^ l *
        norm (eta * X * W) := by
  let chi := CompletedGauss.actualSextic (Ideal.span {p}) hg
  let psi := quotientTrace p hp.ne_zero
  let q : Complex := Ideal.absNorm (Ideal.span {p})
  let G1 := primeGauss p hp.ne_zero chi 1
  let omega := chi (-1)
  have h6 : chi ^ 6 = 1 := actualSextic_six _ hg hc
  have h2 : Not (chi ^ 2 = 1) := by
    intro he
    have hd := (actualSextic_pow_eq_one_iff _ hg hc 2).mp he
    omega
  have ho : omega ^ 2 = 1 := actualSextic_neg_one_sq _ hg
  have hG1 : Not (G1 = 0) := firstGauss_ne_zero p hp hg hc
  have hq : Not (q = 0) := primeNorm_ne_zero p hp
  have hraw : gaussSum chi psi = G1 := by
    simp only [G1, psi, primeGauss, gaussSum, tsum_fintype, map_one, one_mul]
  have hminus : frequencyGauss chi psi (-1) = omega * G1 := by
    rw [frequencyGauss_nonzero chi psi (neg_ne_zero.mpr one_ne_zero), hraw]
    simp only [MulChar.inv_apply', inv_neg_one, omega]
  by_cases hd : Dvd.dvd (p ^ (3 * l + 1)) H
  case pos =>
    choose h he using hd
    have hLift := fourthCarrierLocalFourier_lift p hp.ne_zero chi 1 l 1 (by omega) h
    simp only [show 1 + 3 * l + 1 - 1 = 3 * l + 1 by omega] at hLift
    have hval : fourthCarrierState p hp hg eta a C X W 1 l 1 H =
        -(eta * X * W) * (a * X ^ 3 / q) ^ l * localCubePhase C omega 0 l 0 *
          (frequencyGauss 1 psi (Ideal.Quotient.mk (Ideal.span {p}) h) / q) := by
      unfold fourthCarrierState
      dsimp only
      rw [he, hLift, fourthPrimeFourier_source chi h6 h2 psi 1 l (by decide)]
      simp only [Nat.one_ne_zero, ite_false]
      have hcard : Fintype.card (Res p) = Ideal.absNorm (Ideal.span {p}) := by
        rw [<-Nat.card_eq_fintype_card]
        rfl
      rw [hcard]
      unfold weightedScalar
      simp only [pow_one, pow_zero, mul_one, one_mul]
      calc
        _ = -(eta * X * W) * (a * X ^ 3 / q) ^ l *
            (localCubePhase C omega 1 l 1 * omega) *
              (frequencyGauss 1 psi (Ideal.Quotient.mk (Ideal.span {p}) h) / q) := by
          rw [hminus]
          dsimp only [chi, G1, q, omega] at hG1 hq
          dsimp only [chi, G1, q, omega]
          field_simp [hG1, hq]
          <;> ring
        _ = _ := by rw [cubePhase_shared_cancel C omega ho]
    rw [hval, norm_mul, norm_mul, norm_mul, norm_neg, norm_pow]
    have hphase := localCubePhase_norm_le_one C omega hC
      (FiniteRayExpansion.norm_char_le_one _ _) 0 l 0
    have hR := principal_frequency_average_norm_le p hp.ne_zero h
    have hinner := (mul_le_of_le_one_left (norm_nonneg
      (frequencyGauss 1 psi (Ideal.Quotient.mk (Ideal.span {p}) h) / q)) hphase).trans hR
    have hprod := mul_le_of_le_one_right
      (mul_nonneg (norm_nonneg (eta * X * W))
        (pow_nonneg (norm_nonneg (a * X ^ 3 / q)) l)) hinner
    simpa only [mul_assoc, mul_comm, mul_left_comm, q] using hprod
  case neg =>
    have hz : fourthCarrierLocalFourier p hp.ne_zero chi 1 l 1 H = 0 := by
      unfold fourthCarrierLocalFourier
      rw [if_neg (by omega : Not (1 + 3 * l + 1 = 0)),
        show 1 + 3 * l + 1 - 1 = 3 * l + 1 by omega,
        liftedFourthPrimeFourier_off_support p hp.ne_zero chi _ 1 l 1 H hd, zero_div]
    unfold fourthCarrierState
    dsimp only
    rw [hz]
    simp only [weightedScalar, mul_zero, zero_mul, norm_zero]
    positivity

end OAI.SevenEighths.ProbePowerGauss


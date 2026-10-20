/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/

import OAI.NumberTheory.DirichletL.Detector.LocalSeries
import PrimeFactorOscillations.Assembly.DetectorPackets.PowerSampleValuationCarrier

/-!
# PowerSampleCarrierNorm

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

local instance normCarrierField (p : O) [(Ideal.span {p} : Ideal O).IsMaximal] :
    Field (Res p) := Ideal.Quotient.field _
local instance normCarrierFintype (p : O) [(Ideal.span {p} : Ideal O).IsMaximal] :
    Fintype (Res p) := Fintype.ofFinite _

theorem actual_fourthPhase_norm_le_one (p : O) (hp : Prime p)
    [(Ideal.span {p} : Ideal O).IsMaximal]
    (hg : Not (Membership.mem (Ideal.span {p}) goodLambda))
    (hc : Not (ringChar (Res p) = 2))
    (hprimary : Dvd.dvd (goodLambda ^ 2) (p - 1)) (H : O) :
    norm (FiniteGaussPhase.angularFactor p * MixedGaussConversion.localG p hp.ne_zero hg *
      (CompletedGauss.actualSextic (Ideal.span {p}) hg ^ 4)
        (Ideal.Quotient.mk (Ideal.span {p}) H)) <= 1 := by
  have hsig := localGamma_one_two_signal p hp.ne_zero hg hc hprimary
  have hn1 := localGamma_norm_one p hp.ne_zero hg hc 1 (by decide) (by decide)
  have hn2 := localGamma_norm_one p hp.ne_zero hg hc 2 (by decide) (by decide)
  have hA : norm (FiniteGaussPhase.angularFactor p *
      MixedGaussConversion.localG p hp.ne_zero hg) = 1 := by
    have he := congrArg norm hsig
    simpa only [norm_mul, norm_neg, hn1, hn2, one_mul] using he.symm
  rw [norm_mul, hA, one_mul]
  exact FiniteRayExpansion.norm_char_le_one _ _

theorem actual_fourth_wave_norm_le (p : O) (hp : Prime p)
    [(Ideal.span {p} : Ideal O).IsMaximal]
    (hg : Not (Membership.mem (Ideal.span {p}) goodLambda))
    (hc : Not (ringChar (Res p) = 2))
    (hprimary : Dvd.dvd (goodLambda ^ 2) (p - 1))
    (eta X W : Complex) (H : O) :
    let chi := CompletedGauss.actualSextic (Ideal.span {p}) hg
    norm ((-eta * X / primeGauss p hp.ne_zero chi 1) *
        primeGauss p hp.ne_zero (chi ^ 4) H / (Ideal.absNorm (Ideal.span {p}) : Complex) +
      W * primeGauss p hp.ne_zero chi (-1) *
        primeGauss p hp.ne_zero (chi ^ 2) H / (Ideal.absNorm (Ideal.span {p}) : Complex)) <=
      norm (eta * X) / (Ideal.absNorm (Ideal.span {p}) : Real) + norm W := by
  dsimp only
  rw [actual_fourth_cubic_wave_pair p hp hg hc hprimary eta X W H]
  have hB := actual_fourthPhase_norm_le_one p hp hg hc hprimary H
  have ho : norm (CompletedGauss.actualSextic (Ideal.span {p}) hg (-1)) <= 1 :=
    FiniteRayExpansion.norm_char_le_one _ _
  calc
    _ <= norm (eta * X * star (FiniteGaussPhase.angularFactor p *
        MixedGaussConversion.localG p hp.ne_zero hg *
          (CompletedGauss.actualSextic (Ideal.span {p}) hg ^ 4)
            (Ideal.Quotient.mk (Ideal.span {p}) H)) /
              (Ideal.absNorm (Ideal.span {p}) : Complex)) +
      norm (W * CompletedGauss.actualSextic (Ideal.span {p}) hg (-1) *
        (FiniteGaussPhase.angularFactor p * MixedGaussConversion.localG p hp.ne_zero hg *
          (CompletedGauss.actualSextic (Ideal.span {p}) hg ^ 4)
            (Ideal.Quotient.mk (Ideal.span {p}) H))) := norm_sub_le _ _
    _ <= _ := by
      rw [norm_div, norm_mul, norm_star, Complex.norm_natCast, norm_mul, norm_mul]
      have hleft := mul_le_of_le_one_right (norm_nonneg (eta * X)) hB
      have hright : norm W *
          norm (CompletedGauss.actualSextic (Ideal.span {p}) hg (-1)) *
          norm (FiniteGaussPhase.angularFactor p * MixedGaussConversion.localG p hp.ne_zero hg *
            (CompletedGauss.actualSextic (Ideal.span {p}) hg ^ 4)
              (Ideal.Quotient.mk (Ideal.span {p}) H)) <= norm W := by
        have hfirst := mul_le_of_le_one_right (norm_nonneg W) ho
        have hsecond := mul_le_of_le_one_right
          (mul_nonneg (norm_nonneg W)
            (norm_nonneg (CompletedGauss.actualSextic (Ideal.span {p}) hg (-1)))) hB
        linarith
      simpa only [norm_mul] using
        add_le_add (div_le_div_of_nonneg_right hleft (Nat.cast_nonneg _)) hright

theorem principal_frequency_average_norm_le (p : O) (hp : Not (p = 0))
    [(Ideal.span {p} : Ideal O).IsMaximal] (H : O) :
    norm (frequencyGauss (1 : MulChar (Res p) Complex) (quotientTrace p hp)
      (Ideal.Quotient.mk (Ideal.span {p}) H) /
        (Ideal.absNorm (Ideal.span {p}) : Complex)) <= 1 := by
  have hq : 0 < (Ideal.absNorm (Ideal.span {p}) : Real) := by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr
      (Ideal.span_singleton_eq_bot.not.mpr hp))
  have he := rawFourier_norm_le p hp (1 : MulChar (Res p) Complex)
    (fun x => FiniteRayExpansion.norm_char_le_one _ x) H
  have hf : rawFourier p hp (1 : MulChar (Res p) Complex) H =
      frequencyGauss 1 (quotientTrace p hp) (Ideal.Quotient.mk (Ideal.span {p}) H) := by
    rw [rawFourier, tsum_fintype]
    rfl
  rw [hf] at he
  rw [norm_div, Complex.norm_natCast]
  exact (div_le_div_of_nonneg_right he hq.le).trans_eq (div_self hq.ne')

theorem fourthCarrierLocalFourier_norm_of_primitive (p : O) (hp : Not (p = 0))
    [(Ideal.span {p} : Ideal O).IsMaximal]
    (chi : MulChar (Res p) Complex) (e l k : Nat) (hnu : 0 < e + 3 * l + k)
    (L : Real) (hL : 0 <= L)
    (hf : forall h : O, norm (fourthPrimeFourier chi (quotientTrace p hp) e l k
      (Ideal.Quotient.mk (Ideal.span {p}) h)) <= L) (H : O) :
    norm (fourthCarrierLocalFourier p hp chi e l k H) <= L := by
  by_cases hd : Dvd.dvd (p ^ (e + 3 * l + k - 1)) H
  case pos =>
    choose h he using hd
    rw [he, fourthCarrierLocalFourier_lift p hp chi e l k hnu]
    exact hf h
  case neg =>
    unfold fourthCarrierLocalFourier
    rw [if_neg (by omega : Not (e + 3 * l + k = 0)),
      liftedFourthPrimeFourier_off_support p hp chi _ e l k H hd, zero_div, norm_zero]
    exact hL

theorem localCubePhase_norm_le_one (C omega : Complex)
    (hC : norm C <= 1) (ho : norm omega <= 1) (e l k : Nat) :
    norm (localCubePhase C omega e l k) <= 1 := by
  have hp (z : Complex) (hz : norm z <= 1) (n : Nat) : norm (z ^ n) <= 1 := by
    induction n with
    | zero => simp only [pow_zero, norm_one, le_refl]
    | succ n ih =>
      rw [pow_succ, norm_mul]
      exact (mul_le_of_le_one_right (norm_nonneg _) hz).trans ih
  unfold localCubePhase
  rw [norm_mul]
  exact (mul_le_of_le_one_left (norm_nonneg _) (hp C hC l)).trans (hp omega ho _)

def fourthCarrierWaveBlock (p : O) (hp : Prime p)
    [(Ideal.span {p} : Ideal O).IsMaximal]
    (hg : Not (Membership.mem (Ideal.span {p}) goodLambda))
    (eta a C X W : Complex) (l : Nat) (H : O) : Complex :=
  let chi := CompletedGauss.actualSextic (Ideal.span {p}) hg
  let q : Complex := Ideal.absNorm (Ideal.span {p})
  let G1 := primeGauss p hp.ne_zero chi 1
  let omega := chi (-1)
  weightedScalar q eta a G1 C omega X W 1
    (fourthCarrierLocalFourier p hp.ne_zero chi 1 l 0 H) 1 l 0 0 +
  weightedScalar q eta a G1 C omega X W 1
    (fourthCarrierLocalFourier p hp.ne_zero chi 0 l 1 H) 0 l 1 0

theorem fourthCarrierWaveBlock_at_lift (p : O) (hp : Prime p)
    [(Ideal.span {p} : Ideal O).IsMaximal]
    (hg : Not (Membership.mem (Ideal.span {p}) goodLambda))
    (hc : Not (ringChar (Res p) = 2))
    (eta a C X W : Complex) (l : Nat) (h : O) :
    let chi := CompletedGauss.actualSextic (Ideal.span {p}) hg
    let q : Complex := Ideal.absNorm (Ideal.span {p})
    let G1 := primeGauss p hp.ne_zero chi 1
    fourthCarrierWaveBlock p hp hg eta a C X W l (p ^ (3 * l) * h) =
      (a * X ^ 3 / q) ^ l * localCubePhase C (chi (-1)) 1 l 0 *
        ((-eta * X / G1) * primeGauss p hp.ne_zero (chi ^ 4) h / q +
          W * primeGauss p hp.ne_zero chi (-1) *
            primeGauss p hp.ne_zero (chi ^ 2) h / q) := by
  dsimp only
  let chi := CompletedGauss.actualSextic (Ideal.span {p}) hg
  have h6 : chi ^ 6 = 1 := actualSextic_six _ hg hc
  have h2 : Not (chi ^ 2 = 1) := by
    intro he
    have hd := (actualSextic_pow_eq_one_iff _ hg hc 2).mp he
    omega
  have ho := actualSextic_neg_one_sq (Ideal.span {p}) hg
  have h10 := fourthCarrierLocalFourier_lift p hp.ne_zero chi 1 l 0 (by omega) h
  have h01 := fourthCarrierLocalFourier_lift p hp.ne_zero chi 0 l 1 (by omega) h
  simp only [show 1 + 3 * l + 0 - 1 = 3 * l by omega] at h10
  simp only [show 0 + 3 * l + 1 - 1 = 3 * l by omega] at h01
  unfold fourthCarrierWaveBlock
  dsimp only
  rw [h10, h01,
    fourthPrimeFourier_no_source chi h6 (quotientTrace p hp.ne_zero) 1 l (by decide),
    fourthPrimeFourier_source chi h6 h2 (quotientTrace p hp.ne_zero) 0 l (by decide)]
  unfold weightedScalar
  simp only [ite_true, Nat.one_ne_zero, ite_false, pow_zero, pow_one, mul_one, one_mul]
  rw [cubePhase_source_cubic C (chi (-1)) ho]
  have hcard : Fintype.card (Res p) = Ideal.absNorm (Ideal.span {p}) := by
    rw [<-Nat.card_eq_fintype_card]
    rfl
  simp only [chi, frequencyGauss, primeGauss, tsum_fintype, map_neg, map_one, hcard]
  ring

theorem fourthCarrierWaveBlock_norm (p : O) (hp : Prime p)
    [(Ideal.span {p} : Ideal O).IsMaximal]
    (hg : Not (Membership.mem (Ideal.span {p}) goodLambda))
    (hc : Not (ringChar (Res p) = 2))
    (hprimary : Dvd.dvd (goodLambda ^ 2) (p - 1))
    (eta a C X W : Complex) (hC : norm C <= 1) (l : Nat) (H : O) :
    norm (fourthCarrierWaveBlock p hp hg eta a C X W l H) <=
      norm (a * X ^ 3 / (Ideal.absNorm (Ideal.span {p}) : Complex)) ^ l *
        (norm (eta * X) / (Ideal.absNorm (Ideal.span {p}) : Real) + norm W) := by
  let chi := CompletedGauss.actualSextic (Ideal.span {p}) hg
  by_cases hd : Dvd.dvd (p ^ (3 * l)) H
  case pos =>
    choose h he using hd
    rw [he, fourthCarrierWaveBlock_at_lift p hp hg hc eta a C X W l h]
    rw [norm_mul, norm_mul, norm_pow]
    have hphase := localCubePhase_norm_le_one C (chi (-1)) hC
      (FiniteRayExpansion.norm_char_le_one _ _) 1 l 0
    have hT := actual_fourth_wave_norm_le p hp hg hc hprimary eta X W h
    have hprod := mul_le_mul_of_nonneg_left
      ((mul_le_of_le_one_left (norm_nonneg _) hphase).trans hT)
      (pow_nonneg (norm_nonneg
        (a * X ^ 3 / (Ideal.absNorm (Ideal.span {p}) : Complex))) l)
    simpa only [mul_assoc] using hprod
  case neg =>
    have hzero (e k : Nat) (hn : e + 3 * l + k - 1 = 3 * l)
        (hpos : 0 < e + 3 * l + k) :
        fourthCarrierLocalFourier p hp.ne_zero chi e l k H = 0 := by
      unfold fourthCarrierLocalFourier
      rw [if_neg (by omega : Not (e + 3 * l + k = 0)), hn,
        liftedFourthPrimeFourier_off_support p hp.ne_zero chi _ e l k H hd, zero_div]
    unfold fourthCarrierWaveBlock
    dsimp only
    rw [hzero 1 0 (by omega) (by omega), hzero 0 1 (by omega) (by omega)]
    simp only [weightedScalar, mul_zero, zero_mul, zero_add, norm_zero]
    positivity

end OAI.SevenEighths.ProbePowerGauss


/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/

import PrimeFactorOscillations.Assembly.DetectorPackets.PowerSampleEulerCorrection
import PrimeFactorOscillations.Assembly.DetectorPackets.PowerSampleFrequencyLift

/-!
# PowerSampleCarrierPacket

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
open ActualEisensteinCubic CubicEisenstein ProbeGauss ProbePrimePower ProbePhysical ProbeEuler
open ConcretePrimeRowBridge
local notation "O" => ActualEisensteinCubic.O
local notation "Res" p => HasQuotient.Quotient O (Ideal.span {p})

local instance carrierQuotientField (p : O) [(Ideal.span {p} : Ideal O).IsMaximal] :
    Field (Res p) := Ideal.Quotient.field _
local instance carrierQuotientFintype (p : O) [(Ideal.span {p} : Ideal O).IsMaximal] :
    Fintype (Res p) := Fintype.ofFinite _

def fourthCarrierLocalFourier (p : O) (hp : Not (p = 0))
    [(Ideal.span {p} : Ideal O).IsMaximal]
    (chi : MulChar (Res p) Complex) (e l k : Nat) (H : O) : Complex :=
  if e + 3 * l + k = 0 then 1 else
    liftedFourthPrimeFourier p hp chi (e + 3 * l + k - 1) e l k H /
      (Ideal.absNorm (Ideal.span {p}) : Complex) ^ (e + 3 * l + k)

theorem fourthCarrierLocalFourier_vanish (p : O) (hp : Not (p = 0))
    [(Ideal.span {p} : Ideal O).IsMaximal]
    (chi : MulChar (Res p) Complex) (e l k : Nat) (H : O)
    (hnu : 2 <= e + 3 * l + k) (hH : Not (Dvd.dvd p H)) :
    fourthCarrierLocalFourier p hp chi e l k H = 0 := by
  unfold fourthCarrierLocalFourier
  rw [if_neg (by omega : Not (e + 3 * l + k = 0)),
    liftedFourthPrimeFourier_coprime_vanish p hp chi _ e l k H (by omega) hH,
    zero_div]

theorem fourthCarrierLocalFourier_first (p : O) (hp : Not (p = 0))
    [(Ideal.span {p} : Ideal O).IsMaximal]
    (chi : MulChar (Res p) Complex) (e l k : Nat) (H : O)
    (hnu : e + 3 * l + k = 1) :
    fourthCarrierLocalFourier p hp chi e l k H =
      fourthPrimeFourier chi (quotientTrace p hp) e l k
        (Ideal.Quotient.mk (Ideal.span {p}) H) := by
  have hq : Not ((Ideal.absNorm (Ideal.span {p}) : Complex) = 0) := by
    exact_mod_cast Ideal.absNorm_eq_zero_iff.not.mpr
      (Ideal.span_singleton_eq_bot.not.mpr hp)
  have he := liftedFourthPrimeFourier_lift p hp chi 0 e l k H
  simp only [pow_zero, one_mul, zero_add, pow_one] at he
  unfold fourthCarrierLocalFourier
  rw [hnu]
  simp only [Nat.one_ne_zero, ite_false, Nat.sub_self, pow_one, he]
  field_simp

def fourthCarrierCubeBlock (p : O) (hp : Not (p = 0))
    [(Ideal.span {p} : Ideal O).IsMaximal]
    (chi : MulChar (Res p) Complex) (eta a G1 C omega X W : Complex)
    (l : Nat) (H : O) : Complex :=
  Finset.univ.sum (fun e : Fin 2 =>
    Finset.univ.sum (fun k : Fin 2 =>
      weightedScalar (Ideal.absNorm (Ideal.span {p}) : Complex) eta a G1 C omega X W 1
        (fourthCarrierLocalFourier p hp chi e.val l k.val H) e.val l k.val 0))

theorem fourthCarrierCubeBlock_coprime (p : O) (hp : Not (p = 0))
    [(Ideal.span {p} : Ideal O).IsMaximal]
    (chi : MulChar (Res p) Complex) (h6 : chi ^ 6 = 1) (h2 : Not (chi ^ 2 = 1))
    (eta a G1 C omega X W : Complex) (l : Nat) (H : O)
    (hH : Not (Dvd.dvd p H)) :
    let q : Complex := Ideal.absNorm (Ideal.span {p})
    let psi := quotientTrace p hp
    let h := Ideal.Quotient.mk (Ideal.span {p}) H
    fourthCarrierCubeBlock p hp chi eta a G1 C omega X W l H =
      if l = 0 then
        1 + (-eta * X / G1) * frequencyGauss (chi ^ 4) psi h / q +
          W * frequencyGauss chi psi (-1) * frequencyGauss (chi ^ 2) psi h / q
      else 0 := by
  dsimp only
  by_cases hl : l = 0
  case pos =>
    subst l
    unfold fourthCarrierCubeBlock
    simp only [Fin.sum_univ_two, Fin.val_zero, Fin.val_one]
    rw [fourthCarrierLocalFourier_first p hp chi 1 0 0 H (by decide),
      fourthCarrierLocalFourier_first p hp chi 0 0 1 H (by decide),
      fourthCarrierLocalFourier_vanish p hp chi 1 0 1 H (by decide) hH]
    have hbase : fourthCarrierLocalFourier p hp chi 0 0 0 H = 1 := by
      simp only [fourthCarrierLocalFourier, Nat.mul_zero, Nat.add_zero, ite_true]
    rw [hbase]
    rw [fourthPrimeFourier_no_source chi h6 (quotientTrace p hp) 1 0 (by decide),
      fourthPrimeFourier_source chi h6 h2 (quotientTrace p hp) 0 0 (by decide)]
    unfold weightedScalar localCubePhase
    simp only [Nat.zero_add, Nat.add_zero, Nat.mul_zero, Nat.zero_mul, pow_zero,
      pow_one, one_mul, mul_one, mul_zero, zero_mul, ite_true, ite_false, Nat.one_ne_zero,
      Nat.choose_zero_right, Nat.choose_eq_zero_of_lt (by decide : 0 < 2)]
    have hcard : Fintype.card (Res p) = Ideal.absNorm (Ideal.span {p}) := by
      rw [<-Nat.card_eq_fintype_card]
      rfl
    rw [hcard]
    ring
  case neg =>
    have hc (e k : Nat) : fourthCarrierLocalFourier p hp chi e l k H = 0 :=
      fourthCarrierLocalFourier_vanish p hp chi e l k H (by omega) hH
    unfold fourthCarrierCubeBlock
    simp only [hc, weightedScalar, mul_zero, zero_mul, Finset.sum_const_zero, if_neg hl]

theorem fourthCarrierCube_hasSum (p : O) (hp : Not (p = 0))
    [(Ideal.span {p} : Ideal O).IsMaximal]
    (chi : MulChar (Res p) Complex) (h6 : chi ^ 6 = 1) (h2 : Not (chi ^ 2 = 1))
    (eta a G1 C omega X W : Complex) (H : O) (hH : Not (Dvd.dvd p H)) :
    let q : Complex := Ideal.absNorm (Ideal.span {p})
    let psi := quotientTrace p hp
    let h := Ideal.Quotient.mk (Ideal.span {p}) H
    HasSum (fun l : Nat => fourthCarrierCubeBlock p hp chi eta a G1 C omega X W l H)
      (1 + (-eta * X / G1) * frequencyGauss (chi ^ 4) psi h / q +
        W * frequencyGauss chi psi (-1) * frequencyGauss (chi ^ 2) psi h / q) := by
  dsimp only
  convert hasSum_ite_eq (0 : Nat)
    (1 + (-eta * X / G1) *
      frequencyGauss (chi ^ 4) (quotientTrace p hp)
        (Ideal.Quotient.mk (Ideal.span {p}) H) / (Ideal.absNorm (Ideal.span {p}) : Complex) +
      W * frequencyGauss chi (quotientTrace p hp) (-1) *
        frequencyGauss (chi ^ 2) (quotientTrace p hp)
          (Ideal.Quotient.mk (Ideal.span {p}) H) / (Ideal.absNorm (Ideal.span {p}) : Complex)) using 1
  funext l
  exact fourthCarrierCubeBlock_coprime p hp chi h6 h2 eta a G1 C omega X W l H hH

theorem actual_fourthCarrierCube_hasSum (p : O) (hp : Prime p)
    [(Ideal.span {p} : Ideal O).IsMaximal]
    (hg : Not (Membership.mem (Ideal.span {p}) goodLambda))
    (hc : Not (ringChar (Res p) = 2))
    (hprimary : Dvd.dvd (goodLambda ^ 2) (p - 1))
    (eta a C X W : Complex) (H : O) (hH : Not (Dvd.dvd p H)) :
    let chi := CompletedGauss.actualSextic (Ideal.span {p}) hg
    let q : Complex := Ideal.absNorm (Ideal.span {p})
    let B : Complex := FiniteGaussPhase.angularFactor p *
      MixedGaussConversion.localG p hp.ne_zero hg *
        (chi ^ 4) (Ideal.Quotient.mk (Ideal.span {p}) H)
    HasSum (fun l : Nat => fourthCarrierCubeBlock p hp.ne_zero chi eta a
        (primeGauss p hp.ne_zero chi 1) C (chi (-1)) X W l H)
      (1 + eta * X * star B / q - W * chi (-1) * B) := by
  let chi := CompletedGauss.actualSextic (Ideal.span {p}) hg
  have h6 : chi ^ 6 = 1 := actualSextic_six _ hg hc
  have h2 : Not (chi ^ 2 = 1) := by
    intro he
    have hd := (actualSextic_pow_eq_one_iff _ hg hc 2).mp he
    omega
  have he := fourthCarrierCube_hasSum p hp.ne_zero chi h6 h2 eta a
    (primeGauss p hp.ne_zero chi 1) C (chi (-1)) X W H hH
  have hpair := actual_fourth_cubic_wave_pair p hp hg hc hprimary eta X W H
  dsimp only at he hpair
  have hf : (-eta * X / primeGauss p hp.ne_zero chi 1) *
        frequencyGauss (chi ^ 4) (quotientTrace p hp.ne_zero)
          (Ideal.Quotient.mk (Ideal.span {p}) H) /
            (Ideal.absNorm (Ideal.span {p}) : Complex) +
      W * frequencyGauss chi (quotientTrace p hp.ne_zero) (-1) *
        frequencyGauss (chi ^ 2) (quotientTrace p hp.ne_zero)
          (Ideal.Quotient.mk (Ideal.span {p}) H) /
            (Ideal.absNorm (Ideal.span {p}) : Complex) =
      eta * X * star (FiniteGaussPhase.angularFactor p *
        MixedGaussConversion.localG p hp.ne_zero hg *
          (chi ^ 4) (Ideal.Quotient.mk (Ideal.span {p}) H)) /
            (Ideal.absNorm (Ideal.span {p}) : Complex) -
      W * chi (-1) * (FiniteGaussPhase.angularFactor p *
        MixedGaussConversion.localG p hp.ne_zero hg *
          (chi ^ 4) (Ideal.Quotient.mk (Ideal.span {p}) H)) := by
    simpa only [chi, primeGauss, frequencyGauss, tsum_fintype, map_neg, map_one] using hpair
  convert he using 1
  dsimp only [chi] at hf
  linear_combination -hf

end OAI.SevenEighths.ProbePowerGauss


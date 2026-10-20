/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/

import OAI.NumberTheory.DirichletL.Detector.LocalUnitFrequency
import PrimeFactorOscillations.Assembly.DetectorPackets.PowerSampleCarrierPacket

/-!
# PowerSamplePhysicalCarrier

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
open CanonicalRowCompletion GaussianShiftedPartition ProbeGauss ProbePrimePower ProbePhysical
local notation "O" => ActualEisensteinCubic.O
local notation "Res" p => HasQuotient.Quotient O (Ideal.span {p})

local instance physicalCarrierQuotientField (p : O) [(Ideal.span {p} : Ideal O).IsMaximal] :
    Field (Res p) := Ideal.Quotient.field _
local instance physicalCarrierQuotientFintype (p : O) [(Ideal.span {p} : Ideal O).IsMaximal] :
    Fintype (Res p) := Fintype.ofFinite _

theorem sexticGauss_prime_eq_frequency (p : O) (hp : Prime p)
    [(Ideal.span {p} : Ideal O).IsMaximal]
    (hg : Not (Membership.mem (Ideal.span {p}) goodLambda)) (H : O) :
    sexticGauss p hp.ne_zero H =
      frequencyGauss (CompletedGauss.actualSextic (Ideal.span {p}) hg)
        (quotientTrace p hp.ne_zero) (Ideal.Quotient.mk (Ideal.span {p}) H) := by
  have he := sexticGauss_prime_power p hp hg 0 H
  simp only [Nat.zero_add, pow_one] at he
  have hl := primePowerGauss_lift p hp.ne_zero
    (CompletedGauss.actualSextic (Ideal.span {p}) hg) 0 H
  simp only [pow_zero, one_mul] at hl
  rw [he, hl, primeGauss, tsum_fintype]
  rfl

theorem actual_power_prime_function (p : O) (hp : Prime p)
    [(Ideal.span {p} : Ideal O).IsMaximal]
    (hg : Not (Membership.mem (Ideal.span {p}) goodLambda))
    (e l k : Nat) (hk : k <= 1) (r : O) :
    let chi := CompletedGauss.actualSextic (Ideal.span {p}) hg
    idealRowHom (r ^ 4) (Ideal.span {p ^ (e + 3 * l)}) *
        sexticGauss (p ^ k) (pow_ne_zero _ hp.ne_zero) (-(r ^ 4)) =
      chi (Ideal.Quotient.mk (Ideal.span {p}) r) ^ (4 * (e + 3 * l)) *
        frequencyGauss chi (quotientTrace p hp.ne_zero)
          (-((Ideal.Quotient.mk (Ideal.span {p}) r) ^ 4)) ^ k := by
  dsimp only
  rw [idealRowHom_prime_power_value p (r ^ 4) hg,
    map_pow, map_pow, <-pow_mul]
  have hcases : k = 0 \/ k = 1 := by omega
  rcases hcases with rfl | rfl
  case inl =>
    simp only [pow_zero, sexticGauss_one, mul_one]
  case inr =>
    simp only [pow_one]
    rw [sexticGauss_prime_eq_frequency p hp hg, map_neg, map_pow]

theorem powerPhysicalFourier_prime_carrier (p : O) (hp : Prime p)
    [(Ideal.span {p} : Ideal O).IsMaximal]
    (hg : Not (Membership.mem (Ideal.span {p}) goodLambda))
    (e l k : Nat) (hk : k <= 1) (hnu : 0 < e + 3 * l + k) (H : O) :
    powerPhysicalFourier 4 (p ^ (e + 3 * l)) (p ^ k)
      (pow_ne_zero _ hp.ne_zero) (pow_ne_zero _ hp.ne_zero) H =
    liftedFourthPrimeFourier p hp.ne_zero
      (CompletedGauss.actualSextic (Ideal.span {p}) hg)
      (e + 3 * l + k - 1) e l k H := by
  let n := e + 3 * l + k - 1
  have hM : p ^ (e + 3 * l) * p ^ k = p * p ^ n := by
    rw [<-pow_add, <-pow_succ']
    congr 1
    dsimp only [n]
    omega
  unfold powerPhysicalFourier
  rw [elementFourier_congr _ _ _
    (mul_ne_zero hp.ne_zero (pow_ne_zero n hp.ne_zero)) _ H hM]
  unfold elementFourier liftedFourthPrimeFourier conductorFourier
  apply tsum_congr
  intro x
  have hr : conductorReduction p (p ^ n) x =
      Ideal.Quotient.mk (Ideal.span {p}) (representative (p * p ^ n) x) := by
    conv_lhs => rw [<-representative_spec (p * p ^ n) x]
    rfl
  rw [hr]
  dsimp only
  rw [actual_power_prime_function p hp hg e l k hk]

theorem powerPhysicalFourier_one (d : Nat) (H : O) :
    powerPhysicalFourier d 1 1 one_ne_zero one_ne_zero H = 1 := by
  have he : powerPhysicalFourier d 1 1 one_ne_zero one_ne_zero H =
      barePhysicalFourier 1 1 one_ne_zero one_ne_zero H := by
    unfold powerPhysicalFourier barePhysicalFourier
    simp only [sexticGauss_one, mul_one, Ideal.span_singleton_one,
      <-Ideal.one_eq_top, map_one]
  rw [he, barePhysicalFourier_outer_one, sexticGauss_one]

theorem fourthCarrierLocalFourier_physical (p : O) (hp : Prime p)
    [(Ideal.span {p} : Ideal O).IsMaximal]
    (hg : Not (Membership.mem (Ideal.span {p}) goodLambda))
    (e l k : Nat) (hk : k <= 1) (H : O) :
    fourthCarrierLocalFourier p hp.ne_zero
      (CompletedGauss.actualSextic (Ideal.span {p}) hg) e l k H =
    powerPhysicalFourier 4 (p ^ (e + 3 * l)) (p ^ k)
      (pow_ne_zero _ hp.ne_zero) (pow_ne_zero _ hp.ne_zero) H /
        (Ideal.absNorm (Ideal.span {p}) : Complex) ^ (e + 3 * l + k) := by
  by_cases hz : e + 3 * l + k = 0
  case pos =>
    have he : e = 0 := by omega
    have hl : l = 0 := by omega
    have hk0 : k = 0 := by omega
    subst e
    subst l
    subst k
    simp only [fourthCarrierLocalFourier, Nat.mul_zero, Nat.zero_add, pow_zero,
      ite_true, div_one, powerPhysicalFourier_one]
  case neg =>
    unfold fourthCarrierLocalFourier
    rw [if_neg hz, powerPhysicalFourier_prime_carrier p hp hg e l k hk (by omega)]

open ProbeEuler

def fourthPhysicalCubeBlock (p : O) (hp : Prime p)
    [(Ideal.span {p} : Ideal O).IsMaximal]
    (hg : Not (Membership.mem (Ideal.span {p}) goodLambda))
    (eta a C X W : Complex) (l : Nat) (H : O) : Complex :=
  let chi := CompletedGauss.actualSextic (Ideal.span {p}) hg
  Finset.univ.sum (fun e : Fin 2 => Finset.univ.sum (fun k : Fin 2 =>
    weightedScalar (Ideal.absNorm (Ideal.span {p}) : Complex) eta a
      (primeGauss p hp.ne_zero chi 1) C (chi (-1)) X W 1
      (powerPhysicalFourier 4 (p ^ (e.val + 3 * l)) (p ^ k.val)
        (pow_ne_zero _ hp.ne_zero) (pow_ne_zero _ hp.ne_zero) H /
          (Ideal.absNorm (Ideal.span {p}) : Complex) ^ (e.val + 3 * l + k.val))
      e.val l k.val 0))

theorem physical_fourthCarrierCube_hasSum (p : O) (hp : Prime p)
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
    HasSum (fun l : Nat => fourthPhysicalCubeBlock p hp hg eta a C X W l H)
      (1 + eta * X * star B / q - W * chi (-1) * B) := by
  have he := actual_fourthCarrierCube_hasSum p hp hg hc hprimary eta a C X W H hH
  dsimp only at he
  dsimp only
  convert he using 1
  funext l
  unfold fourthPhysicalCubeBlock fourthCarrierCubeBlock
  dsimp only
  apply Finset.sum_congr rfl
  intro e he
  apply Finset.sum_congr rfl
  intro k hk
  rw [fourthCarrierLocalFourier_physical p hp hg e.val l k.val (by omega) H]

end OAI.SevenEighths.ProbePowerGauss


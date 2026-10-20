/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/

import PrimeFactorOscillations.Assembly.DetectorPackets.PowerSamplePhysicalCarrier

/-!
# PowerSampleValuationCarrier

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
open ActualEisensteinCubic ConcreteTraceCRT CubicEisenstein
open GaussianShiftedPartition ProbeGauss ProbePrimePower ProbePhysical
local notation "O" => ActualEisensteinCubic.O
local notation "Res" p => HasQuotient.Quotient O (Ideal.span {p})

local instance valuationCarrierField (p : O) [(Ideal.span {p} : Ideal O).IsMaximal] :
    Field (Res p) := Ideal.Quotient.field _
local instance valuationCarrierFintype (p : O) [(Ideal.span {p} : Ideal O).IsMaximal] :
    Fintype (Res p) := Fintype.ofFinite _

theorem fourthCarrierLocalFourier_lift (p : O) (hp : Not (p = 0))
    [(Ideal.span {p} : Ideal O).IsMaximal]
    (chi : MulChar (Res p) Complex) (e l k : Nat)
    (hnu : 0 < e + 3 * l + k) (h : O) :
    fourthCarrierLocalFourier p hp chi e l k (p ^ (e + 3 * l + k - 1) * h) =
      fourthPrimeFourier chi (quotientTrace p hp) e l k
        (Ideal.Quotient.mk (Ideal.span {p}) h) := by
  have hq : Not ((Ideal.absNorm (Ideal.span {p}) : Complex) = 0) := by
    exact_mod_cast Ideal.absNorm_eq_zero_iff.not.mpr
      (Ideal.span_singleton_eq_bot.not.mpr hp)
  unfold fourthCarrierLocalFourier
  rw [if_neg (by omega : Not (e + 3 * l + k = 0)),
    liftedFourthPrimeFourier_lift,
    show e + 3 * l + k - 1 + 1 = e + 3 * l + k by omega]
  field_simp

theorem fourthCarrier_valuation (p : O) (hp : Prime p)
    [(Ideal.span {p} : Ideal O).IsMaximal]
    (chi : MulChar (Res p) Complex) (e l k j : Nat) (h : O)
    (hh : Not (Dvd.dvd p h)) :
    fourthCarrierLocalFourier p hp.ne_zero chi e l k (p ^ j * h) =
      if e + 3 * l + k = 0 then 1 else
      if e + 3 * l + k <= j then
        fourthPrimeFourier chi (quotientTrace p hp.ne_zero) e l k 0 else
      if e + 3 * l + k = j + 1 then
        fourthPrimeFourier chi (quotientTrace p hp.ne_zero) e l k
          (Ideal.Quotient.mk (Ideal.span {p}) h)
      else 0 := by
  by_cases hz : e + 3 * l + k = 0
  case pos =>
    simp only [fourthCarrierLocalFourier, hz, ite_true]
  case neg =>
    rw [if_neg hz]
    have hpos : 0 < e + 3 * l + k := by omega
    by_cases hs : e + 3 * l + k <= j
    case pos =>
      rw [if_pos hs]
      let n := e + 3 * l + k - 1
      have hnj : n <= j := by dsimp only [n]; omega
      have hpow : p ^ j * h = p ^ n * (p ^ (j - n) * h) := by
        rw [<-mul_assoc, <-pow_add, Nat.add_sub_of_le hnj]
      rw [hpow, fourthCarrierLocalFourier_lift p hp.ne_zero chi e l k hpos]
      have hd : Dvd.dvd p (p ^ (j - n) * h) :=
        (dvd_pow_self p (by dsimp only [n]; omega)).mul_right h
      have hm : Ideal.Quotient.mk (Ideal.span {p}) (p ^ (j - n) * h) = 0 :=
        Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton.mpr hd)
      rw [hm]
    case neg =>
      rw [if_neg hs]
      by_cases hb : e + 3 * l + k = j + 1
      case pos =>
        rw [if_pos hb]
        have he := fourthCarrierLocalFourier_lift p hp.ne_zero chi e l k hpos h
        simpa only [show e + 3 * l + k - 1 = j by omega] using he
      case neg =>
        rw [if_neg hb]
        have hn : j + 1 <= e + 3 * l + k - 1 := by omega
        have hoff : Not (Dvd.dvd (p ^ (e + 3 * l + k - 1)) (p ^ j * h)) := by
          intro hd
          have ht := (pow_dvd_pow p hn).trans hd
          rw [pow_succ] at ht
          exact hh ((mul_dvd_mul_iff_left (pow_ne_zero j hp.ne_zero)).mp ht)
        unfold fourthCarrierLocalFourier
        rw [if_neg hz, liftedFourthPrimeFourier_off_support p hp.ne_zero chi _ e l k _ hoff,
          zero_div]

end OAI.SevenEighths.ProbePowerGauss


/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/

import PrimeFactorOscillations.Assembly.DetectorPackets.PowerSampleZeroMode

/-!
# PowerSampleZeroModeActual

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
open ActualEisensteinCubic ConcretePrimeRowBridge ConcreteTraceCRT CubicEisenstein
open ProbeGauss ProbePrimePower ProbeEuler
local notation "O" => ActualEisensteinCubic.O
local notation "Res" p => HasQuotient.Quotient O (Ideal.span {p})

def actualFourthZeroCubeBlock (p : O) (hp : Prime p)
    [(Ideal.span {p} : Ideal O).IsMaximal]
    (hg : Not (Membership.mem (Ideal.span {p}) goodLambda))
    (eta a X W : Complex) (l : Nat) : Complex :=
  letI : Field (Res p) := Ideal.Quotient.field _
  letI : Fintype (Res p) := Fintype.ofFinite _
  let chi := CompletedGauss.actualSextic (Ideal.span {p}) hg
  fourthZeroCubeBlock chi (quotientTrace p hp.ne_zero) eta a
    (primeGauss p hp.ne_zero chi 1) (star (localGamma p hp.ne_zero hg 3))
    (chi (-1)) X W l

theorem actual_fourthZeroCube_hasSum (p : O) (hp : Prime p)
    [(Ideal.span {p} : Ideal O).IsMaximal]
    (hg : Not (Membership.mem (Ideal.span {p}) goodLambda))
    (hc : Not (ringChar (Res p) = 2)) (eta a X W : Complex)
    (hv : norm ((a * X ^ 3 / (Ideal.absNorm (Ideal.span {p}) : Complex)) ^ 2) < 1) :
    let q : Complex := Ideal.absNorm (Ideal.span {p})
    let v : Complex := a * X ^ 3 / q
    HasSum (actualFourthZeroCubeBlock p hp hg eta a X W)
      (1 / q + (1 - 1 / q) * (1 - eta * X * W) *
        (1 + star (localGamma p hp.ne_zero hg 3) * v) / (1 - v ^ 2)) := by
  letI : Field (Res p) := Ideal.Quotient.field _
  letI : Fintype (Res p) := Fintype.ofFinite _
  let chi := CompletedGauss.actualSextic (Ideal.span {p}) hg
  let psi := quotientTrace p hp.ne_zero
  let G1 := primeGauss p hp.ne_zero chi 1
  let C := star (localGamma p hp.ne_zero hg 3)
  let omega := chi (-1)
  have h6 : chi ^ 6 = 1 := actualSextic_six _ hg hc
  have h2 : Not (chi ^ 2 = 1) := by
    intro he
    have hd := (actualSextic_pow_eq_one_iff _ hg hc 2).mp he
    omega
  have ho : omega ^ 2 = 1 := actualSextic_neg_one_sq _ hg
  have hnOmega : norm omega = 1 := by
    have he := congrArg norm ho
    simp only [norm_pow, norm_one] at he
    nlinarith [norm_nonneg omega]
  have hiOmega : omega ^ (-1 : Int) = omega := by
    rw [zpow_neg_one]
    apply inv_eq_of_mul_eq_one_left
    simpa only [pow_two] using ho
  have hsOmega : star omega = omega := by
    calc
      _ = omega ^ (-1 : Int) := by
        simpa only [zpow_neg_one, starRingEnd_apply] using (Complex.inv_eq_conj hnOmega).symm
      _ = omega := hiOmega
  have hthree : localGamma p hp.ne_zero hg 3 ^ 2 = omega := by
    have he : localGamma p hp.ne_zero hg 3 * localGamma p hp.ne_zero hg 3 = omega ^ 3 := by
      simpa only [show 6 - 3 = 3 from rfl] using
        (localGamma_inverse_pair p hp.ne_zero hg hc 3 (by decide) (by decide))
    calc
      _ = omega ^ 3 := by simpa only [pow_two] using he
      _ = omega ^ 2 * omega := pow_succ omega 2
      _ = omega := by rw [ho, one_mul]
  have hC : C ^ 2 = omega := by
    have he := congrArg star hthree
    simpa only [star_pow, hsOmega] using he
  have hnGamma : Not (localGamma p hp.ne_zero hg 1 = 0) := by
    intro he
    have hn := localGamma_norm_one p hp.ne_zero hg hc 1 (by decide) (by decide)
    rw [he, norm_zero] at hn
    norm_num at hn
  have hqpos : 0 < (Ideal.absNorm (Ideal.span {p}) : Real) := by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr
      (Ideal.span_singleton_eq_bot.not.mpr hp.ne_zero))
  have hroot : Not ((Real.sqrt (Ideal.absNorm (Ideal.span {p}) : Real) : Complex) = 0) := by
    exact_mod_cast (Real.sqrt_pos.mpr hqpos).ne'
  have hG1 : Not (G1 = 0) := by
    change Not (primeGauss p hp.ne_zero chi 1 = 0)
    rw [firstGauss_eq_gamma_sqrt p hp hg]
    exact mul_ne_zero hnGamma hroot
  have hraw : gaussSum chi psi = G1 := by
    simp only [G1, psi, primeGauss, tsum_fintype, map_one, one_mul, gaussSum]
  have hminus : frequencyGauss chi psi (-1) = omega * G1 := by
    rw [frequencyGauss_nonzero chi psi (neg_ne_zero.mpr one_ne_zero), hraw]
    simp only [MulChar.inv_apply', inv_neg_one, omega]
  have hcard : Fintype.card (Res p) = Ideal.absNorm (Ideal.span {p}) := by
    rw [<-Nat.card_eq_fintype_card]
    rfl
  have hcardpos : 1 <= Fintype.card (Res p) :=
    Nat.one_le_iff_ne_zero.mpr Fintype.card_ne_zero
  have hcardne : Not ((Fintype.card (Res p) : Complex) = 0) := by
    exact_mod_cast Fintype.card_ne_zero
  have hunit :
      (Fintype.card (Units (Res p)) : Complex) / (Fintype.card (Res p) : Complex) =
        1 - 1 / (Fintype.card (Res p) : Complex) := by
    rw [Fintype.card_units, Nat.cast_sub hcardpos, Nat.cast_one]
    field_simp
  have hvF : norm ((a * X ^ 3 / (Fintype.card (Res p) : Complex)) ^ 2) < 1 := by
    simpa only [hcard] using hv
  have he := fourthZeroCube_hasSum chi h6 h2 psi eta a G1 C omega X W
    hG1 hC ho hminus hvF
  change HasSum (fourthZeroCubeBlock chi psi eta a G1 C omega X W) _
  convert he using 1
  rw [hunit, hcard]
  ring

end OAI.SevenEighths.ProbePowerGauss

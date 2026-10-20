/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/

import PrimeFactorOscillations.Proof.DetectorPackets.PowerSampleGauss
import PrimeFactorOscillations.Proof.DetectorPackets.PowerSampleNormalization

/-!
# PowerSampleJointFourier

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

theorem primeGauss_over_sqrt (p : O) (hp : Not (p = 0))
    [(Ideal.span {p} : Ideal O).IsMaximal]
    (hg : Not (Membership.mem (Ideal.span {p}) goodLambda)) (j : Nat) :
    primeGauss p hp (CompletedGauss.actualSextic (Ideal.span {p}) hg ^ j) 1 /
      (Real.sqrt (Ideal.absNorm (Ideal.span {p}) : Real) : Complex) =
        localGamma p hp hg j := by
  let : Field (Res p) := Ideal.Quotient.field _
  let : Fintype (Res p) := Fintype.ofFinite _
  unfold localGamma
  rw [ProbePhase.normalizedTraceGauss_eq_normalizedGauss]
  simp only [normalizedGauss, primeGauss, tsum_fintype, map_one, one_mul,
    gaussSum, <-Nat.card_eq_fintype_card]
  rfl

theorem source_cubic_fourier_product (p : O) (hp : Not (p = 0))
    [(Ideal.span {p} : Ideal O).IsMaximal]
    (hg : Not (Membership.mem (Ideal.span {p}) goodLambda))
    (hc : Not (ringChar (Res p) = 2))
    (hprimary : Dvd.dvd (goodLambda ^ 2) (p - 1)) (h : O) :
    primeGauss p hp (CompletedGauss.actualSextic (Ideal.span {p}) hg) (-1) *
      primeGauss p hp (CompletedGauss.actualSextic (Ideal.span {p}) hg ^ 2) h /
        (Ideal.absNorm (Ideal.span {p}) : Complex) =
      -(CompletedGauss.actualSextic (Ideal.span {p}) hg (-1)) *
        FiniteGaussPhase.angularFactor p * MixedGaussConversion.localG p hp hg *
        (CompletedGauss.actualSextic (Ideal.span {p}) hg ^ 4)
          (Ideal.Quotient.mk (Ideal.span {p}) h) := by
  let : Field (Res p) := Ideal.Quotient.field _
  let : Fintype (Res p) := Fintype.ofFinite _
  let chi := CompletedGauss.actualSextic (Ideal.span {p}) hg
  have hsix : chi ^ 6 = 1 := actualSextic_six _ hg hc
  have htwo : Not (chi ^ 2 = 1) := by
    intro he
    have hd := (actualSextic_pow_eq_one_iff _ hg hc 2).mp he
    omega
  have hinv : (chi ^ 2) ^ (-1 : Int) = chi ^ 4 := by
    rw [zpow_neg_one]
    apply inv_eq_of_mul_eq_one_right
    rw [<-pow_add]
    exact hsix
  have hfreq (a : O) :
      primeGauss p hp (chi ^ 2) a =
        (chi ^ 4) (Ideal.Quotient.mk (Ideal.span {p}) a) *
          primeGauss p hp (chi ^ 2) 1 := by
    have he := frequencyGauss_nonprincipal (chi ^ 2) (quotientTrace p hp)
      htwo (Ideal.Quotient.mk (Ideal.span {p}) a)
    simp only [frequencyGauss, gaussSum, map_one, one_mul, <-zpow_neg_one, hinv] at he
    simpa only [primeGauss, tsum_fintype, map_one, one_mul] using he
  have hminus :
      primeGauss p hp chi (-1) = chi (-1) * primeGauss p hp chi 1 := by
    have he := frequencyGauss_nonzero chi (quotientTrace p hp) (neg_ne_zero.mpr one_ne_zero)
    simp only [frequencyGauss, gaussSum, MulChar.inv_apply', inv_neg_one] at he
    simpa only [primeGauss, tsum_fintype, map_neg, map_one, one_mul] using he
  have hQ : 0 <= (Ideal.absNorm (Ideal.span {p}) : Real) := Nat.cast_nonneg _
  have hroot : (Real.sqrt (Ideal.absNorm (Ideal.span {p}) : Real) : Complex) ^ 2 =
      (Ideal.absNorm (Ideal.span {p}) : Complex) := by
    exact_mod_cast Real.sq_sqrt hQ
  have hg1 : primeGauss p hp chi 1 /
      (Real.sqrt (Ideal.absNorm (Ideal.span {p}) : Real) : Complex) =
        localGamma p hp hg 1 := by
    simpa only [pow_one] using primeGauss_over_sqrt p hp hg 1
  have hg2 := primeGauss_over_sqrt p hp hg 2
  change primeGauss p hp chi (-1) * primeGauss p hp (chi ^ 2) h /
    (Ideal.absNorm (Ideal.span {p}) : Complex) = _
  rw [hminus, hfreq]
  calc
    _ = chi (-1) * (chi ^ 4) (Ideal.Quotient.mk (Ideal.span {p}) h) *
        ((primeGauss p hp chi 1 /
          (Real.sqrt (Ideal.absNorm (Ideal.span {p}) : Real) : Complex)) *
         (primeGauss p hp (chi ^ 2) 1 /
          (Real.sqrt (Ideal.absNorm (Ideal.span {p}) : Real) : Complex))) := by
      rw [div_mul_div_comm, <-pow_two, hroot]
      ring
    _ = _ := by
      rw [hg1, hg2, localGamma_one_two_signal p hp hg hc hprimary]
      ring

theorem inverse_cubic_fourier_product (p : O) (hp : Not (p = 0))
    [(Ideal.span {p} : Ideal O).IsMaximal]
    (hg : Not (Membership.mem (Ideal.span {p}) goodLambda))
    (hc : Not (ringChar (Res p) = 2)) (h : O) :
    localGamma p hp hg 2 *
      (primeGauss p hp (CompletedGauss.actualSextic (Ideal.span {p}) hg ^ 4) h /
        (Real.sqrt (Ideal.absNorm (Ideal.span {p}) : Real) : Complex)) =
      (CompletedGauss.actualSextic (Ideal.span {p}) hg ^ 2)
        (Ideal.Quotient.mk (Ideal.span {p}) h) := by
  let : Field (Res p) := Ideal.Quotient.field _
  let : Fintype (Res p) := Fintype.ofFinite _
  let chi := CompletedGauss.actualSextic (Ideal.span {p}) hg
  have hfour : Not (chi ^ 4 = 1) := by
    intro he
    have hd := (actualSextic_pow_eq_one_iff _ hg hc 4).mp he
    omega
  have hinv : (chi ^ 4) ^ (-1 : Int) = chi ^ 2 := by
    rw [zpow_neg_one]
    apply inv_eq_of_mul_eq_one_right
    rw [<-pow_add]
    exact actualSextic_six _ hg hc
  have hfreq : primeGauss p hp (chi ^ 4) h =
      (chi ^ 2) (Ideal.Quotient.mk (Ideal.span {p}) h) *
        primeGauss p hp (chi ^ 4) 1 := by
    have he := frequencyGauss_nonprincipal (chi ^ 4) (quotientTrace p hp)
      hfour (Ideal.Quotient.mk (Ideal.span {p}) h)
    simp only [frequencyGauss, gaussSum, map_one, one_mul, <-zpow_neg_one, hinv] at he
    simpa only [primeGauss, tsum_fintype, map_one, one_mul] using he
  change localGamma p hp hg 2 * (primeGauss p hp (chi ^ 4) h /
    (Real.sqrt (Ideal.absNorm (Ideal.span {p}) : Real) : Complex)) = _
  rw [hfreq]
  calc
    _ = (chi ^ 2) (Ideal.Quotient.mk (Ideal.span {p}) h) *
        (localGamma p hp hg 2 *
          (primeGauss p hp (chi ^ 4) 1 /
            (Real.sqrt (Ideal.absNorm (Ideal.span {p}) : Real) : Complex))) := by ring
    _ = _ := by
      rw [primeGauss_over_sqrt p hp hg 4, localGamma_two_four p hp hg hc, mul_one]

theorem actual_power_fourier (p : O) (hp : Not (p = 0))
    [(Ideal.span {p} : Ideal O).IsMaximal]
    (chi xi : MulChar (Res p) Complex) {d : Nat} (hd : 0 < d) (h : O) :
    (tsum fun r : Res p =>
      (xi r ^ d * primeGauss p hp chi (-(GaussianShiftedPartition.representative p r ^ d))) *
        quotientTrace p hp (Ideal.Quotient.mk (Ideal.span {p}) h * r)) =
      primeGauss p hp chi (-1) *
        primeGauss p hp ((xi * chi ^ (-1 : Int)) ^ d) h := by
  let : Field (Res p) := Ideal.Quotient.field _
  let : Fintype (Res p) := Fintype.ofFinite _
  have hf (rho : MulChar (Res p) Complex) (a : O) :
      primeGauss p hp rho a =
        frequencyGauss rho (quotientTrace p hp) (Ideal.Quotient.mk (Ideal.span {p}) a) := by
    rw [primeGauss, tsum_fintype]
    rfl
  simp_rw [hf]
  rw [tsum_fintype]
  simp only [map_neg, map_pow, map_one, GaussianShiftedPartition.representative_spec]
  exact power_fourier chi xi (quotientTrace p hp) (quotientTrace p hp) hd _

theorem source_unit_fourth_fourier (p : O) (hp : Not (p = 0))
    [(Ideal.span {p} : Ideal O).IsMaximal]
    (hg : Not (Membership.mem (Ideal.span {p}) goodLambda))
    (hc : Not (ringChar (Res p) = 2))
    (hprimary : Dvd.dvd (goodLambda ^ 2) (p - 1)) (h : O) :
    (tsum fun r : Res p =>
      (((1 : MulChar (Res p) Complex) r) ^ 4 *
        primeGauss p hp (CompletedGauss.actualSextic (Ideal.span {p}) hg)
          (-(GaussianShiftedPartition.representative p r ^ 4))) *
        quotientTrace p hp (Ideal.Quotient.mk (Ideal.span {p}) h * r)) /
          (Ideal.absNorm (Ideal.span {p}) : Complex) =
      -(CompletedGauss.actualSextic (Ideal.span {p}) hg (-1)) *
        FiniteGaussPhase.angularFactor p * MixedGaussConversion.localG p hp hg *
        (CompletedGauss.actualSextic (Ideal.span {p}) hg ^ 4)
          (Ideal.Quotient.mk (Ideal.span {p}) h) := by
  let chi := CompletedGauss.actualSextic (Ideal.span {p}) hg
  have hi : (1 * chi ^ (-1 : Int)) ^ 4 = chi ^ 2 := by
    rw [one_mul, zpow_neg_one, inv_pow]
    apply inv_eq_of_mul_eq_one_right
    rw [<-pow_add]
    exact actualSextic_six _ hg hc
  rw [actual_power_fourier p hp chi 1 (by decide : 0 < 4) h, hi]
  exact source_cubic_fourier_product p hp hg hc hprimary h

theorem shared_fourth_fourier (p : O) (hp : Prime p)
    [(Ideal.span {p} : Ideal O).IsMaximal]
    (hg : Not (Membership.mem (Ideal.span {p}) goodLambda))
    (hc : Not (ringChar (Res p) = 2))
    (hprimary : Dvd.dvd (goodLambda ^ 2) (p - 1))
    (hs : CanonicalQuadraticSieve.Supported (Ideal.span {p})) (h : O) :
    (localGamma p hp.ne_zero hg 2 * star (FiniteGaussPhase.angularFactor p) *
      star (ProbePhase.G p) /
      (Real.sqrt (Ideal.absNorm (Ideal.span {p}) : Real) : Complex)) *
      CompletedGauss.actualSextic (Ideal.span {p}) hg (-1) *
      (tsum fun r : Res p =>
        ((CompletedGauss.actualSextic (Ideal.span {p}) hg r) ^ 4 *
          primeGauss p hp.ne_zero (CompletedGauss.actualSextic (Ideal.span {p}) hg)
            (-(GaussianShiftedPartition.representative p r ^ 4))) *
          quotientTrace p hp.ne_zero (Ideal.Quotient.mk (Ideal.span {p}) h * r)) =
      -primeGauss p hp.ne_zero 1 h := by
  let : Field (Res p) := Ideal.Quotient.field _
  let : Fintype (Res p) := Fintype.ofFinite _
  let chi := CompletedGauss.actualSextic (Ideal.span {p}) hg
  have hm : primeGauss p hp.ne_zero chi (-1) =
      chi (-1) * primeGauss p hp.ne_zero chi 1 := by
    have he := frequencyGauss_nonzero chi (quotientTrace p hp.ne_zero)
      (neg_ne_zero.mpr one_ne_zero)
    simp only [frequencyGauss, gaussSum, MulChar.inv_apply', inv_neg_one] at he
    simpa only [primeGauss, tsum_fintype, map_neg, map_one, one_mul] using he
  have hi : (chi * chi ^ (-1 : Int)) ^ 4 = 1 := by
    rw [zpow_neg_one, mul_inv_cancel, one_pow]
  rw [actual_power_fourier p hp.ne_zero chi chi (by decide : 0 < 4) h, hi, hm]
  have hsig := corrected_diagonal_raw p hp hg hc hprimary hs
  have homega : chi (-1) ^ 2 = 1 := actualSextic_neg_one_sq _ hg
  calc
    _ = chi (-1) ^ 2 *
        (((localGamma p hp.ne_zero hg 2 * star (FiniteGaussPhase.angularFactor p) *
          star (ProbePhase.G p) /
          (Real.sqrt (Ideal.absNorm (Ideal.span {p}) : Real) : Complex)) *
            primeGauss p hp.ne_zero chi 1) * primeGauss p hp.ne_zero 1 h) := by ring
    _ = _ := by rw [homega, hsig]; ring

end OAI.SevenEighths.ProbePowerGauss

/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Assembly.FiniteFieldNativeAgreementSpectrum

/-!
# Full principal centering for native agreement rows

Every integer numerator is fixed before the independent field scale.
The principal row retains its complete nonunit mask; a square multiplier
is removed only after all its prime divisors have left the observed band.
-/

set_option autoImplicit false
set_option Elab.async false

noncomputable section
namespace PrimeFactorOscillations.FiniteFieldIntegerSignature
open Filter IntegerQuadraticCharacter
open FiniteFieldIntegerWindowTransfer

def numeratorPrincipalIndicator (D : Int) : Real := by
  classical
  exact if hD : D = 0 then 0 else if numeratorCharacter D hD = 1 then 1 else 0

theorem principal_prime_kernel_eventually (D : Int) (hD : Not (D = 0))
    (hchi : numeratorCharacter D hD = 1) :
    Filter.Eventually (fun p : Nat => Nat.Prime p ->
      (numeratorKernel D p).re = 1) atTop := by
  filter_upwards [eventually_gt_atTop (4 * D.natAbs)] with p hp hprime
  have hlevel : 0 < 4 * D.natAbs := by
    have hd := Int.natAbs_pos.mpr hD
    omega
  have hcop : Nat.Coprime p (4 * D.natAbs) :=
    Nat.coprime_of_lt_prime (ne_of_gt hlevel) hp hprime
  have hunit : IsUnit (p : ZMod (4 * D.natAbs)) :=
    (ZMod.isUnit_iff_coprime p (4 * D.natAbs)).mpr hcop
  have hv : numeratorKernel D p = (1 : Complex) := by
    rw [<- numerator_character_natCast D hD p, hchi, MulChar.one_apply hunit]
  simpa only [Complex.one_re] using congrArg Complex.re hv

theorem principal_prime_correlation_eventually_eq_mass (D : Int)
    (hD : Not (D = 0)) (hchi : numeratorCharacter D hD = 1) :
    Filter.Eventually (fun U : Nat =>
      primeCorrelation D (preciseCore U + 1) (preciseCore U * preciseCore U + 1) =
        reciprocalBand (preciseCore U + 1) (preciseCore U * preciseCore U + 1)) atTop := by
  choose N hN using eventually_atTop.mp (principal_prime_kernel_eventually D hD hchi)
  filter_upwards [precise_core_tendsto_atTop.eventually_ge_atTop N] with U hU
  unfold primeCorrelation reciprocalBand
  apply Finset.sum_congr rfl
  intro p hp
  have hdata := Finset.mem_filter.mp hp
  have hband := Finset.mem_Ico.mp hdata.1
  rw [hN p (by omega) hdata.2, mul_one]

theorem prime_correlation_principal_centered_tendsto_zero (D : Int)
    (hD : Not (D = 0)) :
    Tendsto (fun U : Nat =>
      primeCorrelation D (preciseCore U + 1) (preciseCore U * preciseCore U + 1) -
        numeratorPrincipalIndicator D *
          reciprocalBand (preciseCore U + 1) (preciseCore U * preciseCore U + 1))
      atTop (nhds 0) := by
  classical
  by_cases hchi : numeratorCharacter D hD = 1
  . simp only [numeratorPrincipalIndicator, dite_eq_right hD, ite_eq_left hchi, one_mul]
    have heq := principal_prime_correlation_eventually_eq_mass D hD hchi
    apply Metric.tendsto_nhds.mpr
    intro eps heps
    filter_upwards [heq] with U hU
    simpa only [hU, sub_self, dist_self] using heps
  . simpa only [numeratorPrincipalIndicator, dite_eq_right hD, ite_eq_right hchi,
      zero_mul, sub_zero] using
      fixed_nonprincipal_prime_correlation_tendsto_zero D hD hchi

theorem negative_prime_correlation_tendsto_zero (D : Int) (hD : D < 0) :
    Tendsto (fun U : Nat =>
      primeCorrelation D (preciseCore U + 1) (preciseCore U * preciseCore U + 1))
      atTop (nhds 0) := by
  cases D with
  | ofNat z =>
    have hz : (0 : Int) <= (z : Int) := by exact_mod_cast (Nat.zero_le z)
    exact False.elim ((not_lt_of_ge hz) hD)
  | negSucc z =>
    have he : Int.negSucc z = -((z + 1 : Nat) : Int) := by omega
    rw [he]
    have hz : Not (-((z + 1 : Nat) : Int) = 0) := by omega
    exact fixed_nonprincipal_prime_correlation_tendsto_zero _ hz
      (negative_numerator_character_ne_one (z + 1) (by omega) hz)

theorem prime_correlation_square_factor_eventually (a : Nat) (ha : 0 < a)
    (D : Int) :
    Filter.Eventually (fun U : Nat =>
      primeCorrelation ((a : Int) ^ 2 * D)
          (preciseCore U + 1) (preciseCore U * preciseCore U + 1) =
        primeCorrelation D (preciseCore U + 1) (preciseCore U * preciseCore U + 1))
      atTop := by
  filter_upwards [precise_core_tendsto_atTop.eventually_ge_atTop (max a 3)]
    with U hU
  unfold primeCorrelation
  apply Finset.sum_congr rfl
  intro p hp
  have hdata := Finset.mem_filter.mp hp
  have hband := Finset.mem_Ico.mp hdata.1
  have : Fact (Nat.Prime p) := Fact.mk hdata.2
  have hap : a < p := by omega
  have hna : Not ((a : ZMod p) = 0) := by
    intro hz
    exact (Nat.not_dvd_of_pos_of_lt ha hap) ((ZMod.natCast_eq_zero_iff a p).mp hz)
  have hza : Not (((a : Int) : ZMod p) = 0) := by
    simpa only [Int.cast_natCast] using hna
  have hs : (numeratorKernel (a : Int) p).re *
      (numeratorKernel (a : Int) p).re = 1 := by
    simpa only [pow_two] using real_kernel_square_of_nonzero (a : Int) p (by omega) hza
  have hka : (numeratorKernel ((a : Int) ^ 2) p).re = 1 := by
    rw [pow_two, real_kernel_mul]
    exact hs
  rw [real_kernel_mul, hka, one_mul]

end PrimeFactorOscillations.FiniteFieldIntegerSignature

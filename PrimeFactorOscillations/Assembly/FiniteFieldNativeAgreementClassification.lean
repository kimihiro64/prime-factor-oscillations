/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Assembly.FiniteFieldNativePrincipalMean

/-!
# The complete agreement spectrum of actual prime pairs

Both integer pairs are fixed before the independent field scale.
All seven signed rows are retained, including both principal cross rows.
-/

set_option autoImplicit false
set_option Elab.async false

noncomputable section
namespace PrimeFactorOscillations.FiniteFieldIntegerSignature
open Filter IntegerQuadraticCharacter
open FiniteFieldIntegerWindowTransfer

def nativeAgreementRate (n h m k : Nat) : Real :=
  (3 + numeratorPrincipalIndicator ((h : Int) * (k : Int) * (n : Int) * (m : Int)) +
    numeratorPrincipalIndicator
      ((h : Int) * (k : Int) * ((n + h : Nat) : Int) * ((m + k : Nat) : Int))) / 8

theorem native_product_prime_correlation_tendsto_zero (n h m k : Nat)
    (hn : Nat.Prime n) (hnh : Nat.Prime (n + h))
    (hm : Nat.Prime m) (hmk : Nat.Prime (m + k))
    (hh : 0 < h) (hk : 0 < k) (hneq : Not (And (n = m) (h = k))) :
    Tendsto (fun U : Nat =>
      primeCorrelation
        (-((h : Int) * (n : Int)) * ((h : Int) * ((n + h : Nat) : Int)) *
          (-((k : Int) * (m : Int))) * ((k : Int) * ((m + k : Nat) : Int)))
        (preciseCore U + 1) (preciseCore U * preciseCore U + 1))
      atTop (nhds 0) := by
  let A : Int := -((h : Int) * (n : Int))
  let B : Int := (h : Int) * ((n + h : Nat) : Int)
  let C : Int := -((k : Int) * (m : Int))
  let D : Int := (k : Int) * ((m + k : Nat) : Int)
  let E : Int := ((n * (n + h) * m * (m + k) : Nat) : Int)
  change Tendsto (fun U : Nat => primeCorrelation (A * B * C * D)
    (preciseCore U + 1) (preciseCore U * preciseCore U + 1)) atTop (nhds 0)
  choose a P ha hP hP2 hcop hprod using
    distinct_prime_pairs_have_odd_carrier n h m k hn hnh hm hmk hh hk hneq
  have hn0 := hn.pos
  have hm0 := hm.pos
  have hEpos : 0 < E := by dsimp [E]; positivity
  have hE : Not (E = 0) := ne_of_gt hEpos
  have hEq : E = (a : Int) * (P : Int) := by
    dsimp only [E]
    exact_mod_cast hprod
  have hchi := numerator_character_ne_one_of_coprime_prime_factor
    a P ha hP hP2 hcop E hE (Or.inl hEq)
  have hbase := fixed_nonprincipal_prime_correlation_tendsto_zero E hE hchi
  have hsquare := prime_correlation_square_factor_eventually (h * k) (Nat.mul_pos hh hk) E
  have hnum : A * B * C * D = ((h * k : Nat) : Int) ^ 2 * E := by
    dsimp only [A, B, C, D, E]
    push_cast
    ring
  apply Metric.tendsto_nhds.mpr
  intro eps heps
  have he := Metric.tendsto_nhds.mp hbase eps heps
  filter_upwards [he, hsquare] with U hsmall hs
  rw [hnum, hs]
  exact hsmall

theorem native_agreement_centered_by_cross_characters (n h m k : Nat)
    (hn : Nat.Prime n) (hnh : Nat.Prime (n + h))
    (hm : Nat.Prime m) (hmk : Nat.Prime (m + k))
    (hh : 0 < h) (hk : 0 < k) (hneq : Not (And (n = m) (h = k))) :
    Tendsto (fun U : Nat =>
      nativeAgreementMass n h m k (preciseCore U + 1)
          (preciseCore U * preciseCore U + 1) -
        nativeAgreementRate n h m k *
          reciprocalBand (preciseCore U + 1) (preciseCore U * preciseCore U + 1))
      atTop (nhds 0) := by
  let A : Int := -((h : Int) * (n : Int))
  let B : Int := (h : Int) * ((n + h : Nat) : Int)
  let C : Int := -((k : Int) * (m : Int))
  let D : Int := (k : Int) * ((m + k : Nat) : Int)
  let f : Int -> Nat -> Real := fun E U =>
    primeCorrelation E (preciseCore U + 1) (preciseCore U * preciseCore U + 1)
  let M : Nat -> Real := fun U =>
    reciprocalBand (preciseCore U + 1) (preciseCore U * preciseCore U + 1)
  let e1 : Real := numeratorPrincipalIndicator (A * C)
  let e2 : Real := numeratorPrincipalIndicator (B * D)
  have hn0 := hn.pos
  have hm0 := hm.pos
  have hA : A < 0 := by dsimp [A]; apply neg_neg_of_pos; positivity
  have hB : 0 < B := by dsimp [B]; positivity
  have hC : C < 0 := by dsimp [C]; apply neg_neg_of_pos; positivity
  have hD : 0 < D := by dsimp [D]; positivity
  have hAC : Not (A * C = 0) := mul_ne_zero (ne_of_lt hA) (ne_of_lt hC)
  have hBD : Not (B * D = 0) := mul_ne_zero (ne_of_gt hB) (ne_of_gt hD)
  have h1 : Tendsto (f (A * B)) atTop (nhds 0) :=
    negative_prime_correlation_tendsto_zero _ (mul_neg_of_neg_of_pos hA hB)
  have h2 : Tendsto (f (C * D)) atTop (nhds 0) :=
    negative_prime_correlation_tendsto_zero _ (mul_neg_of_neg_of_pos hC hD)
  have h3 : Tendsto (fun U => f (A * C) U - e1 * M U) atTop (nhds 0) :=
    prime_correlation_principal_centered_tendsto_zero _ hAC
  have h4 : Tendsto (f (A * D)) atTop (nhds 0) :=
    negative_prime_correlation_tendsto_zero _ (mul_neg_of_neg_of_pos hA hD)
  have h5 : Tendsto (f (B * C)) atTop (nhds 0) :=
    negative_prime_correlation_tendsto_zero _ (mul_neg_of_pos_of_neg hB hC)
  have h6 : Tendsto (fun U => f (B * D) U - e2 * M U) atTop (nhds 0) :=
    prime_correlation_principal_centered_tendsto_zero _ hBD
  have h7 : Tendsto (f (A * B * C * D)) atTop (nhds 0) :=
    native_product_prime_correlation_tendsto_zero n h m k hn hnh hm hmk hh hk hneq
  have hfull : Tendsto (fun U : Nat => (3 : Real) * f (A * B * C * D) U)
      atTop (nhds (3 * (0 : Real))) := tendsto_const_nhds.mul h7
  have htotal := ((((((h1.add h2).neg).add h3).add h4).add h5).add h6).add hfull
  have hlim : Tendsto (fun U : Nat =>
      (-(f (A * B) U + f (C * D) U) + (f (A * C) U - e1 * M U) +
        f (A * D) U + f (B * C) U + (f (B * D) U - e2 * M U) +
        3 * f (A * B * C * D) U) / 8) atTop (nhds 0) := by
    simpa only [neg_zero, zero_add, add_zero, mul_zero, zero_div] using
      htotal.div_const (8 : Real)
  have hACeq : A * C = (h : Int) * (k : Int) * (n : Int) * (m : Int) := by
    dsimp only [A, C]
    ring
  have hBDeq : B * D =
      (h : Int) * (k : Int) * ((n + h : Nat) : Int) * ((m + k : Nat) : Int) := by
    dsimp only [B, D]
    ring
  have hRate : nativeAgreementRate n h m k = (3 + e1 + e2) / 8 := by
    dsimp only [nativeAgreementRate, e1, e2]
    rw [hACeq, hBDeq]
  apply Metric.tendsto_nhds.mpr
  intro eps heps
  have he := Metric.tendsto_nhds.mp hlim eps heps
  have hcore := precise_core_tendsto_atTop.eventually_ge_atTop
    (max (n + h) (m + k) + 5)
  filter_upwards [he, hcore] with U hsmall hU
  have hid := native_agreement_mass_eq_seven_correlations n h m k
    (preciseCore U + 1) (preciseCore U * preciseCore U + 1)
    hn.pos hh hm.pos hk (by omega) (by omega) (by omega)
  change nativeAgreementMass n h m k (preciseCore U + 1)
      (preciseCore U * preciseCore U + 1) =
    3 * M U / 8 + (-(f (A * B) U + f (C * D) U) + f (A * C) U +
      f (A * D) U + f (B * C) U + f (B * D) U +
      3 * f (A * B * C * D) U) / 8 at hid
  have hdiff : nativeAgreementMass n h m k (preciseCore U + 1)
      (preciseCore U * preciseCore U + 1) - nativeAgreementRate n h m k * M U =
    (-(f (A * B) U + f (C * D) U) + (f (A * C) U - e1 * M U) +
      f (A * D) U + f (B * C) U + (f (B * D) U - e2 * M U) +
      3 * f (A * B * C * D) U) / 8 := by
    rw [hid, hRate]
    ring
  rw [hdiff]
  exact hsmall

theorem native_agreement_rate_dichotomy (n h m k : Nat)
    (hn : Nat.Prime n) (hnh : Nat.Prime (n + h))
    (hm : Nat.Prime m) (hmk : Nat.Prime (m + k))
    (hh : 0 < h) (hk : 0 < k) (hneq : Not (And (n = m) (h = k))) :
    Or (nativeAgreementRate n h m k = 3 / 8)
      (nativeAgreementRate n h m k = 1 / 2) := by
  classical
  have hvalue (E : Int) : Or (numeratorPrincipalIndicator E = 0)
      (numeratorPrincipalIndicator E = 1) := by
    by_cases hE : E = 0
    . exact Or.inl (by simp only [numeratorPrincipalIndicator, dite_eq_left hE])
    . by_cases hc : numeratorCharacter E hE = 1
      . exact Or.inr (by simp only [numeratorPrincipalIndicator, dite_eq_right hE,
          ite_eq_left hc])
      . exact Or.inl (by simp only [numeratorPrincipalIndicator, dite_eq_right hE,
          ite_eq_right hc])
  have hvalues : Or (nativeAgreementRate n h m k = 3 / 8)
      (Or (nativeAgreementRate n h m k = 1 / 2)
        (nativeAgreementRate n h m k = 5 / 8)) := by
    unfold nativeAgreementRate
    rcases hvalue ((h : Int) * (k : Int) * (n : Int) * (m : Int)) with h1 | h1 <;>
      rcases hvalue
        ((h : Int) * (k : Int) * ((n + h : Nat) : Int) * ((m + k : Nat) : Int))
        with h2 | h2 <;> rw [h1, h2] <;> norm_num
  rcases hvalues with hgood | hgood | hbad
  . exact Or.inl hgood
  . exact Or.inr hgood
  . exfalso
    let eps : Real := Real.log 2 / 100
    have heps : 0 < eps := by dsimp [eps]; positivity
    have hlim := native_agreement_centered_by_cross_characters
      n h m k hn hnh hm hmk hh hk hneq
    have hlo := hlim.eventually (Ioi_mem_nhds (show -eps < 0 by linarith only [heps]))
    choose B hB hupper using
      exists_eventual_native_agreement_upper n h m k hn hnh hm hmk hh hk hneq
    have herr := (relative_error_tendsto_zero B).eventually (Iio_mem_nhds heps)
    have hm := precise_core_tendsto_atTop.eventually eventually_reciprocal_square_band_positive
    choose U hU using (hlo.and (hupper.and (herr.and hm))).exists
    have hLower := hU.1
    have hUpper := hU.2.1
    have hError := hU.2.2.1
    have hMass := hU.2.2.2
    rw [hbad] at hLower
    dsimp only [eps] at hLower hError
    have hlog : 0 < Real.log 2 := by positivity
    linarith only [hLower, hUpper, hError, hMass, hlog]

theorem native_agreement_ratio_tendsto_rate (n h m k : Nat)
    (hn : Nat.Prime n) (hnh : Nat.Prime (n + h))
    (hm : Nat.Prime m) (hmk : Nat.Prime (m + k))
    (hh : 0 < h) (hk : 0 < k) (hneq : Not (And (n = m) (h = k))) :
    Tendsto (fun U : Nat =>
      nativeAgreementMass n h m k (preciseCore U + 1)
          (preciseCore U * preciseCore U + 1) /
        reciprocalBand (preciseCore U + 1) (preciseCore U * preciseCore U + 1))
      atTop (nhds (nativeAgreementRate n h m k)) := by
  have hlim := native_agreement_centered_by_cross_characters
    n h m k hn hnh hm hmk hh hk hneq
  apply Metric.tendsto_nhds.mpr
  intro eps heps
  let eta : Real := eps * Real.log 2 / 4
  have heta : 0 < eta := by dsimp [eta]; positivity
  have he := Metric.tendsto_nhds.mp hlim eta heta
  have hm := precise_core_tendsto_atTop.eventually eventually_reciprocal_square_band_positive
  filter_upwards [he, hm] with U hsmall hMass
  let A : Real := nativeAgreementMass n h m k (preciseCore U + 1)
    (preciseCore U * preciseCore U + 1)
  let M : Real := reciprocalBand (preciseCore U + 1) (preciseCore U * preciseCore U + 1)
  have hM : 0 < M := (show 0 < Real.log 2 / 2 by positivity).trans_le hMass
  have hid : A / M - nativeAgreementRate n h m k =
      (A - nativeAgreementRate n h m k * M) / M := by
    field_simp [ne_of_gt hM]
  change dist (A / M) (nativeAgreementRate n h m k) < eps
  rw [Real.dist_eq, hid, abs_div, abs_of_pos hM]
  have hsmall' : abs (A - nativeAgreementRate n h m k * M) < eta := by
    simpa only [Real.dist_eq, sub_zero] using hsmall
  have hscale := mul_le_mul_of_nonneg_left hMass heps.le
  have hpos : 0 < eps * Real.log 2 := mul_pos heps (by positivity)
  dsimp only [eta] at hsmall'
  have hbound : abs (A - nativeAgreementRate n h m k * M) < eps * M := by
    linarith only [hsmall', hscale, hpos]
  have hdiv := div_lt_div_of_pos_right hbound hM
  have hcancel : eps * M / M = eps := by field_simp [ne_of_gt hM]
  rwa [hcancel] at hdiv

end PrimeFactorOscillations.FiniteFieldIntegerSignature

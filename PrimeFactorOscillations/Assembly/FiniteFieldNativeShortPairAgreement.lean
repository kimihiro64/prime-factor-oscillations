/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Assembly.FiniteFieldNativeAgreementSpectrum

/-!
# Exact three-eighths agreement for short prime pairs

Both pairs are fixed before the independent field scale grows. Every one
of the seven signed character rows is bounded with its full modulus.
-/

set_option autoImplicit false
set_option Elab.async false

noncomputable section
namespace PrimeFactorOscillations.FiniteFieldIntegerSignature
open Filter IntegerQuadraticCharacter
open FiniteFieldIntegerWindowTransfer

theorem native_agreement_remainder_tendsto_zero_of_short_gaps (n h m k : Nat)
    (hn : Nat.Prime n) (hnh : Nat.Prime (n + h))
    (hm : Nat.Prime m) (hmk : Nat.Prime (m + k))
    (hh : 0 < h) (hk : 0 < k) (hhn : h < n) (hkm : k < m)
    (hnm : Not (n = m)) (hup : Not (n + h = m + k)) :
    Tendsto (fun U : Nat => nativeAgreementRemainder n h m k
      (preciseCore U + 1) (preciseCore U * preciseCore U + 1)) atTop (nhds 0) := by
  let A : Int := -((h : Int) * (n : Int))
  let B : Int := (h : Int) * ((n + h : Nat) : Int)
  let C : Int := -((k : Int) * (m : Int))
  let D : Int := (k : Int) * ((m + k : Nat) : Int)
  let f : Int -> Nat -> Real := fun E U =>
    primeCorrelation E (preciseCore U + 1) (preciseCore U * preciseCore U + 1)
  change Tendsto (fun U : Nat =>
    (-(f (A * B) U + f (C * D) U) + f (A * C) U + f (A * D) U +
      f (B * C) U + f (B * D) U + 3 * f (A * B * C * D) U) / 8) atTop (nhds 0)
  have hn0 := hn.pos
  have hm0 := hm.pos
  have hn2 := hn.two_le
  have hm2 := hm.two_le
  have hnegative (E : Int) (hE : E < 0) :
      Tendsto (f E) atTop (nhds 0) := by
    cases E with
    | ofNat z =>
      have hz : (0 : Int) <= (z : Int) := by exact_mod_cast (Nat.zero_le z)
      exact False.elim ((not_lt_of_ge hz) hE)
    | negSucc z =>
      have he : Int.negSucc z = -((z + 1 : Nat) : Int) := by omega
      rw [he]
      have hz : Not (-((z + 1 : Nat) : Int) = 0) := by omega
      exact fixed_nonprincipal_prime_correlation_tendsto_zero _ hz
        (negative_numerator_character_ne_one (z + 1) (by omega) hz)
  have hcarrier (E : Int) (a P : Nat) (ha : 0 < a) (hP : Nat.Prime P)
      (hP2 : 2 < P) (hcop : Nat.Coprime P a)
      (he : E = (a : Int) * (P : Int)) :
      Tendsto (f E) atTop (nhds 0) := by
    have hE : Not (E = 0) := by
      rw [he]
      exact mul_ne_zero (by exact_mod_cast (ne_of_gt ha))
        (by exact_mod_cast (ne_of_gt hP.pos))
    have hchi := numerator_character_ne_one_of_coprime_prime_factor
      a P ha hP hP2 hcop E hE (Or.inl he)
    exact fixed_nonprincipal_prime_correlation_tendsto_zero E hE hchi
  have hAneg : A < 0 := by
    dsimp [A]
    apply neg_neg_of_pos
    positivity
  have hBpos : 0 < B := by dsimp [B]; positivity
  have hCneg : C < 0 := by
    dsimp [C]
    apply neg_neg_of_pos
    positivity
  have hDpos : 0 < D := by dsimp [D]; positivity
  have h1 := hnegative (A * B) (mul_neg_of_neg_of_pos hAneg hBpos)
  have h2 := hnegative (C * D) (mul_neg_of_neg_of_pos hCneg hDpos)
  have h4 := hnegative (A * D) (mul_neg_of_neg_of_pos hAneg hDpos)
  have h5 := hnegative (B * C) (mul_neg_of_pos_of_neg hBpos hCneg)
  have h3 : Tendsto (f (A * C)) atTop (nhds 0) := by
    by_cases hlt : n < m
    . refine hcarrier (A * C) (h * k * n) m (by positivity) hm (by omega) ?_ ?_
      . exact endpoint_coefficient_coprime h k m n hh hk hm hn
          (by omega) hkm (by omega)
      . dsimp [A, C]
        ring
    . have hlt' : m < n := by omega
      refine hcarrier (A * C) (h * k * m) n (by positivity) hn (by omega) ?_ ?_
      . exact endpoint_coefficient_coprime h k n m hh hk hn hm
          hhn (by omega) (by omega)
      . dsimp [A, C]
        ring
  have h6 : Tendsto (f (B * D)) atTop (nhds 0) := by
    by_cases hlt : n + h < m + k
    . refine hcarrier (B * D) (h * k * (n + h)) (m + k)
        (by positivity) hmk (by omega) ?_ ?_
      . exact endpoint_coefficient_coprime h k (m + k) (n + h)
          hh hk hmk hnh (by omega) (by omega) (by omega)
      . dsimp [B, D]
        ring
    . have hlt' : m + k < n + h := by omega
      refine hcarrier (B * D) (h * k * (m + k)) (n + h)
        (by positivity) hnh (by omega) ?_ ?_
      . exact endpoint_coefficient_coprime h k (n + h) (m + k)
          hh hk hnh hmk (by omega) (by omega) (by omega)
      . dsimp [B, D]
        ring
  have hcoproduct (P u v w : Nat) (hP : Nat.Prime P)
      (hu : 0 < u) (hv : 0 < v) (hw : 0 < w)
      (hhP : h < P) (hkP : k < P) (huP : u < P) (hvP : v < P) (hwP : w < P) :
      Nat.Coprime P (h * h * k * k * u * v * w) := by
    have hPh := Nat.coprime_of_lt_prime (ne_of_gt hh) hhP hP
    have hPk := Nat.coprime_of_lt_prime (ne_of_gt hk) hkP hP
    have hPu := Nat.coprime_of_lt_prime (ne_of_gt hu) huP hP
    have hPv := Nat.coprime_of_lt_prime (ne_of_gt hv) hvP hP
    have hPw := Nat.coprime_of_lt_prime (ne_of_gt hw) hwP hP
    simp only [Nat.coprime_mul_iff_right]
    exact And.intro (And.intro (And.intro (And.intro (And.intro (And.intro (hPh) (hPh)) (hPk)) (hPk)) (hPu)) (hPv)) (hPw)
  have h7 : Tendsto (f (A * B * C * D)) atTop (nhds 0) := by
    by_cases hlt : n + h < m + k
    . refine hcarrier (A * B * C * D) (h * h * k * k * n * (n + h) * m)
        (m + k) (by positivity) hmk (by omega) ?_ ?_
      . exact hcoproduct (m + k) n (n + h) m hmk
          hn0 (by omega) hm0 (by omega) (by omega) (by omega) hlt (by omega)
      . dsimp [A, B, C, D]
        ring
    . have hlt' : m + k < n + h := by omega
      refine hcarrier (A * B * C * D) (h * h * k * k * n * m * (m + k))
        (n + h) (by positivity) hnh (by omega) ?_ ?_
      . exact hcoproduct (n + h) n m (m + k) hnh
          hn0 hm0 (by omega) (by omega) (by omega) (by omega) (by omega) hlt'
      . dsimp [A, B, C, D]
        ring
  have hfull : Tendsto (fun U : Nat => (3 : Real) * f (A * B * C * D) U)
      atTop (nhds (3 * (0 : Real))) := tendsto_const_nhds.mul h7
  have htotal := ((((((h1.add h2).neg).add h3).add h4).add h5).add h6).add hfull
  simpa only [neg_zero, zero_add, add_zero, mul_zero, zero_div] using
    htotal.div_const (8 : Real)

theorem native_agreement_three_eighths_of_short_gaps (n h m k : Nat)
    (hn : Nat.Prime n) (hnh : Nat.Prime (n + h))
    (hm : Nat.Prime m) (hmk : Nat.Prime (m + k))
    (hh : 0 < h) (hk : 0 < k) (hhn : h < n) (hkm : k < m)
    (hnm : Not (n = m)) (hup : Not (n + h = m + k)) :
    Tendsto (fun U : Nat => nativeAgreementMass n h m k
      (preciseCore U + 1) (preciseCore U * preciseCore U + 1) -
        3 * reciprocalBand (preciseCore U + 1)
          (preciseCore U * preciseCore U + 1) / 8) atTop (nhds 0) := by
  have hr := native_agreement_remainder_tendsto_zero_of_short_gaps
    n h m k hn hnh hm hmk hh hk hhn hkm hnm hup
  apply Metric.tendsto_nhds.mpr
  intro eps heps
  have he := Metric.tendsto_nhds.mp hr eps heps
  have hcore := precise_core_tendsto_atTop.eventually_ge_atTop
    (max (n + h) (m + k) + 5)
  filter_upwards [he, hcore] with U hsmall hU
  have hid := native_agreement_mass_eq_seven_correlations n h m k
    (preciseCore U + 1) (preciseCore U * preciseCore U + 1)
    hn.pos hh hm.pos hk (by omega) (by omega) (by omega)
  have hdiff : nativeAgreementMass n h m k (preciseCore U + 1)
      (preciseCore U * preciseCore U + 1) -
      3 * reciprocalBand (preciseCore U + 1)
        (preciseCore U * preciseCore U + 1) / 8 =
      nativeAgreementRemainder n h m k
        (preciseCore U + 1) (preciseCore U * preciseCore U + 1) := by
    rw [hid]
    ring
  simp only [Real.dist_eq, sub_zero] at hsmall
  simp only [Real.dist_eq, sub_zero]
  rw [hdiff]
  exact hsmall

end PrimeFactorOscillations.FiniteFieldIntegerSignature

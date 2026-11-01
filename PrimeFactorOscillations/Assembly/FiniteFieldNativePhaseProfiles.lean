/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Assembly.FiniteFieldNativePhaseEvents

/-! # Exact joint and phase-conditioned native profile probabilities -/

set_option autoImplicit false
set_option Elab.async false

noncomputable section
namespace PrimeFactorOscillations.FiniteFieldIntegerSignature
open Filter IntegerQuadraticCharacter FiniteFieldIntegerWindowTransfer
open scoped Classical
attribute [local instance] Classical.propDecidable

theorem native_phase_fixed_correlation_ratio_tendsto (D : Int) (hD : Not (D = 0)) :
    Tendsto (fun U : Nat =>
      primeCorrelation D (preciseCore U + 1) (preciseCore U * preciseCore U + 1) /
        reciprocalBand (preciseCore U + 1) (preciseCore U * preciseCore U + 1))
      atTop (nhds (numeratorPrincipalIndicator D)) :=
  native_prime_band_ratio_tendsto_of_centered _ _
    (prime_correlation_principal_centered_tendsto_zero D hD)

theorem native_minus_one_principal_indicator_zero :
    numeratorPrincipalIndicator (-1) = 0 := by
  have hn : Not (IsSquare (-1 : Int)) := by
    intro h
    choose k hk using h
    have hp := mul_self_nonneg k
    rw [<- hk] at hp
    omega
  rw [numerator_principal_indicator_int_eq_square (-1) (by decide), ite_eq_right hn]

theorem native_phase_band_ratio_tendsto (b : Bool) :
    Tendsto (fun U : Nat =>
      nativePhaseBand b (preciseCore U + 1) (preciseCore U * preciseCore U + 1) /
        reciprocalBand (preciseCore U + 1) (preciseCore U * preciseCore U + 1))
      atTop (nhds (1 / 2 : Real)) := by
  have h0 := native_phase_fixed_correlation_ratio_tendsto (-1) (by decide)
  rw [native_minus_one_principal_indicator_zero] at h0
  have hlim : Tendsto (fun U : Nat => (1 / 2 : Real) +
      (nativeWordSign b / 2) *
        (primeCorrelation (-1) (preciseCore U + 1) (preciseCore U * preciseCore U + 1) /
          reciprocalBand (preciseCore U + 1) (preciseCore U * preciseCore U + 1)))
      atTop (nhds (1 / 2 : Real)) := by
    simpa only [mul_zero, add_zero] using
      (tendsto_const_nhds : Tendsto (fun _ : Nat => (1 / 2 : Real)) atTop
        (nhds (1 / 2 : Real))).add (Filter.Tendsto.const_mul (nativeWordSign b / 2) h0)
  apply hlim.congr'
  filter_upwards [precise_core_tendsto_atTop.eventually_ge_atTop 3,
    precise_core_tendsto_atTop.eventually eventually_reciprocal_square_band_positive]
    with U h3 hMass
  have hM : (0 : Real) <
      reciprocalBand (preciseCore U + 1) (preciseCore U * preciseCore U + 1) :=
    (show (0 : Real) < Real.log 2 / 2 by positivity).trans_le hMass
  rw [native_phase_band_expansion b _ _ (by omega)]
  simp only [add_div, mul_div_assoc, div_self (ne_of_gt hM), mul_one]

theorem native_phase_band_eventually_positive (b : Bool) :
    Filter.Eventually (fun U : Nat =>
      (0 : Real) < nativePhaseBand b (preciseCore U + 1)
        (preciseCore U * preciseCore U + 1)) atTop := by
  have hp := (native_phase_band_ratio_tendsto b).eventually
    (Ioi_mem_nhds (show (0 : Real) < 1 / 2 by norm_num))
  filter_upwards [hp,
    precise_core_tendsto_atTop.eventually eventually_reciprocal_square_band_positive]
    with U hRatio hMass
  have hM : (0 : Real) <
      reciprocalBand (preciseCore U + 1) (preciseCore U * preciseCore U + 1) :=
    (show (0 : Real) < Real.log 2 / 2 by positivity).trans_le hMass
  have hid : nativePhaseBand b (preciseCore U + 1) (preciseCore U * preciseCore U + 1) =
      (nativePhaseBand b (preciseCore U + 1) (preciseCore U * preciseCore U + 1) /
        reciprocalBand (preciseCore U + 1) (preciseCore U * preciseCore U + 1)) *
        reciprocalBand (preciseCore U + 1) (preciseCore U * preciseCore U + 1) := by
    field_simp [ne_of_gt hM]
  rw [hid]
  exact mul_pos hRatio hM

theorem native_word_sign_power_parity (b : Bool) (n : Nat) :
    nativeWordSign b ^ n = if n % 2 = 0 then 1 else nativeWordSign b := by
  by_cases hn : n % 2 = 0
  . rw [ite_eq_left hn]
    have he : n = 2 * (n / 2) := by omega
    rw [he, pow_mul, native_word_sign_square b, one_pow]
  . rw [ite_eq_right hn]
    have he : n = 2 * (n / 2) + 1 := by omega
    rw [he, pow_add, pow_mul, native_word_sign_square b, one_pow, pow_one, one_mul]

theorem native_phase_diagonal_indicator (P : Finset Nat)
    (hP : forall p : Nat, Membership.mem P p -> Nat.Prime p)
    (C : Finset (Prod Nat Nat)) (hC : C <= nativePrimeVertexEdges P) (b : Bool) :
    numeratorPrincipalIndicator (nativeSignedRowProduct C C) +
      nativeWordSign b * numeratorPrincipalIndicator (-nativeSignedRowProduct C C) =
        if (forall p : Nat, Membership.mem P p ->
          nativePrimeVertexCycleDegree C p % 2 = 0)
        then nativeWordSign b ^ C.card else 0 := by
  have hnz := native_signed_row_product_ne_zero P hP C C hC hC
  rw [numerator_principal_indicator_int_eq_square _ hnz,
    numerator_principal_indicator_int_eq_square _ (neg_ne_zero.mpr hnz)]
  by_cases hd : (forall p : Nat, Membership.mem P p ->
      nativePrimeVertexCycleDegree C p % 2 = 0)
  . by_cases hc : C.card % 2 = 0
    . have hsq := (native_signed_diagonal_isSquare_iff P hP C hC).mpr (And.intro hd hc)
      have hneg : Not (IsSquare (-nativeSignedRowProduct C C)) := by
        intro h
        have ho := ((native_negative_diagonal_isSquare_iff P hP C hC).mp h).2
        omega
      rw [ite_eq_left hsq, ite_eq_right hneg, ite_eq_left hd,
        native_word_sign_power_parity b C.card, ite_eq_left hc]
      ring
    . have ho : C.card % 2 = 1 := by omega
      have hsq := (native_negative_diagonal_isSquare_iff P hP C hC).mpr (And.intro hd ho)
      have hpos : Not (IsSquare (nativeSignedRowProduct C C)) :=
        fun h => hc ((native_signed_diagonal_isSquare_iff P hP C hC).mp h).2
      rw [ite_eq_right hpos, ite_eq_left hsq, ite_eq_left hd,
        native_word_sign_power_parity b C.card, ite_eq_right hc]
      ring
  . have hpos : Not (IsSquare (nativeSignedRowProduct C C)) :=
      fun h => hd ((native_signed_diagonal_isSquare_iff P hP C hC).mp h).1
    have hneg : Not (IsSquare (-nativeSignedRowProduct C C)) :=
      fun h => hd ((native_negative_diagonal_isSquare_iff P hP C hC).mp h).1
    rw [ite_eq_right hpos, ite_eq_right hneg, ite_eq_right hd]
    ring

theorem native_phase_profile_general_ratio_tendsto (P : Finset Nat)
    (hP : forall p : Nat, Membership.mem P p -> Nat.Prime p)
    (G : Finset (Prod Nat Nat)) (hG : G <= nativePrimeVertexEdges P)
    (a : Prod Nat Nat -> Bool) (b : Bool) :
    Tendsto (fun U : Nat =>
      nativePhaseProfileMass G a b (preciseCore U + 1)
        (preciseCore U * preciseCore U + 1) /
        reciprocalBand (preciseCore U + 1) (preciseCore U * preciseCore U + 1))
      atTop (nhds (nativePhaseProfileRate G a b)) := by
  let K : Real := 1 / (2 : Real) ^ (G.card + 1)
  let F : Nat -> Real := fun U =>
    K * G.powerset.sum (fun C => nativeVanishingProfileCoefficient C a *
      (primeCorrelation (nativeSignedRowProduct C C) (preciseCore U + 1)
          (preciseCore U * preciseCore U + 1) /
          reciprocalBand (preciseCore U + 1) (preciseCore U * preciseCore U + 1) +
        nativeWordSign b *
          (primeCorrelation (-nativeSignedRowProduct C C) (preciseCore U + 1)
              (preciseCore U * preciseCore U + 1) /
            reciprocalBand (preciseCore U + 1) (preciseCore U * preciseCore U + 1))))
  have hlim : Tendsto F atTop (nhds (nativePhaseProfileRate G a b)) := by
    dsimp only [F, K, nativePhaseProfileRate]
    apply Filter.Tendsto.const_mul
    apply tendsto_finsetSum G.powerset
    intro C hC
    have hsub := (Finset.mem_powerset.mp hC).trans hG
    have hnz := native_signed_row_product_ne_zero P hP C C hsub hsub
    exact Filter.Tendsto.const_mul (nativeVanishingProfileCoefficient C a)
      ((native_phase_fixed_correlation_ratio_tendsto _ hnz).add
        (Filter.Tendsto.const_mul (nativeWordSign b)
          (native_phase_fixed_correlation_ratio_tendsto _ (neg_ne_zero.mpr hnz))))
  apply hlim.congr'
  filter_upwards [native_phase_profile_mass_expansion_eventually P hP G hG a b] with U hU
  dsimp only [F, K]
  rw [hU]
  simp only [mul_div_assoc, Finset.sum_div, add_div]

theorem native_phase_compatible_rate (P : Finset Nat)
    (hP : forall p : Nat, Membership.mem P p -> Nat.Prime p)
    (G : Finset (Prod Nat Nat)) (hG : G <= nativePrimeVertexEdges P)
    (a : Prod Nat Nat -> Bool) (b : Bool) (hc : nativePhaseProfileCompatible P G a b) :
    nativePhaseProfileRate G a b =
      (1 / (2 : Real) ^ (G.card + 1)) * (nativeEulerianCount P G : Real) := by
  let f := fun C : Finset (Prod Nat Nat) => nativeVanishingProfileCoefficient C a *
    (numeratorPrincipalIndicator (nativeSignedRowProduct C C) +
      nativeWordSign b * numeratorPrincipalIndicator (-nativeSignedRowProduct C C))
  have hsub : nativeEulerianMasks P G <= G.powerset := Finset.filter_subset _ _
  have ho : forall C : Finset (Prod Nat Nat), Membership.mem G.powerset C ->
      Not (Membership.mem (nativeEulerianMasks P G) C) -> f C = 0 := by
    intro C hC hn
    have hCG := Finset.mem_powerset.mp hC
    have hd : Not (forall p : Nat, Membership.mem P p ->
        nativePrimeVertexCycleDegree C p % 2 = 0) :=
      fun h => hn ((native_eulerian_masks_mem_iff P G C).mpr (And.intro hCG h))
    change nativeVanishingProfileCoefficient C a * _ = 0
    rw [native_phase_diagonal_indicator P hP C (hCG.trans hG) b, ite_eq_right hd, mul_zero]
  have hm : (nativeEulerianMasks P G).sum f = (nativeEulerianCount P G : Real) := by
    calc
      _ = (nativeEulerianMasks P G).sum (fun _ => (1 : Real)) := by
        apply Finset.sum_congr rfl
        intro C hC
        have hh := (native_eulerian_masks_mem_iff P G C).mp hC
        change nativeVanishingProfileCoefficient C a * _ = 1
        rw [hc C hC, native_phase_diagonal_indicator P hP C (hh.1.trans hG) b,
          ite_eq_left hh.2, <- pow_two, <- pow_mul, Nat.mul_comm C.card 2,
          pow_mul, native_word_sign_square b, one_pow]
      _ = _ := by simp [nativeEulerianCount]
  have hall : G.powerset.sum f = (nativeEulerianCount P G : Real) :=
    (Finset.sum_subset hsub ho).symm.trans hm
  change (1 / (2 : Real) ^ (G.card + 1)) * G.powerset.sum f =
    (1 / (2 : Real) ^ (G.card + 1)) * (nativeEulerianCount P G : Real)
  rw [hall]

theorem native_phase_incompatible_rate (P : Finset Nat)
    (hP : forall p : Nat, Membership.mem P p -> Nat.Prime p)
    (G : Finset (Prod Nat Nat)) (hG : G <= nativePrimeVertexEdges P)
    (a : Prod Nat Nat -> Bool) (b : Bool) (hn : Not (nativePhaseProfileCompatible P G a b)) :
    nativePhaseProfileRate G a b = 0 := by
  have hlim := native_phase_profile_general_ratio_tendsto P hP G hG a b
  have hz : Tendsto (fun U : Nat =>
      nativePhaseProfileMass G a b (preciseCore U + 1)
        (preciseCore U * preciseCore U + 1) /
        reciprocalBand (preciseCore U + 1) (preciseCore U * preciseCore U + 1))
      atTop (nhds (0 : Real)) := by
    apply tendsto_const_nhds.congr'
    filter_upwards [native_phase_incompatible_mass_zero_eventually P hP G hG a b hn]
      with U hU
    rw [hU, zero_div]
  exact tendsto_nhds_unique hlim hz

theorem native_phase_profile_rate_eq (P : Finset Nat)
    (hP : forall p : Nat, Membership.mem P p -> Nat.Prime p)
    (G : Finset (Prod Nat Nat)) (hG : G <= nativePrimeVertexEdges P)
    (a : Prod Nat Nat -> Bool) (b : Bool) :
    nativePhaseProfileRate G a b =
      if nativePhaseProfileCompatible P G a b then
        (1 / (2 : Real) ^ (G.card + 1)) * (nativeEulerianCount P G : Real) else 0 := by
  by_cases hc : nativePhaseProfileCompatible P G a b
  . rw [ite_eq_left hc]
    exact native_phase_compatible_rate P hP G hG a b hc
  . rw [ite_eq_right hc]
    exact native_phase_incompatible_rate P hP G hG a b hc

theorem native_phase_profile_joint_ratio_tendsto (P : Finset Nat)
    (hP : forall p : Nat, Membership.mem P p -> Nat.Prime p)
    (G : Finset (Prod Nat Nat)) (hG : G <= nativePrimeVertexEdges P)
    (a : Prod Nat Nat -> Bool) (b : Bool) :
    Tendsto (fun U : Nat =>
      nativePhaseProfileMass G a b (preciseCore U + 1)
        (preciseCore U * preciseCore U + 1) /
        reciprocalBand (preciseCore U + 1) (preciseCore U * preciseCore U + 1))
      atTop (nhds (if nativePhaseProfileCompatible P G a b then
        (1 / (2 : Real) ^ (G.card + 1)) * (nativeEulerianCount P G : Real) else 0)) := by
  rw [<- native_phase_profile_rate_eq P hP G hG a b]
  exact native_phase_profile_general_ratio_tendsto P hP G hG a b

theorem native_phase_profile_conditional_ratio_tendsto (P : Finset Nat)
    (hP : forall p : Nat, Membership.mem P p -> Nat.Prime p)
    (G : Finset (Prod Nat Nat)) (hG : G <= nativePrimeVertexEdges P)
    (a : Prod Nat Nat -> Bool) (b : Bool) :
    Tendsto (fun U : Nat =>
      nativePhaseProfileMass G a b (preciseCore U + 1)
        (preciseCore U * preciseCore U + 1) /
        nativePhaseBand b (preciseCore U + 1) (preciseCore U * preciseCore U + 1))
      atTop (nhds (if nativePhaseProfileCompatible P G a b then
        (1 / (2 : Real) ^ G.card) * (nativeEulerianCount P G : Real) else 0)) := by
  have hj := native_phase_profile_joint_ratio_tendsto P hP G hG a b
  have hb := native_phase_band_ratio_tendsto b
  have hlim := hj.div hb (show Not ((1 / 2 : Real) = 0) by norm_num)
  have hc : ((if nativePhaseProfileCompatible P G a b then
        (1 / (2 : Real) ^ (G.card + 1)) * (nativeEulerianCount P G : Real) else 0) /
        (1 / 2 : Real)) =
      (if nativePhaseProfileCompatible P G a b then
        (1 / (2 : Real) ^ G.card) * (nativeEulerianCount P G : Real) else 0) := by
    by_cases h : nativePhaseProfileCompatible P G a b
    . rw [ite_eq_left h, ite_eq_left h, pow_succ]
      have h2 : Not ((2 : Real) ^ G.card = 0) := pow_ne_zero _ (by norm_num)
      field_simp [h2]
    . rw [ite_eq_right h, ite_eq_right h]
      norm_num
  rw [hc] at hlim
  apply hlim.congr'
  filter_upwards [native_phase_band_eventually_positive b,
    precise_core_tendsto_atTop.eventually eventually_reciprocal_square_band_positive]
    with U hB hMass
  have hM : (0 : Real) <
      reciprocalBand (preciseCore U + 1) (preciseCore U * preciseCore U + 1) :=
    (show (0 : Real) < Real.log 2 / 2 by positivity).trans_le hMass
  simp only [Pi.div_apply]
  field_simp [ne_of_gt hM, ne_of_gt hB]

end PrimeFactorOscillations.FiniteFieldIntegerSignature

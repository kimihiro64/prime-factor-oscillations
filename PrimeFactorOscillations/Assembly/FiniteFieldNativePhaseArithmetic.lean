/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Assembly.FiniteFieldNativePhaseProfiles
import PrimeFactorOscillations.Helpers.NativePrimeEulerianGeometry
import PrimeFactorOscillations.Mathlib.NumberTheory.LegendreSymbol.QuadraticPairOddPellArithmetic

/-! # Actual central-weight profiles in the two odd prime residue classes -/

set_option autoImplicit false
set_option Elab.async false

noncomputable section
namespace PrimeFactorOscillations.FiniteFieldIntegerSignature
open Filter IntegerQuadraticCharacter FiniteFieldIntegerCharacter
open FiniteFieldIntegerWindowTransfer
open scoped Classical
attribute [local instance] Classical.propDecidable

def nativeModuloFourBand (b : Bool) (Y X : Nat) : Real :=
  ((Finset.Ico Y X).filter Nat.Prime).sum (fun ell =>
    (1 / (ell : Real)) * (if ell % 4 = (if b then 1 else 3) then 1 else 0))

def nativeCentralPhaseProfileEvent (G : Finset (Prod Nat Nat))
    (a : Prod Nat Nat -> Bool) (b : Bool) (ell : Nat) : Prop :=
  And (nativeQuadraticPhaseEvent b ell) (nativeCentralProfileEvent G a ell)

def nativeCentralPhaseProfileMass (G : Finset (Prod Nat Nat))
    (a : Prod Nat Nat -> Bool) (b : Bool) (Y X : Nat) : Real :=
  ((Finset.Ico Y X).filter Nat.Prime).sum (fun ell =>
    (1 / (ell : Real)) * (if nativeCentralPhaseProfileEvent G a b ell then 1 else 0))

theorem native_quadratic_phase_mod_four (ell : Nat) (hell : Nat.Prime ell) (hell2 : 2 < ell) :
    Or (And (nativeQuadraticPhase ell = 1) (ell % 4 = 1))
      (And (nativeQuadraticPhase ell = -1) (ell % 4 = 3)) := by
  let : Fact (Nat.Prime ell) := Fact.mk hell
  have hF : Not (ringChar (ZMod ell) = 2) := by
    simpa only [ZMod.ringChar_zmod_n] using (show Not (ell = 2) by omega)
  have hid : nativeQuadraticPhase ell =
      ((quadraticChar (ZMod ell) (-1) : Int) : Real) := by
    unfold nativeQuadraticPhase
    rw [numerator_kernel_prime (-1) ell (by omega)]
    simp
  have h := _root_.FiniteField.oddPell_character_mod_four (F := ZMod ell) hF
  rcases h with h | h
  . refine Or.inl (And.intro ?_ ?_)
    . rw [hid, h.1]
      norm_num
    . simpa only [ZMod.card] using h.2
  . refine Or.inr (And.intro ?_ ?_)
    . rw [hid, h.1]
      norm_num
    . simpa only [ZMod.card] using h.2

theorem native_phase_event_mod_four (b : Bool) (ell : Nat)
    (hell : Nat.Prime ell) (hell2 : 2 < ell) :
    nativeQuadraticPhaseEvent b ell <-> ell % 4 = (if b then 1 else 3) := by
  unfold nativeQuadraticPhaseEvent
  rcases native_quadratic_phase_mod_four ell hell hell2 with h | h
  . rw [h.1, h.2]
    cases b <;> norm_num [nativeWordSign]
  . rw [h.1, h.2]
    cases b <;> norm_num [nativeWordSign]

theorem native_phase_band_eq_mod_four (b : Bool) (Y X : Nat) (hY : 2 < Y) :
    nativePhaseBand b Y X = nativeModuloFourBand b Y X := by
  unfold nativePhaseBand nativeModuloFourBand
  apply Finset.sum_congr rfl
  intro ell hell
  have hh := Finset.mem_filter.mp hell
  have hb := Finset.mem_Ico.mp hh.1
  have hi := native_phase_event_mod_four b ell hh.2 (by omega)
  by_cases h : nativeQuadraticPhaseEvent b ell
  . rw [ite_eq_left h, ite_eq_left (hi.mp h)]
  . have hn : Not (ell % 4 = (if b then 1 else 3)) := fun he => h (hi.mpr he)
    rw [ite_eq_right h, ite_eq_right hn]

theorem native_mod_four_band_ratio_tendsto (b : Bool) :
    Tendsto (fun U : Nat =>
      nativeModuloFourBand b (preciseCore U + 1) (preciseCore U * preciseCore U + 1) /
        reciprocalBand (preciseCore U + 1) (preciseCore U * preciseCore U + 1))
      atTop (nhds (1 / 2 : Real)) := by
  apply (native_phase_band_ratio_tendsto b).congr'
  filter_upwards [precise_core_tendsto_atTop.eventually_ge_atTop 3] with U hU
  rw [native_phase_band_eq_mod_four b _ _ (by omega)]

theorem native_central_phase_profile_iff (P : Finset Nat)
    (hP : forall p : Nat, Membership.mem P p -> Nat.Prime p)
    (G : Finset (Prod Nat Nat)) (hG : G <= nativePrimeVertexEdges P)
    (a : Prod Nat Nat -> Bool) (b : Bool) (ell : Nat)
    (hell : Nat.Prime ell) (hell5 : 5 <= ell)
    (hlarge : forall p : Nat, Membership.mem P p -> p < ell) :
    nativeCentralPhaseProfileEvent G a b ell <-> nativePhaseProfileEvent G a b ell := by
  have hi := native_central_profile_iff_vanishing P hP G hG a ell hell hell5 hlarge
  constructor
  . intro h
    exact And.intro h.1 (hi.mp h.2)
  . intro h
    exact And.intro h.1 (hi.mpr h.2)

theorem native_central_phase_profile_mod_four_iff (G : Finset (Prod Nat Nat))
    (a : Prod Nat Nat -> Bool) (b : Bool) (ell : Nat)
    (hell : Nat.Prime ell) (hell2 : 2 < ell) :
    nativeCentralPhaseProfileEvent G a b ell <->
      And (ell % 4 = (if b then 1 else 3)) (nativeCentralProfileEvent G a ell) := by
  have hi := native_phase_event_mod_four b ell hell hell2
  constructor
  . intro h
    exact And.intro (hi.mp h.1) h.2
  . intro h
    exact And.intro (hi.mpr h.1) h.2

theorem native_central_phase_profile_mass_eq (P : Finset Nat)
    (hP : forall p : Nat, Membership.mem P p -> Nat.Prime p)
    (G : Finset (Prod Nat Nat)) (hG : G <= nativePrimeVertexEdges P)
    (a : Prod Nat Nat -> Bool) (b : Bool) (Y X : Nat) (hY : 5 <= Y)
    (hPY : forall p : Nat, Membership.mem P p -> p < Y) :
    nativeCentralPhaseProfileMass G a b Y X = nativePhaseProfileMass G a b Y X := by
  unfold nativeCentralPhaseProfileMass nativePhaseProfileMass
  apply Finset.sum_congr rfl
  intro ell hell
  have hh := Finset.mem_filter.mp hell
  have hb := Finset.mem_Ico.mp hh.1
  have hlarge : forall p : Nat, Membership.mem P p -> p < ell :=
    fun p hp => (hPY p hp).trans_le hb.1
  have hi := native_central_phase_profile_iff P hP G hG a b ell hh.2 (hY.trans hb.1) hlarge
  by_cases h : nativeCentralPhaseProfileEvent G a b ell
  . rw [ite_eq_left h, ite_eq_left (hi.mp h)]
  . have hn : Not (nativePhaseProfileEvent G a b ell) := fun ht => h (hi.mpr ht)
    rw [ite_eq_right h, ite_eq_right hn]

theorem native_central_phase_profile_mass_eq_eventually (P : Finset Nat)
    (hP : forall p : Nat, Membership.mem P p -> Nat.Prime p)
    (G : Finset (Prod Nat Nat)) (hG : G <= nativePrimeVertexEdges P)
    (a : Prod Nat Nat -> Bool) (b : Bool) :
    Filter.Eventually (fun U : Nat =>
      nativeCentralPhaseProfileMass G a b (preciseCore U + 1)
        (preciseCore U * preciseCore U + 1) =
      nativePhaseProfileMass G a b (preciseCore U + 1)
        (preciseCore U * preciseCore U + 1)) atTop := by
  filter_upwards [native_graph_field_window_eventually P,
    precise_core_tendsto_atTop.eventually_ge_atTop 4] with U hU h4
  exact native_central_phase_profile_mass_eq P hP G hG a b _ _ (by omega) hU.2

theorem native_central_phase_profile_joint_ratio_tendsto (P : Finset Nat)
    (hP : forall p : Nat, Membership.mem P p -> Nat.Prime p)
    (G : Finset (Prod Nat Nat)) (hG : G <= nativePrimeVertexEdges P)
    (a : Prod Nat Nat -> Bool) (b : Bool) :
    Tendsto (fun U : Nat =>
      nativeCentralPhaseProfileMass G a b (preciseCore U + 1)
        (preciseCore U * preciseCore U + 1) /
        reciprocalBand (preciseCore U + 1) (preciseCore U * preciseCore U + 1))
      atTop (nhds (if nativePhaseProfileCompatible P G a b then
        (1 / (2 : Real) ^ (G.card + 1)) * (nativeEulerianCount P G : Real) else 0)) := by
  apply (native_phase_profile_joint_ratio_tendsto P hP G hG a b).congr'
  filter_upwards [native_central_phase_profile_mass_eq_eventually P hP G hG a b] with U hU
  rw [hU]

theorem native_central_phase_profile_conditional_ratio_tendsto (P : Finset Nat)
    (hP : forall p : Nat, Membership.mem P p -> Nat.Prime p)
    (G : Finset (Prod Nat Nat)) (hG : G <= nativePrimeVertexEdges P)
    (a : Prod Nat Nat -> Bool) (b : Bool) :
    Tendsto (fun U : Nat =>
      nativeCentralPhaseProfileMass G a b (preciseCore U + 1)
        (preciseCore U * preciseCore U + 1) /
        nativePhaseBand b (preciseCore U + 1) (preciseCore U * preciseCore U + 1))
      atTop (nhds (if nativePhaseProfileCompatible P G a b then
        (1 / (2 : Real) ^ G.card) * (nativeEulerianCount P G : Real) else 0)) := by
  apply (native_phase_profile_conditional_ratio_tendsto P hP G hG a b).congr'
  filter_upwards [native_central_phase_profile_mass_eq_eventually P hP G hG a b] with U hU
  rw [hU]

theorem native_central_profile_mod_four_ratio_tendsto (P : Finset Nat)
    (hP : forall p : Nat, Membership.mem P p -> Nat.Prime p)
    (G : Finset (Prod Nat Nat)) (hG : G <= nativePrimeVertexEdges P)
    (a : Prod Nat Nat -> Bool) (b : Bool) :
    Tendsto (fun U : Nat =>
      nativeCentralPhaseProfileMass G a b (preciseCore U + 1)
        (preciseCore U * preciseCore U + 1) /
        nativeModuloFourBand b (preciseCore U + 1) (preciseCore U * preciseCore U + 1))
      atTop (nhds (if nativePhaseProfileCompatible P G a b then
        (1 / (2 : Real) ^ G.card) * (nativeEulerianCount P G : Real) else 0)) := by
  apply (native_central_phase_profile_conditional_ratio_tendsto P hP G hG a b).congr'
  filter_upwards [precise_core_tendsto_atTop.eventually_ge_atTop 3] with U hU
  rw [native_phase_band_eq_mod_four b _ _ (by omega)]


theorem native_phase_small_profile_compatible (P : Finset Nat)
    (G : Finset (Prod Nat Nat)) (hG : G <= nativePrimeVertexEdges P)
    (hc : G.card <= 2) (a : Prod Nat Nat -> Bool) (b : Bool) :
    nativePhaseProfileCompatible P G a b := by
  unfold nativePhaseProfileCompatible
  rw [native_phase_eulerian_masks_small P G hG hc]
  intro C hC
  have hz := Finset.mem_singleton.mp hC
  rw [hz]
  simp [nativeVanishingProfileCoefficient]

theorem native_small_central_profile_mod_four_ratio_tendsto (P : Finset Nat)
    (hP : forall p : Nat, Membership.mem P p -> Nat.Prime p)
    (G : Finset (Prod Nat Nat)) (hG : G <= nativePrimeVertexEdges P)
    (hc : G.card <= 2) (a : Prod Nat Nat -> Bool) (b : Bool) :
    Tendsto (fun U : Nat =>
      nativeCentralPhaseProfileMass G a b (preciseCore U + 1)
        (preciseCore U * preciseCore U + 1) /
        nativeModuloFourBand b (preciseCore U + 1) (preciseCore U * preciseCore U + 1))
      atTop (nhds (1 / (2 : Real) ^ G.card)) := by
  simpa only [ite_eq_left (native_phase_small_profile_compatible P G hG hc a b),
    native_phase_eulerian_count_small P G hG hc, Nat.cast_one, mul_one] using
    native_central_profile_mod_four_ratio_tendsto P hP G hG a b

theorem native_triangle_phase_profile_compatible_iff (P : Finset Nat) (p q r : Nat)
    (hp : Membership.mem P p) (hq : Membership.mem P q) (hr : Membership.mem P r)
    (hpq : p < q) (hqr : q < r) (a : Prod Nat Nat -> Bool) (b : Bool) :
    nativePhaseProfileCompatible P {(p, q), (q, r), (p, r)} a b <->
      nativeVanishingProfileCoefficient {(p, q), (q, r), (p, r)} a = nativeWordSign b := by
  have hpow : nativeWordSign b ^
      ({(p, q), (q, r), (p, r)} : Finset (Prod Nat Nat)).card = nativeWordSign b := by
    rw [native_phase_triangle_card p q r hpq hqr, native_word_sign_power_parity]
    norm_num
  unfold nativePhaseProfileCompatible
  rw [native_phase_triangle_eulerian_masks P p q r hp hq hr hpq hqr]
  constructor
  . intro h
    have hh := h {(p, q), (q, r), (p, r)} (by simp)
    rw [hpow] at hh
    exact hh
  . intro h C hC
    simp only [Finset.mem_insert, Finset.mem_singleton] at hC
    rcases hC with rfl | rfl
    . simp [nativeVanishingProfileCoefficient]
    . rw [hpow]
      exact h

theorem native_triangle_central_profile_mod_four_ratio_tendsto (P : Finset Nat)
    (hP : forall p : Nat, Membership.mem P p -> Nat.Prime p) (p q r : Nat)
    (hp : Membership.mem P p) (hq : Membership.mem P q) (hr : Membership.mem P r)
    (hpq : p < q) (hqr : q < r) (a : Prod Nat Nat -> Bool) (b : Bool) :
    Tendsto (fun U : Nat =>
      nativeCentralPhaseProfileMass {(p, q), (q, r), (p, r)} a b (preciseCore U + 1)
        (preciseCore U * preciseCore U + 1) /
        nativeModuloFourBand b (preciseCore U + 1) (preciseCore U * preciseCore U + 1))
      atTop (nhds (if nativeVanishingProfileCoefficient {(p, q), (q, r), (p, r)} a =
        nativeWordSign b then (1 / 4 : Real) else 0)) := by
  have h := native_central_profile_mod_four_ratio_tendsto P hP
    {(p, q), (q, r), (p, r)} (native_phase_triangle_support P p q r hp hq hr hpq hqr) a b
  rw [native_triangle_phase_profile_compatible_iff P p q r hp hq hr hpq hqr a b,
    native_phase_triangle_eulerian_count P p q r hp hq hr hpq hqr,
    native_phase_triangle_card p q r hpq hqr] at h
  norm_num at h
  exact h

theorem native_four_cycle_phase_profile_compatible_iff (P : Finset Nat) (p q r s : Nat)
    (hp : Membership.mem P p) (hq : Membership.mem P q)
    (hr : Membership.mem P r) (hs : Membership.mem P s)
    (hpq : p < q) (hqr : q < r) (hrs : r < s)
    (a : Prod Nat Nat -> Bool) (b : Bool) :
    nativePhaseProfileCompatible P (nativePrimeFourCycle p q r s) a b <->
      nativeVanishingProfileCoefficient (nativePrimeFourCycle p q r s) a = 1 := by
  have hpow : nativeWordSign b ^ (nativePrimeFourCycle p q r s).card = 1 := by
    rw [native_four_cycle_card p q r s hpq hqr hrs, native_word_sign_power_parity]
    norm_num
  unfold nativePhaseProfileCompatible
  rw [native_phase_four_cycle_eulerian_masks P p q r s hp hq hr hs hpq hqr hrs]
  constructor
  . intro h
    have hh := h (nativePrimeFourCycle p q r s) (by simp)
    rw [hpow] at hh
    exact hh
  . intro h C hC
    simp only [Finset.mem_insert, Finset.mem_singleton] at hC
    rcases hC with rfl | rfl
    . simp [nativeVanishingProfileCoefficient]
    . rw [hpow]
      exact h

theorem native_four_cycle_central_profile_mod_four_ratio_tendsto (P : Finset Nat)
    (hP : forall p : Nat, Membership.mem P p -> Nat.Prime p) (p q r s : Nat)
    (hp : Membership.mem P p) (hq : Membership.mem P q)
    (hr : Membership.mem P r) (hs : Membership.mem P s)
    (hpq : p < q) (hqr : q < r) (hrs : r < s)
    (a : Prod Nat Nat -> Bool) (b : Bool) :
    Tendsto (fun U : Nat =>
      nativeCentralPhaseProfileMass (nativePrimeFourCycle p q r s) a b (preciseCore U + 1)
        (preciseCore U * preciseCore U + 1) /
        nativeModuloFourBand b (preciseCore U + 1) (preciseCore U * preciseCore U + 1))
      atTop (nhds (if nativeVanishingProfileCoefficient (nativePrimeFourCycle p q r s) a = 1
        then (1 / 8 : Real) else 0)) := by
  have h := native_central_profile_mod_four_ratio_tendsto P hP
    (nativePrimeFourCycle p q r s)
    (native_four_cycle_support P p q r s hp hq hr hs hpq hqr hrs) a b
  rw [native_four_cycle_phase_profile_compatible_iff P p q r s hp hq hr hs hpq hqr hrs a b,
    native_phase_four_cycle_eulerian_count P p q r s hp hq hr hs hpq hqr hrs,
    native_four_cycle_card p q r s hpq hqr hrs] at h
  norm_num at h
  exact h

end PrimeFactorOscillations.FiniteFieldIntegerSignature

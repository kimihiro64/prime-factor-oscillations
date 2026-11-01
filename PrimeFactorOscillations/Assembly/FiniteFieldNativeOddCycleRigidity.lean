/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Assembly.FiniteFieldNativePhaseArithmetic

/-! # Odd-cycle rigidity of synchronized native weights

The integer prime graph stays fixed. Negative field phase eliminates both
nonzero synchronized trace events pointwise, without gap independence.
-/

set_option autoImplicit false
set_option Elab.async false

noncomputable section
namespace PrimeFactorOscillations.FiniteFieldIntegerSignature
open Filter IntegerQuadraticCharacter FiniteFieldIntegerWindowTransfer
open scoped Classical
attribute [local instance] Classical.propDecidable

theorem native_constant_profile_coefficient (C : Finset (Prod Nat Nat)) (b : Bool) :
    nativeVanishingProfileCoefficient C (fun _ => b) = nativeWordSign b ^ C.card := by
  simp [nativeVanishingProfileCoefficient]

theorem native_central_negative_phase_compatible (P : Finset Nat)
    (G : Finset (Prod Nat Nat)) :
    nativePhaseProfileCompatible P G (fun _ => false) false := by
  intro C _
  exact native_constant_profile_coefficient C false

theorem native_noncentral_positive_phase_compatible (P : Finset Nat)
    (G : Finset (Prod Nat Nat)) :
    nativePhaseProfileCompatible P G (fun _ => true) true := by
  intro C _
  exact native_constant_profile_coefficient C true

theorem native_odd_mask_noncentral_negative_impossible (P : Finset Nat)
    (hP : forall p : Nat, Membership.mem P p -> Nat.Prime p)
    (G : Finset (Prod Nat Nat)) (hG : G <= nativePrimeVertexEdges P)
    (C : Finset (Prod Nat Nat)) (hCG : C <= G)
    (hdeg : forall p : Nat, Membership.mem P p -> nativePrimeVertexCycleDegree C p % 2 = 0)
    (hodd : C.card % 2 = 1) (ell : Nat) (hell : Nat.Prime ell) (hell2 : 2 < ell)
    (hlarge : forall p : Nat, Membership.mem P p -> p < ell)
    (hphase : nativeQuadraticPhaseEvent false ell) :
    Not (nativeVanishingProfileEvent G (fun _ => true) ell) := by
  intro hevent
  have hc := native_phase_profile_event_compatible P hP G hG (fun _ => true) false
    ell hell hell2 hlarge (And.intro hphase hevent)
  have hh := hc C ((native_eulerian_masks_mem_iff P G C).mpr (And.intro hCG hdeg))
  simp only [native_constant_profile_coefficient, native_word_sign_power_parity] at hh
  norm_num [nativeWordSign, hodd] at hh

theorem native_odd_mask_central_positive_impossible (P : Finset Nat)
    (hP : forall p : Nat, Membership.mem P p -> Nat.Prime p)
    (G : Finset (Prod Nat Nat)) (hG : G <= nativePrimeVertexEdges P)
    (C : Finset (Prod Nat Nat)) (hCG : C <= G)
    (hdeg : forall p : Nat, Membership.mem P p -> nativePrimeVertexCycleDegree C p % 2 = 0)
    (hodd : C.card % 2 = 1) (ell : Nat) (hell : Nat.Prime ell) (hell2 : 2 < ell)
    (hlarge : forall p : Nat, Membership.mem P p -> p < ell)
    (hphase : nativeQuadraticPhaseEvent true ell) :
    Not (nativeVanishingProfileEvent G (fun _ => false) ell) := by
  intro hevent
  have hc := native_phase_profile_event_compatible P hP G hG (fun _ => false) true
    ell hell hell2 hlarge (And.intro hphase hevent)
  have hh := hc C ((native_eulerian_masks_mem_iff P G C).mpr (And.intro hCG hdeg))
  rw [native_constant_profile_coefficient, native_word_sign_power_parity] at hh
  norm_num [nativeWordSign, hodd] at hh

theorem native_graph_negative_phase_agreement_iff_zero (P : Finset Nat)
    (hP : forall p : Nat, Membership.mem P p -> Nat.Prime p)
    (G : Finset (Prod Nat Nat)) (hG : G <= nativePrimeVertexEdges P)
    (C : Finset (Prod Nat Nat)) (hCG : C <= G)
    (hdeg : forall p : Nat, Membership.mem P p -> nativePrimeVertexCycleDegree C p % 2 = 0)
    (hodd : C.card % 2 = 1) (ell : Nat) (hell : Nat.Prime ell) (hell2 : 2 < ell)
    (hlarge : forall p : Nat, Membership.mem P p -> p < ell)
    (hphase : nativeQuadraticPhaseEvent false ell) :
    nativeGraphAgreementEvent G ell <-> nativeGraphZeroTraceEvent G ell := by
  constructor
  . intro ha e he
    by_contra hn
    apply native_odd_mask_noncentral_negative_impossible P hP G hG C hCG hdeg hodd
      ell hell hell2 hlarge hphase
    intro f hf
    change Not (nativeTrace f.1 (f.2 - f.1) ell = 0)
    intro hz
    exact hn ((ha e he f hf).trans hz)
  . intro hz e he f hf
    exact (hz e he).trans (hz f hf).symm

theorem native_graph_negative_phase_weight_agreement_iff_central (P : Finset Nat)
    (hP : forall p : Nat, Membership.mem P p -> Nat.Prime p)
    (G : Finset (Prod Nat Nat)) (hG : G <= nativePrimeVertexEdges P)
    (C : Finset (Prod Nat Nat)) (hCG : C <= G)
    (hdeg : forall p : Nat, Membership.mem P p -> nativePrimeVertexCycleDegree C p % 2 = 0)
    (hodd : C.card % 2 = 1) (ell : Nat) (hell : Nat.Prime ell) (hell5 : 5 <= ell)
    (hlarge : forall p : Nat, Membership.mem P p -> p < ell)
    (hphase : nativeQuadraticPhaseEvent false ell) :
    nativeGraphWeightAgreementEvent G ell <->
      nativeCentralProfileEvent G (fun _ => false) ell := by
  have hw := native_graph_weight_agreement_iff P hP G hG ell hell hell5 hlarge
  have ht := native_graph_negative_phase_agreement_iff_zero P hP G hG C hCG hdeg hodd
    ell hell (by omega) hlarge hphase
  have hc := native_central_profile_iff_vanishing P hP G hG (fun _ => false)
    ell hell hell5 hlarge
  constructor
  . intro h
    exact hc.mpr (ht.mp (hw.mp h))
  . intro h
    exact hw.mpr (ht.mpr (hc.mp h))

theorem native_graph_mod_four_three_weight_agreement_iff_central (P : Finset Nat)
    (hP : forall p : Nat, Membership.mem P p -> Nat.Prime p)
    (G : Finset (Prod Nat Nat)) (hG : G <= nativePrimeVertexEdges P)
    (C : Finset (Prod Nat Nat)) (hCG : C <= G)
    (hdeg : forall p : Nat, Membership.mem P p -> nativePrimeVertexCycleDegree C p % 2 = 0)
    (hodd : C.card % 2 = 1) (ell : Nat) (hell : Nat.Prime ell) (hell5 : 5 <= ell)
    (hlarge : forall p : Nat, Membership.mem P p -> p < ell) (hmod : ell % 4 = 3) :
    nativeGraphWeightAgreementEvent G ell <->
      nativeCentralProfileEvent G (fun _ => false) ell := by
  apply native_graph_negative_phase_weight_agreement_iff_central P hP G hG C hCG hdeg
    hodd ell hell hell5 hlarge
  exact (native_phase_event_mod_four false ell hell (by omega)).mpr hmod

theorem native_graph_negative_phase_weight_event_iff (P : Finset Nat)
    (hP : forall p : Nat, Membership.mem P p -> Nat.Prime p)
    (G : Finset (Prod Nat Nat)) (hG : G <= nativePrimeVertexEdges P)
    (C : Finset (Prod Nat Nat)) (hCG : C <= G)
    (hdeg : forall p : Nat, Membership.mem P p -> nativePrimeVertexCycleDegree C p % 2 = 0)
    (hodd : C.card % 2 = 1) (ell : Nat) (hell : Nat.Prime ell) (hell5 : 5 <= ell)
    (hlarge : forall p : Nat, Membership.mem P p -> p < ell) :
    And (nativeQuadraticPhaseEvent false ell) (nativeGraphWeightAgreementEvent G ell) <->
      nativeCentralPhaseProfileEvent G (fun _ => false) false ell := by
  constructor
  . intro h
    exact And.intro h.1
      ((native_graph_negative_phase_weight_agreement_iff_central P hP G hG C hCG hdeg
        hodd ell hell hell5 hlarge h.1).mp h.2)
  . intro h
    exact And.intro h.1
      ((native_graph_negative_phase_weight_agreement_iff_central P hP G hG C hCG hdeg
        hodd ell hell hell5 hlarge h.1).mpr h.2)

theorem native_graph_positive_phase_agreement_noncentral (P : Finset Nat)
    (hP : forall p : Nat, Membership.mem P p -> Nat.Prime p)
    (G : Finset (Prod Nat Nat)) (hG : G <= nativePrimeVertexEdges P)
    (C : Finset (Prod Nat Nat)) (hCG : C <= G)
    (hdeg : forall p : Nat, Membership.mem P p -> nativePrimeVertexCycleDegree C p % 2 = 0)
    (hodd : C.card % 2 = 1) (ell : Nat) (hell : Nat.Prime ell) (hell5 : 5 <= ell)
    (hlarge : forall p : Nat, Membership.mem P p -> p < ell)
    (hphase : nativeQuadraticPhaseEvent true ell)
    (hagree : nativeGraphWeightAgreementEvent G ell) :
    nativeCentralProfileEvent G (fun _ => true) ell := by
  intro e he
  change Not (integerNativeWeight e.1 (e.2 - e.1) ell =
    ((ell : Real) - 1) / ((ell : Real) - 3))
  intro hec
  have hall : nativeCentralProfileEvent G (fun _ => false) ell := by
    intro f hf
    change integerNativeWeight f.1 (f.2 - f.1) ell =
      ((ell : Real) - 1) / ((ell : Real) - 3)
    exact (hagree f hf e he).trans hec
  have hzero := (native_central_profile_iff_vanishing P hP G hG (fun _ => false)
    ell hell hell5 hlarge).mp hall
  exact native_odd_mask_central_positive_impossible P hP G hG C hCG hdeg hodd ell hell
    (by omega) hlarge hphase hzero


def nativeGraphPhaseWeightAgreementMass (G : Finset (Prod Nat Nat))
    (b : Bool) (Y X : Nat) : Real :=
  ((Finset.Ico Y X).filter Nat.Prime).sum (fun ell =>
    (1 / (ell : Real)) *
      (if And (nativeQuadraticPhaseEvent b ell) (nativeGraphWeightAgreementEvent G ell)
        then 1 else 0))

theorem native_graph_negative_phase_weight_mass_eq (P : Finset Nat)
    (hP : forall p : Nat, Membership.mem P p -> Nat.Prime p)
    (G : Finset (Prod Nat Nat)) (hG : G <= nativePrimeVertexEdges P)
    (C : Finset (Prod Nat Nat)) (hCG : C <= G)
    (hdeg : forall p : Nat, Membership.mem P p -> nativePrimeVertexCycleDegree C p % 2 = 0)
    (hodd : C.card % 2 = 1) (Y X : Nat) (hY : 5 <= Y)
    (hPY : forall p : Nat, Membership.mem P p -> p < Y) :
    nativeGraphPhaseWeightAgreementMass G false Y X =
      nativeCentralPhaseProfileMass G (fun _ => false) false Y X := by
  unfold nativeGraphPhaseWeightAgreementMass nativeCentralPhaseProfileMass
  apply Finset.sum_congr rfl
  intro ell hell
  have hh := Finset.mem_filter.mp hell
  have hb := Finset.mem_Ico.mp hh.1
  have hlarge : forall p : Nat, Membership.mem P p -> p < ell :=
    fun p hp => (hPY p hp).trans_le hb.1
  have hi := native_graph_negative_phase_weight_event_iff P hP G hG C hCG hdeg hodd
    ell hh.2 (hY.trans hb.1) hlarge
  by_cases h : And (nativeQuadraticPhaseEvent false ell) (nativeGraphWeightAgreementEvent G ell)
  . rw [ite_eq_left h, ite_eq_left (hi.mp h)]
  . have hn : Not (nativeCentralPhaseProfileEvent G (fun _ => false) false ell) :=
      fun he => h (hi.mpr he)
    rw [ite_eq_right h, ite_eq_right hn]

theorem native_graph_negative_phase_weight_mass_eq_eventually (P : Finset Nat)
    (hP : forall p : Nat, Membership.mem P p -> Nat.Prime p)
    (G : Finset (Prod Nat Nat)) (hG : G <= nativePrimeVertexEdges P)
    (C : Finset (Prod Nat Nat)) (hCG : C <= G)
    (hdeg : forall p : Nat, Membership.mem P p -> nativePrimeVertexCycleDegree C p % 2 = 0)
    (hodd : C.card % 2 = 1) :
    Filter.Eventually (fun U : Nat =>
      nativeGraphPhaseWeightAgreementMass G false (preciseCore U + 1)
        (preciseCore U * preciseCore U + 1) =
      nativeCentralPhaseProfileMass G (fun _ => false) false (preciseCore U + 1)
        (preciseCore U * preciseCore U + 1)) atTop := by
  filter_upwards [native_graph_field_window_eventually P,
    precise_core_tendsto_atTop.eventually_ge_atTop 4] with U hU h4
  exact native_graph_negative_phase_weight_mass_eq P hP G hG C hCG hdeg hodd
    _ _ (by omega) hU.2

theorem native_graph_negative_phase_weight_joint_ratio_tendsto (P : Finset Nat)
    (hP : forall p : Nat, Membership.mem P p -> Nat.Prime p)
    (G : Finset (Prod Nat Nat)) (hG : G <= nativePrimeVertexEdges P)
    (C : Finset (Prod Nat Nat)) (hCG : C <= G)
    (hdeg : forall p : Nat, Membership.mem P p -> nativePrimeVertexCycleDegree C p % 2 = 0)
    (hodd : C.card % 2 = 1) :
    Tendsto (fun U : Nat =>
      nativeGraphPhaseWeightAgreementMass G false (preciseCore U + 1)
        (preciseCore U * preciseCore U + 1) /
        reciprocalBand (preciseCore U + 1) (preciseCore U * preciseCore U + 1))
      atTop (nhds ((1 / (2 : Real) ^ (G.card + 1)) * (nativeEulerianCount P G : Real))) := by
  have hlim := native_central_phase_profile_joint_ratio_tendsto P hP G hG
    (fun _ => false) false
  rw [ite_eq_left (native_central_negative_phase_compatible P G)] at hlim
  apply hlim.congr'
  filter_upwards [native_graph_negative_phase_weight_mass_eq_eventually P hP G hG C hCG
    hdeg hodd] with U hU
  rw [hU]

theorem native_graph_negative_phase_weight_conditional_ratio_tendsto (P : Finset Nat)
    (hP : forall p : Nat, Membership.mem P p -> Nat.Prime p)
    (G : Finset (Prod Nat Nat)) (hG : G <= nativePrimeVertexEdges P)
    (C : Finset (Prod Nat Nat)) (hCG : C <= G)
    (hdeg : forall p : Nat, Membership.mem P p -> nativePrimeVertexCycleDegree C p % 2 = 0)
    (hodd : C.card % 2 = 1) :
    Tendsto (fun U : Nat =>
      nativeGraphPhaseWeightAgreementMass G false (preciseCore U + 1)
        (preciseCore U * preciseCore U + 1) /
        nativeModuloFourBand false (preciseCore U + 1) (preciseCore U * preciseCore U + 1))
      atTop (nhds ((1 / (2 : Real) ^ G.card) * (nativeEulerianCount P G : Real))) := by
  have hlim := native_central_profile_mod_four_ratio_tendsto P hP G hG
    (fun _ => false) false
  rw [ite_eq_left (native_central_negative_phase_compatible P G)] at hlim
  apply hlim.congr'
  filter_upwards [native_graph_negative_phase_weight_mass_eq_eventually P hP G hG C hCG
    hdeg hodd] with U hU
  rw [hU]

theorem native_triangle_negative_phase_weight_conditional_ratio_tendsto (P : Finset Nat)
    (hP : forall p : Nat, Membership.mem P p -> Nat.Prime p) (p q r : Nat)
    (hp : Membership.mem P p) (hq : Membership.mem P q) (hr : Membership.mem P r)
    (hpq : p < q) (hqr : q < r) :
    Tendsto (fun U : Nat =>
      nativeGraphPhaseWeightAgreementMass {(p, q), (q, r), (p, r)} false (preciseCore U + 1)
        (preciseCore U * preciseCore U + 1) /
        nativeModuloFourBand false (preciseCore U + 1) (preciseCore U * preciseCore U + 1))
      atTop (nhds (1 / 4 : Real)) := by
  have hodd : ({(p, q), (q, r), (p, r)} : Finset (Prod Nat Nat)).card % 2 = 1 := by
    rw [native_phase_triangle_card p q r hpq hqr]
  have hlim := native_graph_negative_phase_weight_conditional_ratio_tendsto P hP
    {(p, q), (q, r), (p, r)} (native_phase_triangle_support P p q r hp hq hr hpq hqr)
    {(p, q), (q, r), (p, r)} (Finset.Subset.refl _)
    (fun x _ => native_phase_triangle_degrees_even p q r hpq hqr x) hodd
  rw [native_phase_triangle_eulerian_count P p q r hp hq hr hpq hqr,
    native_phase_triangle_card p q r hpq hqr] at hlim
  norm_num at hlim
  exact hlim

theorem native_graph_mod_four_three_agreement_realization_above (P : Finset Nat)
    (hP : forall p : Nat, Membership.mem P p -> Nat.Prime p)
    (G : Finset (Prod Nat Nat)) (hG : G <= nativePrimeVertexEdges P)
    (C : Finset (Prod Nat Nat)) (hCG : C <= G)
    (hdeg : forall p : Nat, Membership.mem P p -> nativePrimeVertexCycleDegree C p % 2 = 0)
    (hodd : C.card % 2 = 1) (B : Nat) :
    exists ell : Nat, And (Nat.Prime ell)
      (And (B < ell) (And (ell % 4 = 3) (nativeGraphWeightAgreementEvent G ell))) := by
  have hlim := native_graph_negative_phase_weight_joint_ratio_tendsto P hP G hG C hCG
    hdeg hodd
  have hN : (0 : Real) < (nativeEulerianCount P G : Real) := by
    exact_mod_cast native_eulerian_count_positive P G
  have hr : (0 : Real) <
      (1 / (2 : Real) ^ (G.card + 1)) * (nativeEulerianCount P G : Real) := by positivity
  have hp := hlim.eventually (Ioi_mem_nhds hr)
  have htail := precise_core_tendsto_atTop.eventually_ge_atTop (max (B + 1) 4)
  choose U hU using (hp.and htail).exists
  have hUB : B + 1 <= preciseCore U := (Nat.le_max_left (B + 1) 4).trans hU.2
  have hU4 : 4 <= preciseCore U := (Nat.le_max_right (B + 1) 4).trans hU.2
  by_contra hn
  have hno : forall ell : Nat, Nat.Prime ell -> B < ell -> 2 < ell ->
      Not (And (nativeQuadraticPhaseEvent false ell) (nativeGraphWeightAgreementEvent G ell)) := by
    intro ell hell hB hell2 he
    have hmod : ell % 4 = 3 :=
      (native_phase_event_mod_four false ell hell hell2).mp he.1
    exact hn (Exists.intro ell (And.intro hell
      (And.intro hB (And.intro hmod he.2))))
  have hz : nativeGraphPhaseWeightAgreementMass G false (preciseCore U + 1)
      (preciseCore U * preciseCore U + 1) = 0 := by
    unfold nativeGraphPhaseWeightAgreementMass
    apply Finset.sum_eq_zero
    intro ell hell
    have hh := Finset.mem_filter.mp hell
    have hb := Finset.mem_Ico.mp hh.1
    have hnell := hno ell hh.2 (by omega) (by omega)
    rw [ite_eq_right hnell, mul_zero]
  have hpos := hU.1
  rw [hz, zero_div] at hpos
  exact (lt_irrefl (0 : Real)) hpos

end PrimeFactorOscillations.FiniteFieldIntegerSignature

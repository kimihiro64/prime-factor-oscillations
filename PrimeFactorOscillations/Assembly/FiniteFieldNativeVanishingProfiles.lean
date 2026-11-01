/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Assembly.FiniteFieldNativeVanishingEvents

/-! # Complete universal native vanishing profile law

Every compatible profile has the same exact limiting frequency.
Incompatible profiles are eventually impossible. All prime labels are
arbitrary actual primes; no vertex/gap independence is assumed.
-/

set_option autoImplicit false
set_option Elab.async false

noncomputable section
namespace PrimeFactorOscillations.FiniteFieldIntegerSignature
open Filter IntegerQuadraticCharacter FiniteFieldIntegerWindowTransfer
open scoped Classical
attribute [local instance] Classical.propDecidable

theorem native_vanishing_compatible_rate (P : Finset Nat)
    (hP : forall p : Nat, Membership.mem P p -> Nat.Prime p)
    (G : Finset (Prod Nat Nat)) (hG : G <= nativePrimeVertexEdges P)
    (a : Prod Nat Nat -> Bool) (hc : nativeVanishingProfileCompatible P G a) :
    nativeVanishingProfileRate G a =
      (1 / (2 : Real) ^ G.card) * (nativeEvenCycleCount P G : Real) := by
  let f := fun C : Finset (Prod Nat Nat) => nativeVanishingProfileCoefficient C a *
    numeratorPrincipalIndicator (nativeSignedRowProduct C C)
  have hsub : nativeEvenCycleMasks P G <= G.powerset := Finset.filter_subset _ _
  have ho : forall C : Finset (Prod Nat Nat), Membership.mem G.powerset C ->
      Not (Membership.mem (nativeEvenCycleMasks P G) C) -> f C = 0 := by
    intro C hC hn
    change nativeVanishingProfileCoefficient C a *
      numeratorPrincipalIndicator (nativeSignedRowProduct C C) = 0
    rw [native_graph_diagonal_indicator_zero_outside_cycles P hP G C hG
      (Finset.mem_powerset.mp hC) hn, mul_zero]
  have hm : (nativeEvenCycleMasks P G).sum f = (nativeEvenCycleCount P G : Real) := by
    calc
      _ = (nativeEvenCycleMasks P G).sum (fun _ => (1 : Real)) := by
        apply Finset.sum_congr rfl
        intro C hC
        change nativeVanishingProfileCoefficient C a *
          numeratorPrincipalIndicator (nativeSignedRowProduct C C) = 1
        rw [hc C hC, native_graph_cycle_indicator_eq_one P hP G hG C hC, mul_one]
      _ = _ := by simp [nativeEvenCycleCount]
  have hall : G.powerset.sum f = (nativeEvenCycleCount P G : Real) :=
    (Finset.sum_subset hsub ho).symm.trans hm
  change (1 / (2 : Real) ^ G.card) * G.powerset.sum f =
    (1 / (2 : Real) ^ G.card) * (nativeEvenCycleCount P G : Real)
  rw [hall]

theorem native_vanishing_incompatible_rate (P : Finset Nat)
    (hP : forall p : Nat, Membership.mem P p -> Nat.Prime p)
    (G : Finset (Prod Nat Nat)) (hG : G <= nativePrimeVertexEdges P)
    (a : Prod Nat Nat -> Bool) (hn : Not (nativeVanishingProfileCompatible P G a)) :
    nativeVanishingProfileRate G a = 0 := by
  have hlim := native_vanishing_profile_general_ratio_tendsto P hP G hG a
  have hz : Tendsto (fun U : Nat =>
      nativeVanishingProfileMass G a (preciseCore U + 1)
        (preciseCore U * preciseCore U + 1) /
        reciprocalBand (preciseCore U + 1) (preciseCore U * preciseCore U + 1))
      atTop (nhds (0 : Real)) := by
    apply tendsto_const_nhds.congr'
    filter_upwards [native_vanishing_incompatible_mass_zero_eventually P hP G hG a hn]
      with U hU
    rw [hU, zero_div]
  exact tendsto_nhds_unique hlim hz

theorem native_vanishing_profile_rate_eq (P : Finset Nat)
    (hP : forall p : Nat, Membership.mem P p -> Nat.Prime p)
    (G : Finset (Prod Nat Nat)) (hG : G <= nativePrimeVertexEdges P)
    (a : Prod Nat Nat -> Bool) :
    nativeVanishingProfileRate G a =
      if nativeVanishingProfileCompatible P G a then
        (1 / (2 : Real) ^ G.card) * (nativeEvenCycleCount P G : Real) else 0 := by
  by_cases hc : nativeVanishingProfileCompatible P G a
  . rw [ite_eq_left hc]
    exact native_vanishing_compatible_rate P hP G hG a hc
  . rw [ite_eq_right hc]
    exact native_vanishing_incompatible_rate P hP G hG a hc

theorem native_vanishing_profile_ratio_tendsto (P : Finset Nat)
    (hP : forall p : Nat, Membership.mem P p -> Nat.Prime p)
    (G : Finset (Prod Nat Nat)) (hG : G <= nativePrimeVertexEdges P)
    (a : Prod Nat Nat -> Bool) :
    Tendsto (fun U : Nat =>
      nativeVanishingProfileMass G a (preciseCore U + 1)
        (preciseCore U * preciseCore U + 1) /
        reciprocalBand (preciseCore U + 1) (preciseCore U * preciseCore U + 1))
      atTop (nhds (if nativeVanishingProfileCompatible P G a then
        (1 / (2 : Real) ^ G.card) * (nativeEvenCycleCount P G : Real) else 0)) := by
  rw [<- native_vanishing_profile_rate_eq P hP G hG a]
  exact native_vanishing_profile_general_ratio_tendsto P hP G hG a

theorem native_vanishing_incompatible_eventually_absent (P : Finset Nat)
    (hP : forall p : Nat, Membership.mem P p -> Nat.Prime p)
    (G : Finset (Prod Nat Nat)) (hG : G <= nativePrimeVertexEdges P)
    (a : Prod Nat Nat -> Bool) (hn : Not (nativeVanishingProfileCompatible P G a)) :
    exists Y : Nat, forall ell : Nat, Y <= ell -> Nat.Prime ell ->
      Not (nativeVanishingProfileEvent G a ell) := by
  choose K hK using P.finite_toSet.bddAbove
  refine Exists.intro (max K 3 + 1) ?_
  intro ell hle hell he
  apply hn
  apply native_vanishing_profile_event_compatible P hP G hG a ell hell (by omega)
  . intro p hp
    have hpK := hK hp
    have hKK := Nat.le_max_left K 3
    omega
  . exact he

theorem native_vanishing_compatible_realization_above (P : Finset Nat)
    (hP : forall p : Nat, Membership.mem P p -> Nat.Prime p)
    (G : Finset (Prod Nat Nat)) (hG : G <= nativePrimeVertexEdges P)
    (a : Prod Nat Nat -> Bool) (hc : nativeVanishingProfileCompatible P G a)
    (B : Nat) :
    exists ell : Nat, And (Nat.Prime ell)
      (And (B < ell) (nativeVanishingProfileEvent G a ell)) := by
  have hlim := native_vanishing_profile_ratio_tendsto P hP G hG a
  rw [ite_eq_left hc] at hlim
  have hN : (0 : Real) < (nativeEvenCycleCount P G : Real) := by
    exact_mod_cast native_even_cycle_count_positive P G
  have hr : (0 : Real) <
      (1 / (2 : Real) ^ G.card) * (nativeEvenCycleCount P G : Real) := by positivity
  have hp := hlim.eventually (Ioi_mem_nhds hr)
  have htail := precise_core_tendsto_atTop.eventually_ge_atTop (B + 1)
  have hboth := hp.and htail
  choose U hU using hboth.exists
  by_contra hn
  have hno : forall ell : Nat, Nat.Prime ell -> B < ell ->
      Not (nativeVanishingProfileEvent G a ell) := by
    intro ell hell hB he
    exact hn (Exists.intro ell (And.intro hell (And.intro hB he)))
  have hz : nativeVanishingProfileMass G a (preciseCore U + 1)
      (preciseCore U * preciseCore U + 1) = 0 := by
    unfold nativeVanishingProfileMass
    apply Finset.sum_eq_zero
    intro ell hell
    have hh := Finset.mem_filter.mp hell
    have hb := Finset.mem_Ico.mp hh.1
    have hnell := hno ell hh.2 (by omega)
    rw [ite_eq_right hnell, mul_zero]
  have hpos := hU.1
  rw [hz, zero_div] at hpos
  exact (lt_irrefl (0 : Real)) hpos

theorem native_vanishing_profile_recurrence_iff (P : Finset Nat)
    (hP : forall p : Nat, Membership.mem P p -> Nat.Prime p)
    (G : Finset (Prod Nat Nat)) (hG : G <= nativePrimeVertexEdges P)
    (a : Prod Nat Nat -> Bool) :
    (forall B : Nat, exists ell : Nat, And (Nat.Prime ell)
      (And (B < ell) (nativeVanishingProfileEvent G a ell))) <->
      nativeVanishingProfileCompatible P G a := by
  constructor
  . intro hr
    by_contra hn
    choose Y hY using native_vanishing_incompatible_eventually_absent P hP G hG a hn
    choose ell hell using hr Y
    exact hY ell (Nat.le_of_lt hell.2.1) hell.1 hell.2.2
  . intro hc B
    exact native_vanishing_compatible_realization_above P hP G hG a hc B

def nativeCentralProfileEvent (G : Finset (Prod Nat Nat))
    (a : Prod Nat Nat -> Bool) (ell : Nat) : Prop :=
  forall e : Prod Nat Nat, Membership.mem G e ->
    if a e then Not (integerNativeWeight e.1 (e.2 - e.1) ell =
      ((ell : Real) - 1) / ((ell : Real) - 3))
    else integerNativeWeight e.1 (e.2 - e.1) ell =
      ((ell : Real) - 1) / ((ell : Real) - 3)

def nativeCentralProfileMass (G : Finset (Prod Nat Nat))
    (a : Prod Nat Nat -> Bool) (Y X : Nat) : Real :=
  ((Finset.Ico Y X).filter Nat.Prime).sum (fun ell =>
    (1 / (ell : Real)) * (if nativeCentralProfileEvent G a ell then 1 else 0))

theorem native_central_profile_iff_vanishing (P : Finset Nat)
    (hP : forall p : Nat, Membership.mem P p -> Nat.Prime p)
    (G : Finset (Prod Nat Nat)) (hG : G <= nativePrimeVertexEdges P)
    (a : Prod Nat Nat -> Bool) (ell : Nat) (hell : Nat.Prime ell) (hell5 : 5 <= ell)
    (hlarge : forall p : Nat, Membership.mem P p -> p < ell) :
    nativeCentralProfileEvent G a ell <-> nativeVanishingProfileEvent G a ell := by
  have hs : forall e : Prod Nat Nat, Membership.mem G e ->
      ((if a e then Not (integerNativeWeight e.1 (e.2 - e.1) ell =
        ((ell : Real) - 1) / ((ell : Real) - 3))
       else integerNativeWeight e.1 (e.2 - e.1) ell =
        ((ell : Real) - 1) / ((ell : Real) - 3)) <->
      (if a e then Not (nativeTrace e.1 (e.2 - e.1) ell = 0)
       else nativeTrace e.1 (e.2 - e.1) ell = 0)) := by
    intro e he
    have hedge : ({e} : Finset (Prod Nat Nat)) <= nativePrimeVertexEdges P := by
      intro f hf
      have hfe := Finset.mem_singleton.mp hf
      rw [hfe]
      exact hG he
    have hz : integerNativeWeight e.1 (e.2 - e.1) ell =
        ((ell : Real) - 1) / ((ell : Real) - 3) <->
        nativeTrace e.1 (e.2 - e.1) ell = 0 := by
      simpa only [nativeGraphCentralWeightEvent, nativeGraphZeroTraceEvent,
        Finset.mem_singleton, forall_eq] using
        native_graph_central_weight_iff_zero P hP {e} hedge ell hell hell5 hlarge
    cases hbit : a e with
    | false => exact hz
    | true => exact not_congr hz
  constructor
  . intro h e he
    exact (hs e he).mp (h e he)
  . intro h e he
    exact (hs e he).mpr (h e he)

theorem native_central_profile_mass_eq (P : Finset Nat)
    (hP : forall p : Nat, Membership.mem P p -> Nat.Prime p)
    (G : Finset (Prod Nat Nat)) (hG : G <= nativePrimeVertexEdges P)
    (a : Prod Nat Nat -> Bool) (Y X : Nat) (hY : 5 <= Y)
    (hPY : forall p : Nat, Membership.mem P p -> p < Y) :
    nativeCentralProfileMass G a Y X = nativeVanishingProfileMass G a Y X := by
  unfold nativeCentralProfileMass nativeVanishingProfileMass
  apply Finset.sum_congr rfl
  intro ell hell
  have hh := Finset.mem_filter.mp hell
  have hb := Finset.mem_Ico.mp hh.1
  have hlarge : forall p : Nat, Membership.mem P p -> p < ell :=
    fun p hp => (hPY p hp).trans_le hb.1
  have hi := native_central_profile_iff_vanishing P hP G hG a ell hh.2
    (hY.trans hb.1) hlarge
  by_cases h : nativeCentralProfileEvent G a ell
  . rw [ite_eq_left h, ite_eq_left (hi.mp h)]
  . have hn : Not (nativeVanishingProfileEvent G a ell) := fun ht => h (hi.mpr ht)
    rw [ite_eq_right h, ite_eq_right hn]

theorem native_central_profile_mass_eq_eventually (P : Finset Nat)
    (hP : forall p : Nat, Membership.mem P p -> Nat.Prime p)
    (G : Finset (Prod Nat Nat)) (hG : G <= nativePrimeVertexEdges P)
    (a : Prod Nat Nat -> Bool) :
    Filter.Eventually (fun U : Nat =>
      nativeCentralProfileMass G a (preciseCore U + 1)
        (preciseCore U * preciseCore U + 1) =
      nativeVanishingProfileMass G a (preciseCore U + 1)
        (preciseCore U * preciseCore U + 1)) atTop := by
  filter_upwards [native_graph_field_window_eventually P,
    precise_core_tendsto_atTop.eventually_ge_atTop 4] with U hU h4
  exact native_central_profile_mass_eq P hP G hG a _ _ (by omega) hU.2

theorem native_central_profile_ratio_tendsto (P : Finset Nat)
    (hP : forall p : Nat, Membership.mem P p -> Nat.Prime p)
    (G : Finset (Prod Nat Nat)) (hG : G <= nativePrimeVertexEdges P)
    (a : Prod Nat Nat -> Bool) :
    Tendsto (fun U : Nat =>
      nativeCentralProfileMass G a (preciseCore U + 1)
        (preciseCore U * preciseCore U + 1) /
        reciprocalBand (preciseCore U + 1) (preciseCore U * preciseCore U + 1))
      atTop (nhds (if nativeVanishingProfileCompatible P G a then
        (1 / (2 : Real) ^ G.card) * (nativeEvenCycleCount P G : Real) else 0)) := by
  apply (native_vanishing_profile_ratio_tendsto P hP G hG a).congr'
  filter_upwards [native_central_profile_mass_eq_eventually P hP G hG a] with U hU
  rw [hU]

theorem native_small_vanishing_profile_compatible (P : Finset Nat)
    (G : Finset (Prod Nat Nat)) (hG : G <= nativePrimeVertexEdges P)
    (hc : G.card <= 3) (a : Prod Nat Nat -> Bool) :
    nativeVanishingProfileCompatible P G a := by
  intro C hC
  rw [native_even_cycle_masks_small P G hG hc, Finset.mem_singleton] at hC
  rw [hC]
  simp [nativeVanishingProfileCoefficient]

theorem native_small_central_profile_ratio_tendsto (P : Finset Nat)
    (hP : forall p : Nat, Membership.mem P p -> Nat.Prime p)
    (G : Finset (Prod Nat Nat)) (hG : G <= nativePrimeVertexEdges P)
    (hc : G.card <= 3) (a : Prod Nat Nat -> Bool) :
    Tendsto (fun U : Nat =>
      nativeCentralProfileMass G a (preciseCore U + 1)
        (preciseCore U * preciseCore U + 1) /
        reciprocalBand (preciseCore U + 1) (preciseCore U * preciseCore U + 1))
      atTop (nhds (1 / (2 : Real) ^ G.card)) := by
  have h := native_central_profile_ratio_tendsto P hP G hG a
  rw [ite_eq_left (native_small_vanishing_profile_compatible P G hG hc a),
    native_even_cycle_count_small P G hG hc, Nat.cast_one, mul_one] at h
  exact h

theorem native_four_cycle_vanishing_profile_compatible_iff (P : Finset Nat)
    (p q r s : Nat) (hp : Membership.mem P p) (hq : Membership.mem P q)
    (hr : Membership.mem P r) (hs : Membership.mem P s)
    (hpq : p < q) (hqr : q < r) (hrs : r < s)
    (a : Prod Nat Nat -> Bool) :
    nativeVanishingProfileCompatible P (nativePrimeFourCycle p q r s) a <->
      nativeVanishingProfileCoefficient (nativePrimeFourCycle p q r s) a = 1 := by
  have hm := native_even_cycle_masks_four_cycle P p q r s hp hq hr hs hpq hqr hrs
  constructor
  . intro hc
    apply hc
    rw [hm]
    simp
  . intro hc C hC
    rw [hm, Finset.mem_insert, Finset.mem_singleton] at hC
    rcases hC with h | h
    . rw [h]
      simp [nativeVanishingProfileCoefficient]
    . rw [h]
      exact hc

theorem native_four_cycle_central_profile_ratio_tendsto (P : Finset Nat)
    (hP : forall x : Nat, Membership.mem P x -> Nat.Prime x)
    (p q r s : Nat) (hp : Membership.mem P p) (hq : Membership.mem P q)
    (hr : Membership.mem P r) (hs : Membership.mem P s)
    (hpq : p < q) (hqr : q < r) (hrs : r < s)
    (a : Prod Nat Nat -> Bool) :
    Tendsto (fun U : Nat =>
      nativeCentralProfileMass (nativePrimeFourCycle p q r s) a
        (preciseCore U + 1) (preciseCore U * preciseCore U + 1) /
        reciprocalBand (preciseCore U + 1) (preciseCore U * preciseCore U + 1))
      atTop (nhds (if nativeVanishingProfileCoefficient
        (nativePrimeFourCycle p q r s) a = 1 then (1 / 8 : Real) else 0)) := by
  have h := native_central_profile_ratio_tendsto P hP _
    (native_four_cycle_support P p q r s hp hq hr hs hpq hqr hrs) a
  have hi := native_four_cycle_vanishing_profile_compatible_iff P p q r s
    hp hq hr hs hpq hqr hrs a
  by_cases hc : nativeVanishingProfileCoefficient (nativePrimeFourCycle p q r s) a = 1
  . rw [ite_eq_left (hi.mpr hc),
      native_even_cycle_count_four_cycle P p q r s hp hq hr hs hpq hqr hrs,
      native_four_cycle_card p q r s hpq hqr hrs] at h
    norm_num at h
    simpa only [ite_eq_left hc] using h
  . have hn : Not (nativeVanishingProfileCompatible P (nativePrimeFourCycle p q r s) a) :=
      fun hh => hc (hi.mp hh)
    rw [ite_eq_right hn] at h
    simpa only [ite_eq_right hc] using h

end PrimeFactorOscillations.FiniteFieldIntegerSignature

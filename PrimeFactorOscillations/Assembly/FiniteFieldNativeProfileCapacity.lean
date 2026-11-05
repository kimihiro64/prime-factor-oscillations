/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Assembly.FiniteFieldNativeProfileCode
import PrimeFactorOscillations.Helpers.NativePrimeTriangleFan

/-! # Sharp capacity of independent actual native centrality statuses -/

set_option autoImplicit false
set_option Elab.async false

noncomputable section
namespace PrimeFactorOscillations.FiniteFieldIntegerSignature
open Filter IntegerQuadraticCharacter FiniteFieldIntegerCharacter
open FiniteFieldIntegerWindowTransfer
open scoped Classical
attribute [local instance] Classical.propDecidable

def nativeFairCentralProfileLaw (G : Finset (Prod Nat Nat)) : Prop :=
  forall a : Prod Nat Nat -> Bool,
    Tendsto (fun U : Nat =>
      nativeCentralProfileMass G a (preciseCore U + 1) (preciseCore U * preciseCore U + 1) /
        reciprocalBand (preciseCore U + 1) (preciseCore U * preciseCore U + 1))
      atTop (nhds (1 / (2 : Real) ^ G.card))

def nativeCentralityCapacity (n : Nat) : Nat :=
  if n <= 1 then 0 else if n = 2 then 1 else n

theorem native_fair_profile_realization_above (G : Finset (Prod Nat Nat))
    (hfair : nativeFairCentralProfileLaw G) (a : Prod Nat Nat -> Bool) (B : Nat) :
    Exists (fun ell : Nat => And (Nat.Prime ell)
      (And (B < ell) (nativeCentralProfileEvent G a ell))) := by
  have hlim := hfair a
  have hr : (0 : Real) < 1 / (2 : Real) ^ G.card := by positivity
  have hp := hlim.eventually (Ioi_mem_nhds hr)
  have htail := precise_core_tendsto_atTop.eventually_ge_atTop (B + 1)
  choose U hU using (hp.and htail).exists
  by_contra hn
  have hz : nativeCentralProfileMass G a (preciseCore U + 1)
      (preciseCore U * preciseCore U + 1) = 0 := by
    unfold nativeCentralProfileMass
    apply Finset.sum_eq_zero
    intro ell hell
    have hh := Finset.mem_filter.mp hell
    have hb := Finset.mem_Ico.mp hh.1
    have hnell : Not (nativeCentralProfileEvent G a ell) := by
      intro he
      exact hn (Exists.intro ell (And.intro hh.2 (And.intro (by omega) he)))
    rw [ite_eq_right hnell, mul_zero]
  have hpos := hU.1
  rw [hz, zero_div] at hpos
  exact (lt_irrefl (0 : Real)) hpos

theorem native_fair_profile_card_le_vertices (P : Finset Nat)
    (hP : forall p : Nat, Membership.mem P p -> Nat.Prime p)
    (G : Finset (Prod Nat Nat)) (hG : G <= nativePrimeVertexEdges P)
    (hfair : nativeFairCentralProfileLaw G) : G.card <= P.card := by
  by_cases hne : P.Nonempty
  . choose r hr using hne
    choose K hK using P.finite_toSet.bddAbove
    let B := max K 5
    have hPB : forall p : Nat, Membership.mem P p -> p <= B :=
      fun p hp => (hK hp).trans (Nat.le_max_left K 5)
    have hB5 : 5 <= B := Nat.le_max_right K 5
    have heq : nativeRealizableProfileSets G B = G.powerset := by
      unfold nativeRealizableProfileSets
      apply Finset.Subset.antisymm (Finset.filter_subset _ _)
      intro T hT
      apply Finset.mem_filter.mpr
      exact And.intro hT
        (native_fair_profile_realization_above G hfair
          (fun e => decide (Membership.mem T e)) B)
    have hc := native_realizable_profiles_card_le P hP r hr G hG B hB5 hPB
    rw [heq, Finset.card_powerset] at hc
    exact (Nat.pow_le_pow_iff_right (by decide : 1 < 2)).mp hc
  . have hempty : G = {} := by
      apply Finset.Subset.antisymm _ (Finset.empty_subset G)
      intro e he
      have hh := (native_gap_edges_mem_iff P e).mp (hG he)
      exact False.elim (hne (Exists.intro e.1 hh.1))
    rw [hempty]
    simp

theorem native_graph_card_zero_of_vertex_card_le_one (P : Finset Nat)
    (G : Finset (Prod Nat Nat)) (hG : G <= nativePrimeVertexEdges P) (hc : P.card <= 1) :
    G.card = 0 := by
  have hempty : G = {} := by
    apply Finset.Subset.antisymm _ (Finset.empty_subset G)
    intro e he
    have hh := (native_gap_edges_mem_iff P e).mp (hG he)
    have heq := (Finset.card_le_one.mp hc) e.1 hh.1 e.2 hh.2.1
    exact False.elim (hh.2.2.ne heq)
  rw [hempty]
  simp

theorem native_graph_card_le_one_of_two_vertices (P : Finset Nat)
    (G : Finset (Prod Nat Nat)) (hG : G <= nativePrimeVertexEdges P) (hc : P.card = 2) :
    G.card <= 1 := by
  choose a b h using Finset.card_eq_two.mp hc
  apply Finset.card_le_one.mpr
  intro e he f hf
  have hE := (native_gap_edges_mem_iff P e).mp (hG he)
  have hF := (native_gap_edges_mem_iff P f).mp (hG hf)
  simp only [h.2, Finset.mem_insert, Finset.mem_singleton] at hE hF
  apply Prod.ext <;> omega

theorem native_fair_profile_card_le_capacity (P : Finset Nat)
    (hP : forall p : Nat, Membership.mem P p -> Nat.Prime p)
    (G : Finset (Prod Nat Nat)) (hG : G <= nativePrimeVertexEdges P)
    (hfair : nativeFairCentralProfileLaw G) :
    G.card <= nativeCentralityCapacity P.card := by
  unfold nativeCentralityCapacity
  split_ifs with hsmall htwo
  . rw [native_graph_card_zero_of_vertex_card_le_one P G hG hsmall]
  . exact native_graph_card_le_one_of_two_vertices P G hG htwo
  . exact native_fair_profile_card_le_vertices P hP G hG hfair

theorem native_triangle_fan_fair_profile_law (P : Finset Nat)
    (hP : forall p : Nat, Membership.mem P p -> Nat.Prime p)
    (p q r : Nat) (hp : Membership.mem P p) (hq : Membership.mem P q) (hr : Membership.mem P r)
    (hmin : forall x : Nat, Membership.mem P x -> p <= x) (hpq : p < q) (hqr : q < r) :
    nativeFairCentralProfileLaw (nativePrimeTriangleFan P p q r) := by
  intro a
  have hG := native_triangle_fan_support P p q r hp hq hr hmin hqr
  have hc : nativeVanishingProfileCompatible P (nativePrimeTriangleFan P p q r) a := by
    intro C hC
    rw [native_triangle_fan_even_cycle_masks P p q r hp hq hr hmin hpq hqr] at hC
    have he := Finset.mem_singleton.mp hC
    rw [he]
    simp [nativeVanishingProfileCoefficient]
  have hlim := native_central_profile_ratio_tendsto P hP (nativePrimeTriangleFan P p q r) hG a
  rw [ite_eq_left hc, native_triangle_fan_even_cycle_count P p q r hp hq hr hmin hpq hqr,
    Nat.cast_one, mul_one] at hlim
  exact hlim

theorem native_exists_full_vertex_fair_profile_graph (P : Finset Nat)
    (hP : forall p : Nat, Membership.mem P p -> Nat.Prime p) (hc : 3 <= P.card) :
    Exists (fun G : Finset (Prod Nat Nat) => And (G <= nativePrimeVertexEdges P)
      (And (G.card = P.card) (nativeFairCentralProfileLaw G))) := by
  have hPn : P.Nonempty := Finset.card_pos.mp (by omega)
  let p := P.min' hPn
  have hp : Membership.mem P p := Finset.min'_mem P hPn
  let Q := P.erase p
  have hQc : 2 <= Q.card := by
    dsimp only [Q]
    rw [Finset.card_erase_of_mem hp]
    omega
  have hQn : Q.Nonempty := Finset.card_pos.mp (by omega)
  let q := Q.min' hQn
  have hqQ : Membership.mem Q q := Finset.min'_mem Q hQn
  have hq : Membership.mem P q := (Finset.mem_erase.mp hqQ).2
  have hqp : Not (q = p) := (Finset.mem_erase.mp hqQ).1
  have hpq0 : p <= q := Finset.min'_le P q hq
  have hpq : p < q := by omega
  let R := Q.erase q
  have hRc : 0 < R.card := by
    dsimp only [R]
    rw [Finset.card_erase_of_mem hqQ]
    omega
  have hRn : R.Nonempty := Finset.card_pos.mp hRc
  let r := R.min' hRn
  have hrR : Membership.mem R r := Finset.min'_mem R hRn
  have hrQ : Membership.mem Q r := (Finset.mem_erase.mp hrR).2
  have hr : Membership.mem P r := (Finset.mem_erase.mp hrQ).2
  have hrq : Not (r = q) := (Finset.mem_erase.mp hrR).1
  have hqr0 : q <= r := Finset.min'_le Q r hrQ
  have hqr : q < r := by omega
  have hmin : forall x : Nat, Membership.mem P x -> p <= x :=
    fun x hx => Finset.min'_le P x hx
  refine Exists.intro (nativePrimeTriangleFan P p q r)
    (And.intro (native_triangle_fan_support P p q r hp hq hr hmin hqr) (And.intro ?_ ?_))
  . exact native_triangle_fan_card P p q r hp hpq
  . exact native_triangle_fan_fair_profile_law P hP p q r hp hq hr hmin hpq hqr

theorem native_exists_capacity_attaining_profile_graph (P : Finset Nat)
    (hP : forall p : Nat, Membership.mem P p -> Nat.Prime p) :
    Exists (fun G : Finset (Prod Nat Nat) => And (G <= nativePrimeVertexEdges P)
      (And (G.card = nativeCentralityCapacity P.card) (nativeFairCentralProfileLaw G))) := by
  by_cases hsmall : P.card <= 1
  . refine Exists.intro {} (And.intro (Finset.empty_subset _) (And.intro ?_ ?_))
    . simp [nativeCentralityCapacity, hsmall]
    . intro a
      exact native_small_central_profile_ratio_tendsto P hP {} (Finset.empty_subset _)
        (by simp) a
  . by_cases htwo : P.card = 2
    . choose a b h using Finset.card_eq_two.mp htwo
      have ha : Membership.mem P a := by rw [h.2]; simp
      have hb : Membership.mem P b := by rw [h.2]; simp
      rcases lt_or_gt_of_ne h.1 with hlt | hlt
      . have hG : ({(a, b)} : Finset (Prod Nat Nat)) <= nativePrimeVertexEdges P := by
          intro e he
          rw [Finset.mem_singleton.mp he]
          exact (native_gap_edges_mem_iff P (a, b)).mpr (And.intro ha (And.intro hb hlt))
        refine Exists.intro {(a, b)} (And.intro hG (And.intro ?_ ?_))
        . norm_num [nativeCentralityCapacity, htwo]
        . intro alpha
          exact native_small_central_profile_ratio_tendsto P hP {(a, b)} hG (by simp) alpha
      . have hG : ({(b, a)} : Finset (Prod Nat Nat)) <= nativePrimeVertexEdges P := by
          intro e he
          rw [Finset.mem_singleton.mp he]
          exact (native_gap_edges_mem_iff P (b, a)).mpr (And.intro hb (And.intro ha hlt))
        refine Exists.intro {(b, a)} (And.intro hG (And.intro ?_ ?_))
        . norm_num [nativeCentralityCapacity, htwo]
        . intro alpha
          exact native_small_central_profile_ratio_tendsto P hP {(b, a)} hG (by simp) alpha
    . have hthree : 3 <= P.card := by omega
      choose G hG using native_exists_full_vertex_fair_profile_graph P hP hthree
      refine Exists.intro G (And.intro hG.1 (And.intro ?_ hG.2.2))
      simpa only [nativeCentralityCapacity, hsmall, htwo, ite_false] using hG.2.1

theorem native_sharp_centrality_capacity (P : Finset Nat)
    (hP : forall p : Nat, Membership.mem P p -> Nat.Prime p) :
    And
      (forall G : Finset (Prod Nat Nat), G <= nativePrimeVertexEdges P ->
        nativeFairCentralProfileLaw G -> G.card <= nativeCentralityCapacity P.card)
      (Exists (fun G : Finset (Prod Nat Nat) => And (G <= nativePrimeVertexEdges P)
        (And (G.card = nativeCentralityCapacity P.card) (nativeFairCentralProfileLaw G)))) := by
  exact And.intro (fun G hG hfair => native_fair_profile_card_le_capacity P hP G hG hfair)
    (native_exists_capacity_attaining_profile_graph P hP)

end PrimeFactorOscillations.FiniteFieldIntegerSignature

/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Assembly.FiniteFieldNativeFourCycleLaw
import PrimeFactorOscillations.Assembly.FiniteFieldNativeGraphCoincidenceLaw

/-! # Sharp graph coincidence for the actual native outputs

Every graph is fixed before the field-prime limit. The affine trace readout
preserves equality exactly; the small graph values are symbolic, uniform
specializations rather than experiments at selected prime labels.
-/

set_option autoImplicit false
set_option Elab.async false

noncomputable section
namespace PrimeFactorOscillations.FiniteFieldIntegerSignature
open Filter IntegerQuadraticCharacter FiniteFieldIntegerWindowTransfer
open scoped Classical
attribute [local instance] Classical.propDecidable

def nativeGraphWeightAgreementEvent (G : Finset (Prod Nat Nat)) (ell : Nat) : Prop :=
  forall e : Prod Nat Nat, Membership.mem G e ->
    forall f : Prod Nat Nat, Membership.mem G f ->
      integerNativeWeight e.1 (e.2 - e.1) ell =
        integerNativeWeight f.1 (f.2 - f.1) ell

def nativeGraphWeightAgreementMass (G : Finset (Prod Nat Nat)) (Y X : Nat) : Real :=
  ((Finset.Ico Y X).filter Nat.Prime).sum (fun ell =>
    (1 / (ell : Real)) * (if nativeGraphWeightAgreementEvent G ell then 1 else 0))

theorem native_graph_weight_agreement_iff (P : Finset Nat)
    (hP : forall p : Nat, Membership.mem P p -> Nat.Prime p)
    (G : Finset (Prod Nat Nat)) (hG : G <= nativePrimeVertexEdges P)
    (ell : Nat) (hell : Nat.Prime ell) (hell5 : 5 <= ell)
    (hlarge : forall p : Nat, Membership.mem P p -> p < ell) :
    nativeGraphWeightAgreementEvent G ell <-> nativeGraphAgreementEvent G ell := by
  let : Fact (Nat.Prime ell) := Fact.mk hell
  have ha : forall e : Prod Nat Nat, Membership.mem G e ->
      ((ell : Real) - 3) * integerNativeWeight e.1 (e.2 - e.1) ell -
        ((ell : Real) - 1) = nativeTrace e.1 (e.2 - e.1) ell := by
    intro e he
    have hm := (native_gap_edges_mem_iff P e).mp (hG he)
    apply native_weight_large_prime_trace e.1 (e.2 - e.1) ell
      (hP e.1 hm.1).pos hell5
    rw [Nat.add_sub_of_le hm.2.2.le]
    exact hlarge e.2 hm.2.1
  have hR : (5 : Real) <= (ell : Real) := by exact_mod_cast hell5
  have hNZ : Not ((ell : Real) - 3 = 0) := by linarith only [hR]
  constructor
  . intro hw e he f hf
    rw [<- ha e he, <- ha f hf, hw e he f hf]
  . intro ht e he f hf
    have heq := ha e he
    have hfq := ha f hf
    have heqt := ht e he f hf
    have hz : ((ell : Real) - 3) *
        (integerNativeWeight e.1 (e.2 - e.1) ell -
          integerNativeWeight f.1 (f.2 - f.1) ell) = 0 := by
      nlinarith only [heq, hfq, heqt]
    rcases mul_eq_zero.mp hz with h | h
    . exact False.elim (hNZ h)
    . exact sub_eq_zero.mp h

theorem native_graph_weight_mass_eq (P : Finset Nat)
    (hP : forall p : Nat, Membership.mem P p -> Nat.Prime p)
    (G : Finset (Prod Nat Nat)) (hG : G <= nativePrimeVertexEdges P)
    (Y X : Nat) (hY : 5 <= Y)
    (hPY : forall p : Nat, Membership.mem P p -> p < Y) :
    nativeGraphWeightAgreementMass G Y X = nativeGraphAgreementMass G Y X := by
  unfold nativeGraphWeightAgreementMass nativeGraphAgreementMass
  apply Finset.sum_congr rfl
  intro ell hell
  have hh := Finset.mem_filter.mp hell
  have hb := Finset.mem_Ico.mp hh.1
  have hlarge : forall p : Nat, Membership.mem P p -> p < ell :=
    fun p hp => (hPY p hp).trans_le hb.1
  have hi := native_graph_weight_agreement_iff P hP G hG ell hh.2 (hY.trans hb.1) hlarge
  by_cases h : nativeGraphWeightAgreementEvent G ell
  . rw [ite_eq_left h, ite_eq_left (hi.mp h)]
  . have hn : Not (nativeGraphAgreementEvent G ell) := fun ht => h (hi.mpr ht)
    rw [ite_eq_right h, ite_eq_right hn]

theorem native_graph_weight_mass_eq_eventually (P : Finset Nat)
    (hP : forall p : Nat, Membership.mem P p -> Nat.Prime p)
    (G : Finset (Prod Nat Nat)) (hG : G <= nativePrimeVertexEdges P) :
    Filter.Eventually (fun U : Nat =>
      nativeGraphWeightAgreementMass G (preciseCore U + 1)
        (preciseCore U * preciseCore U + 1) =
      nativeGraphAgreementMass G (preciseCore U + 1)
        (preciseCore U * preciseCore U + 1)) atTop := by
  filter_upwards [native_graph_field_window_eventually P,
    precise_core_tendsto_atTop.eventually_ge_atTop 4] with U hU h4
  exact native_graph_weight_mass_eq P hP G hG _ _ (by omega) hU.2

theorem native_graph_weight_agreement_ratio_tendsto (P : Finset Nat)
    (hP : forall p : Nat, Membership.mem P p -> Nat.Prime p)
    (G : Finset (Prod Nat Nat)) (hG : G <= nativePrimeVertexEdges P)
    (hne : G.Nonempty) :
    Tendsto (fun U : Nat =>
      nativeGraphWeightAgreementMass G (preciseCore U + 1)
        (preciseCore U * preciseCore U + 1) /
        reciprocalBand (preciseCore U + 1) (preciseCore U * preciseCore U + 1))
      atTop (nhds (nativeGraphAgreementRate G)) := by
  apply (native_graph_agreement_ratio_tendsto P hP G hG hne).congr'
  filter_upwards [native_graph_weight_mass_eq_eventually P hP G hG] with U hU
  rw [hU]

theorem native_graph_weight_limit_lower_bound (P : Finset Nat)
    (hP : forall p : Nat, Membership.mem P p -> Nat.Prime p)
    (G : Finset (Prod Nat Nat)) (hG : G <= nativePrimeVertexEdges P)
    (hne : G.Nonempty) :
    And
      (Tendsto (fun U : Nat =>
        nativeGraphWeightAgreementMass G (preciseCore U + 1)
          (preciseCore U * preciseCore U + 1) /
          reciprocalBand (preciseCore U + 1) (preciseCore U * preciseCore U + 1))
        atTop (nhds (nativeGraphAgreementRate G)))
      ((nativeEvenCycleCount P G : Real) *
        (1 / (2 : Real) ^ G.card + 2 / (2 : Real) ^ (G.card + G.card)) <=
          nativeGraphAgreementRate G) :=
  And.intro (native_graph_weight_agreement_ratio_tendsto P hP G hG hne)
    (native_graph_agreement_rate_lower_bound P hP G hG)

theorem native_reservoir_graph_weight_ratio_tendsto
    (R : Nat -> Prop) [DecidablePred R] (P : Finset Nat)
    (hP : forall p : Nat, Membership.mem P p ->
      Membership.mem (nativePrimeVertexGapReservoirClass R) p)
    (G : Finset (Prod Nat Nat)) (hG : G <= nativePrimeVertexEdges P)
    (hne : G.Nonempty) :
    Tendsto (fun U : Nat =>
      nativeGraphWeightAgreementMass G (preciseCore U + 1)
        (preciseCore U * preciseCore U + 1) /
        reciprocalBand (preciseCore U + 1) (preciseCore U * preciseCore U + 1))
      atTop (nhds ((nativeEvenCycleCount P G : Real) *
        (1 / (2 : Real) ^ G.card + 2 / (2 : Real) ^ (G.card + G.card)))) := by
  have hp : forall p : Nat, Membership.mem P p -> Nat.Prime p :=
    fun p hm => (native_gap_reservoir_class_geometry R p (hP p hm)).1
  have hind := native_gap_reservoir_class_finite_independent R P hP
  rw [<- native_graph_agreement_rate_eq_of_independent P hp hind G hG]
  exact native_graph_weight_agreement_ratio_tendsto P hp G hG hne

theorem native_infinite_graph_weight_family_in_reservoir
    (R : Nat -> Prop) [DecidablePred R]
    (hR : Not (Tendsto (fun N : Nat => primeEventProbability N R) atTop (nhds 0))) :
    And (Set.Infinite (nativePrimeVertexGapReservoirClass R))
      (And (forall p : Nat, Membership.mem (nativePrimeVertexGapReservoirClass R) p ->
          And (Nat.Prime p) (R p))
        (forall P : Finset Nat,
          (forall p : Nat, Membership.mem P p ->
            Membership.mem (nativePrimeVertexGapReservoirClass R) p) ->
          forall G : Finset (Prod Nat Nat), G <= nativePrimeVertexEdges P -> G.Nonempty ->
            Tendsto (fun U : Nat =>
              nativeGraphWeightAgreementMass G (preciseCore U + 1)
                (preciseCore U * preciseCore U + 1) /
                reciprocalBand (preciseCore U + 1) (preciseCore U * preciseCore U + 1))
              atTop (nhds ((nativeEvenCycleCount P G : Real) *
                (1 / (2 : Real) ^ G.card + 2 / (2 : Real) ^ (G.card + G.card)))))) := by
  have h := native_infinite_graph_coincidence_family_in_reservoir R hR
  exact And.intro h.1 (And.intro h.2.1 (native_reservoir_graph_weight_ratio_tendsto R))

theorem native_even_cycle_masks_small (P : Finset Nat)
    (G : Finset (Prod Nat Nat)) (hG : G <= nativePrimeVertexEdges P)
    (hc : G.card <= 3) :
    nativeEvenCycleMasks P G = {({} : Finset (Prod Nat Nat))} := by
  ext C
  rw [native_even_cycle_masks_mem_iff, Finset.mem_singleton]
  constructor
  . intro h
    exact native_small_even_cycle_empty P C (h.1.trans hG) h.2.1
      ((Finset.card_le_card h.1).trans hc) h.2.2
  . intro h
    rw [h]
    exact And.intro (Finset.empty_subset G)
      (And.intro (by simp [nativePrimeVertexCycleDegree]) (by simp))

theorem native_even_cycle_count_small (P : Finset Nat)
    (G : Finset (Prod Nat Nat)) (hG : G <= nativePrimeVertexEdges P)
    (hc : G.card <= 3) : nativeEvenCycleCount P G = 1 := by
  unfold nativeEvenCycleCount
  rw [native_even_cycle_masks_small P G hG hc, Finset.card_singleton]

theorem native_even_cycle_masks_four_cycle (P : Finset Nat) (p q r s : Nat)
    (hp : Membership.mem P p) (hq : Membership.mem P q)
    (hr : Membership.mem P r) (hs : Membership.mem P s)
    (hpq : p < q) (hqr : q < r) (hrs : r < s) :
    nativeEvenCycleMasks P (nativePrimeFourCycle p q r s) =
      {({} : Finset (Prod Nat Nat)), nativePrimeFourCycle p q r s} := by
  ext C
  rw [native_even_cycle_masks_mem_iff]
  change And (C <= nativePrimeFourCycle p q r s)
      (And (forall x : Nat, Membership.mem P x -> nativePrimeVertexCycleDegree C x % 2 = 0)
        (C.card % 2 = 0)) <->
    Membership.mem ({({} : Finset (Prod Nat Nat)), nativePrimeFourCycle p q r s} :
      Finset (Finset (Prod Nat Nat))) C
  rw [Finset.mem_insert, Finset.mem_singleton]
  constructor
  . intro h
    have hm : nativeSignedCycleMask P C C := And.intro rfl h.2
    rcases (native_four_cycle_mask_iff P p q r s hp hq hr hs hpq hqr hrs C C h.1).mp hm
      with hz | hz
    . exact Or.inl hz.1
    . exact Or.inr hz.1
  . intro h
    rcases h with h | h
    . rw [h]
      exact And.intro (Finset.empty_subset _)
        (And.intro (by simp [nativePrimeVertexCycleDegree]) (by simp))
    . rw [h]
      exact And.intro (Finset.Subset.refl _)
        (And.intro (fun x _ => native_four_cycle_degrees_even p q r s hpq hqr hrs x)
          (by rw [native_four_cycle_card p q r s hpq hqr hrs]))

theorem native_even_cycle_count_four_cycle (P : Finset Nat) (p q r s : Nat)
    (hp : Membership.mem P p) (hq : Membership.mem P q)
    (hr : Membership.mem P r) (hs : Membership.mem P s)
    (hpq : p < q) (hqr : q < r) (hrs : r < s) :
    nativeEvenCycleCount P (nativePrimeFourCycle p q r s) = 2 := by
  have hne : Not (nativePrimeFourCycle p q r s = {}) := by
    intro h
    have hc := native_four_cycle_card p q r s hpq hqr hrs
    rw [h, Finset.card_empty] at hc
    omega
  unfold nativeEvenCycleCount
  rw [native_even_cycle_masks_four_cycle P p q r s hp hq hr hs hpq hqr hrs]
  exact Finset.card_pair (Ne.symm hne)

theorem native_graph_one_edge_rate (P : Finset Nat)
    (hP : forall p : Nat, Membership.mem P p -> Nat.Prime p)
    (hind : nativePrimeVertexGapIndependent P)
    (G : Finset (Prod Nat Nat)) (hG : G <= nativePrimeVertexEdges P)
    (hc : G.card = 1) : nativeGraphAgreementRate G = 1 := by
  rw [native_graph_agreement_rate_eq_of_independent P hP hind G hG,
    native_even_cycle_count_small P G hG (by omega), hc]
  norm_num

theorem native_graph_two_edge_rate (P : Finset Nat)
    (hP : forall p : Nat, Membership.mem P p -> Nat.Prime p)
    (hind : nativePrimeVertexGapIndependent P)
    (G : Finset (Prod Nat Nat)) (hG : G <= nativePrimeVertexEdges P)
    (hc : G.card = 2) : nativeGraphAgreementRate G = 3 / 8 := by
  rw [native_graph_agreement_rate_eq_of_independent P hP hind G hG,
    native_even_cycle_count_small P G hG (by omega), hc]
  norm_num

theorem native_graph_three_edge_rate (P : Finset Nat)
    (hP : forall p : Nat, Membership.mem P p -> Nat.Prime p)
    (hind : nativePrimeVertexGapIndependent P)
    (G : Finset (Prod Nat Nat)) (hG : G <= nativePrimeVertexEdges P)
    (hc : G.card = 3) : nativeGraphAgreementRate G = 5 / 32 := by
  rw [native_graph_agreement_rate_eq_of_independent P hP hind G hG,
    native_even_cycle_count_small P G hG (by omega), hc]
  norm_num

theorem native_graph_four_cycle_rate (P : Finset Nat)
    (hP : forall x : Nat, Membership.mem P x -> Nat.Prime x)
    (hind : nativePrimeVertexGapIndependent P) (p q r s : Nat)
    (hp : Membership.mem P p) (hq : Membership.mem P q)
    (hr : Membership.mem P r) (hs : Membership.mem P s)
    (hpq : p < q) (hqr : q < r) (hrs : r < s) :
    nativeGraphAgreementRate (nativePrimeFourCycle p q r s) = 9 / 64 := by
  rw [native_graph_agreement_rate_eq_of_independent P hP hind _
    (native_four_cycle_support P p q r s hp hq hr hs hpq hqr hrs),
    native_even_cycle_count_four_cycle P p q r s hp hq hr hs hpq hqr hrs,
    native_four_cycle_card p q r s hpq hqr hrs]
  norm_num

theorem native_graph_one_edge_weight_ratio_tendsto (P : Finset Nat)
    (hP : forall p : Nat, Membership.mem P p -> Nat.Prime p)
    (hind : nativePrimeVertexGapIndependent P)
    (G : Finset (Prod Nat Nat)) (hG : G <= nativePrimeVertexEdges P)
    (hc : G.card = 1) :
    Tendsto (fun U : Nat =>
      nativeGraphWeightAgreementMass G (preciseCore U + 1)
        (preciseCore U * preciseCore U + 1) /
        reciprocalBand (preciseCore U + 1) (preciseCore U * preciseCore U + 1))
      atTop (nhds (1 : Real)) := by
  rw [<- native_graph_one_edge_rate P hP hind G hG hc]
  exact native_graph_weight_agreement_ratio_tendsto P hP G hG
    (Finset.card_pos.mp (by omega))

theorem native_graph_two_edge_weight_ratio_tendsto (P : Finset Nat)
    (hP : forall p : Nat, Membership.mem P p -> Nat.Prime p)
    (hind : nativePrimeVertexGapIndependent P)
    (G : Finset (Prod Nat Nat)) (hG : G <= nativePrimeVertexEdges P)
    (hc : G.card = 2) :
    Tendsto (fun U : Nat =>
      nativeGraphWeightAgreementMass G (preciseCore U + 1)
        (preciseCore U * preciseCore U + 1) /
        reciprocalBand (preciseCore U + 1) (preciseCore U * preciseCore U + 1))
      atTop (nhds (3 / 8 : Real)) := by
  rw [<- native_graph_two_edge_rate P hP hind G hG hc]
  exact native_graph_weight_agreement_ratio_tendsto P hP G hG
    (Finset.card_pos.mp (by omega))

theorem native_graph_three_edge_weight_ratio_tendsto (P : Finset Nat)
    (hP : forall p : Nat, Membership.mem P p -> Nat.Prime p)
    (hind : nativePrimeVertexGapIndependent P)
    (G : Finset (Prod Nat Nat)) (hG : G <= nativePrimeVertexEdges P)
    (hc : G.card = 3) :
    Tendsto (fun U : Nat =>
      nativeGraphWeightAgreementMass G (preciseCore U + 1)
        (preciseCore U * preciseCore U + 1) /
        reciprocalBand (preciseCore U + 1) (preciseCore U * preciseCore U + 1))
      atTop (nhds (5 / 32 : Real)) := by
  rw [<- native_graph_three_edge_rate P hP hind G hG hc]
  exact native_graph_weight_agreement_ratio_tendsto P hP G hG
    (Finset.card_pos.mp (by omega))

theorem native_graph_four_cycle_weight_ratio_tendsto (P : Finset Nat)
    (hP : forall x : Nat, Membership.mem P x -> Nat.Prime x)
    (hind : nativePrimeVertexGapIndependent P) (p q r s : Nat)
    (hp : Membership.mem P p) (hq : Membership.mem P q)
    (hr : Membership.mem P r) (hs : Membership.mem P s)
    (hpq : p < q) (hqr : q < r) (hrs : r < s) :
    Tendsto (fun U : Nat =>
      nativeGraphWeightAgreementMass (nativePrimeFourCycle p q r s)
        (preciseCore U + 1) (preciseCore U * preciseCore U + 1) /
        reciprocalBand (preciseCore U + 1) (preciseCore U * preciseCore U + 1))
      atTop (nhds (9 / 64 : Real)) := by
  rw [<- native_graph_four_cycle_rate P hP hind p q r s hp hq hr hs hpq hqr hrs]
  exact native_graph_weight_agreement_ratio_tendsto P hP _
    (native_four_cycle_support P p q r s hp hq hr hs hpq hqr hrs)
    (Finset.card_pos.mp (by rw [native_four_cycle_card p q r s hpq hqr hrs]; omega))

end PrimeFactorOscillations.FiniteFieldIntegerSignature

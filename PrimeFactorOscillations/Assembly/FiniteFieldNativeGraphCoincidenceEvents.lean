/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Assembly.FiniteFieldNativeGeneralMoments
import PrimeFactorOscillations.Assembly.FiniteFieldNativeWordEvents
import PrimeFactorOscillations.Helpers.NativeTraceAgreementAlgebra

/-! # Actual graph-coincidence events and complete physical identities

All vertices and edges are fixed before the independently varying field
band. The three agreement events remain coupled in the exact identity.
-/

set_option autoImplicit false
set_option Elab.async false

noncomputable section
namespace PrimeFactorOscillations.FiniteFieldIntegerSignature
open Filter IntegerQuadraticCharacter
open FiniteFieldIntegerWindowTransfer
open scoped Classical
attribute [local instance] Classical.propDecidable

def nativeGraphZeroTraceEvent (G : Finset (Prod Nat Nat)) (ell : Nat) : Prop :=
  forall e : Prod Nat Nat, Membership.mem G e ->
    nativeTrace e.1 (e.2 - e.1) ell = 0

def nativeGraphAgreementEvent (G : Finset (Prod Nat Nat)) (ell : Nat) : Prop :=
  forall e : Prod Nat Nat, Membership.mem G e ->
    forall f : Prod Nat Nat, Membership.mem G f ->
      nativeTrace e.1 (e.2 - e.1) ell = nativeTrace f.1 (f.2 - f.1) ell

def nativeGraphZeroTraceMass (G : Finset (Prod Nat Nat)) (Y X : Nat) : Real :=
  ((Finset.Ico Y X).filter Nat.Prime).sum (fun ell =>
    (1 / (ell : Real)) * (if nativeGraphZeroTraceEvent G ell then 1 else 0))

def nativeGraphAgreementMass (G : Finset (Prod Nat Nat)) (Y X : Nat) : Real :=
  ((Finset.Ico Y X).filter Nat.Prime).sum (fun ell =>
    (1 / (ell : Real)) * (if nativeGraphAgreementEvent G ell then 1 else 0))

theorem native_graph_zero_pointwise_selector (P : Finset Nat)
    (hP : forall p : Nat, Membership.mem P p -> Nat.Prime p)
    (G : Finset (Prod Nat Nat)) (hG : G <= nativePrimeVertexEdges P)
    (ell : Nat) (hell : Nat.Prime ell) (hell2 : 2 < ell)
    (hlarge : forall p : Nat, Membership.mem P p -> p < ell) :
    (if nativeGraphZeroTraceEvent G ell then (1 : Real) else 0) =
      G.prod (fun e => nativeWordBit false
        ((numeratorKernel (nativeSignedLowerCoefficient e) ell).re *
          (numeratorKernel (nativeSignedUpperCoefficient e) ell).re)) := by
  let x := fun e : Prod Nat Nat => (numeratorKernel (nativeSignedLowerCoefficient e) ell).re
  let y := fun e : Prod Nat Nat => (numeratorKernel (nativeSignedUpperCoefficient e) ell).re
  have hx : forall e : Prod Nat Nat, Membership.mem G e -> x e ^ 2 = 1 :=
    fun e he => (native_signed_edge_kernel_squares P hP e (hG he) ell hell hell2 hlarge).1
  have hy : forall e : Prod Nat Nat, Membership.mem G e -> y e ^ 2 = 1 :=
    fun e he => (native_signed_edge_kernel_squares P hP e (hG he) ell hell hell2 hlarge).2
  have ht : forall e : Prod Nat Nat, Membership.mem G e ->
      nativeTrace e.1 (e.2 - e.1) ell = x e + y e := by
    intro e he
    exact native_trace_eq_signed_rows e.1 e.2 ell
      ((native_gap_edges_mem_iff P e).mp (hG he)).2.2
  change (if nativeGraphZeroTraceEvent G ell then (1 : Real) else 0) =
    G.prod (fun e => nativeWordBit false (x e * y e))
  rw [native_trace_zero_selector_product G x y hx hy]
  by_cases hz : nativeGraphZeroTraceEvent G ell
  . have hs : forall e : Prod Nat Nat, Membership.mem G e -> x e + y e = 0 := by
      intro e he
      rw [<- ht e he]
      exact hz e he
    rw [ite_eq_left hz, ite_eq_left hs]
  . have hs : Not (forall e : Prod Nat Nat, Membership.mem G e -> x e + y e = 0) := by
      intro h
      apply hz
      intro e he
      rw [ht e he]
      exact h e he
    rw [ite_eq_right hz, ite_eq_right hs]

theorem native_graph_agreement_pointwise_decomposition (P : Finset Nat)
    (hP : forall p : Nat, Membership.mem P p -> Nat.Prime p)
    (G : Finset (Prod Nat Nat)) (hG : G <= nativePrimeVertexEdges P)
    (hne : G.Nonempty) (ell : Nat) (hell : Nat.Prime ell) (hell2 : 2 < ell)
    (hlarge : forall p : Nat, Membership.mem P p -> p < ell) :
    (if nativeGraphAgreementEvent G ell then (1 : Real) else 0) =
      (if nativeGraphZeroTraceEvent G ell then 1 else 0) +
        (if nativeSignedWordEvent G G (fun _ => true) (fun _ => true) ell then 1 else 0) +
        (if nativeSignedWordEvent G G (fun _ => false) (fun _ => false) ell then 1 else 0) := by
  let x := fun e : Prod Nat Nat => (numeratorKernel (nativeSignedLowerCoefficient e) ell).re
  let y := fun e : Prod Nat Nat => (numeratorKernel (nativeSignedUpperCoefficient e) ell).re
  have hx : forall e : Prod Nat Nat, Membership.mem G e -> x e ^ 2 = 1 :=
    fun e he => (native_signed_edge_kernel_squares P hP e (hG he) ell hell hell2 hlarge).1
  have hy : forall e : Prod Nat Nat, Membership.mem G e -> y e ^ 2 = 1 :=
    fun e he => (native_signed_edge_kernel_squares P hP e (hG he) ell hell hell2 hlarge).2
  have ht : forall e : Prod Nat Nat, Membership.mem G e ->
      nativeTrace e.1 (e.2 - e.1) ell = x e + y e := by
    intro e he
    exact native_trace_eq_signed_rows e.1 e.2 ell
      ((native_gap_edges_mem_iff P e).mp (hG he)).2.2
  have hi : (if nativeGraphAgreementEvent G ell then (1 : Real) else 0) =
      if (forall e : Prod Nat Nat, Membership.mem G e ->
        forall f : Prod Nat Nat, Membership.mem G f -> x e + y e = x f + y f)
        then 1 else 0 := by
    by_cases ha : nativeGraphAgreementEvent G ell
    . have hs : forall e : Prod Nat Nat, Membership.mem G e ->
          forall f : Prod Nat Nat, Membership.mem G f -> x e + y e = x f + y f := by
        intro e he f hf
        rw [<- ht e he, <- ht f hf]
        exact ha e he f hf
      rw [ite_eq_left ha, ite_eq_left hs]
    . have hs : Not (forall e : Prod Nat Nat, Membership.mem G e ->
          forall f : Prod Nat Nat, Membership.mem G f -> x e + y e = x f + y f) := by
        intro h
        apply ha
        intro e he f hf
        rw [ht e he, ht f hf]
        exact h e he f hf
      rw [ite_eq_right ha, ite_eq_right hs]
  rw [hi, native_trace_agreement_selector_product G hne x y hx hy]
  rw [<- native_graph_zero_pointwise_selector P hP G hG ell hell hell2 hlarge,
    <- native_signed_word_pointwise_selector P hP G G hG hG
      (fun _ => true) (fun _ => true) ell hell hell2 hlarge,
    <- native_signed_word_pointwise_selector P hP G G hG hG
      (fun _ => false) (fun _ => false) ell hell hell2 hlarge]

theorem native_graph_zero_mass_expansion (P : Finset Nat)
    (hP : forall p : Nat, Membership.mem P p -> Nat.Prime p)
    (G : Finset (Prod Nat Nat)) (hG : G <= nativePrimeVertexEdges P)
    (Y X : Nat) (hY : 2 < Y)
    (hPY : forall p : Nat, Membership.mem P p -> p < Y) :
    nativeGraphZeroTraceMass G Y X =
      (1 / (2 : Real) ^ G.card) *
        G.powerset.sum (fun S => (-1 : Real) ^ S.card * nativeSignedRowMoment S S Y X) := by
  let Q := (Finset.Ico Y X).filter Nat.Prime
  let C : Real := 1 / (2 : Real) ^ G.card
  have hpoint : forall ell : Nat, Membership.mem Q ell ->
      (1 / (ell : Real)) * (if nativeGraphZeroTraceEvent G ell then 1 else 0) =
        C * G.powerset.sum (fun S => (-1 : Real) ^ S.card *
          ((1 / (ell : Real)) *
            (S.prod (fun e => (numeratorKernel (nativeSignedLowerCoefficient e) ell).re) *
              S.prod (fun e => (numeratorKernel (nativeSignedUpperCoefficient e) ell).re)))) := by
    intro ell hell
    have hh := Finset.mem_filter.mp hell
    have hband := Finset.mem_Ico.mp hh.1
    have hlarge : forall p : Nat, Membership.mem P p -> p < ell :=
      fun p hp => (hPY p hp).trans_le hband.1
    rw [native_graph_zero_pointwise_selector P hP G hG ell hh.2 (by omega) hlarge,
      native_trace_zero_full_mask_expansion]
    dsimp only [C]
    simp only [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro S _
    ring
  unfold nativeGraphZeroTraceMass
  change Q.sum (fun ell => (1 / (ell : Real)) *
    (if nativeGraphZeroTraceEvent G ell then 1 else 0)) = _
  rw [Finset.sum_congr rfl hpoint, <- Finset.mul_sum]
  change C * _ = C * _
  congr 1
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro S _
  rw [<- Finset.mul_sum]
  rfl

theorem native_graph_agreement_mass_decomposition (P : Finset Nat)
    (hP : forall p : Nat, Membership.mem P p -> Nat.Prime p)
    (G : Finset (Prod Nat Nat)) (hG : G <= nativePrimeVertexEdges P)
    (hne : G.Nonempty) (Y X : Nat) (hY : 2 < Y)
    (hPY : forall p : Nat, Membership.mem P p -> p < Y) :
    nativeGraphAgreementMass G Y X =
      nativeGraphZeroTraceMass G Y X +
        nativeSignedWordMass G G (fun _ => true) (fun _ => true) Y X +
        nativeSignedWordMass G G (fun _ => false) (fun _ => false) Y X := by
  unfold nativeGraphAgreementMass nativeGraphZeroTraceMass nativeSignedWordMass
  rw [<- Finset.sum_add_distrib, <- Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro ell hell
  have hh := Finset.mem_filter.mp hell
  have hband := Finset.mem_Ico.mp hh.1
  have hlarge : forall p : Nat, Membership.mem P p -> p < ell :=
    fun p hp => (hPY p hp).trans_le hband.1
  rw [native_graph_agreement_pointwise_decomposition P hP G hG hne ell hh.2 (by omega) hlarge]
  ring

theorem native_graph_field_window_eventually (P : Finset Nat) :
    Filter.Eventually (fun U : Nat => And (2 < preciseCore U + 1)
      (forall p : Nat, Membership.mem P p -> p < preciseCore U + 1)) atTop := by
  choose K hK using P.finite_toSet.bddAbove
  filter_upwards [precise_core_tendsto_atTop.eventually_ge_atTop (max K 3)] with U hU
  have hKC : K <= preciseCore U := (Nat.le_max_left K 3).trans hU
  have h3C : 3 <= preciseCore U := (Nat.le_max_right K 3).trans hU
  refine And.intro (by omega) ?_
  intro p hp
  have hpK := hK hp
  omega

theorem native_graph_zero_mass_expansion_eventually (P : Finset Nat)
    (hP : forall p : Nat, Membership.mem P p -> Nat.Prime p)
    (G : Finset (Prod Nat Nat)) (hG : G <= nativePrimeVertexEdges P) :
    Filter.Eventually (fun U : Nat =>
      nativeGraphZeroTraceMass G (preciseCore U + 1) (preciseCore U * preciseCore U + 1) =
        (1 / (2 : Real) ^ G.card) *
          G.powerset.sum (fun S => (-1 : Real) ^ S.card *
            nativeSignedRowMoment S S (preciseCore U + 1)
              (preciseCore U * preciseCore U + 1))) atTop := by
  filter_upwards [native_graph_field_window_eventually P] with U hU
  exact native_graph_zero_mass_expansion P hP G hG _ _ hU.1 hU.2

theorem native_graph_agreement_mass_decomposition_eventually (P : Finset Nat)
    (hP : forall p : Nat, Membership.mem P p -> Nat.Prime p)
    (G : Finset (Prod Nat Nat)) (hG : G <= nativePrimeVertexEdges P)
    (hne : G.Nonempty) :
    Filter.Eventually (fun U : Nat =>
      nativeGraphAgreementMass G (preciseCore U + 1) (preciseCore U * preciseCore U + 1) =
        nativeGraphZeroTraceMass G (preciseCore U + 1) (preciseCore U * preciseCore U + 1) +
          nativeSignedWordMass G G (fun _ => true) (fun _ => true)
            (preciseCore U + 1) (preciseCore U * preciseCore U + 1) +
          nativeSignedWordMass G G (fun _ => false) (fun _ => false)
            (preciseCore U + 1) (preciseCore U * preciseCore U + 1)) atTop := by
  filter_upwards [native_graph_field_window_eventually P] with U hU
  exact native_graph_agreement_mass_decomposition P hP G hG hne _ _ hU.1 hU.2

def nativeSignedGeneralWordRate (A B : Finset (Prod Nat Nat))
    (a b : Prod Nat Nat -> Bool) : Real :=
  (1 / (2 : Real) ^ (A.card + B.card)) *
    A.powerset.sum (fun O => B.powerset.sum (fun T =>
      nativeSignedWordMaskCoefficient O T a b *
        numeratorPrincipalIndicator (nativeSignedRowProduct O T)))

def nativeGraphZeroTraceRate (G : Finset (Prod Nat Nat)) : Real :=
  (1 / (2 : Real) ^ G.card) *
    G.powerset.sum (fun S => (-1 : Real) ^ S.card *
      numeratorPrincipalIndicator (nativeSignedRowProduct S S))

def nativeGraphAgreementRate (G : Finset (Prod Nat Nat)) : Real :=
  nativeGraphZeroTraceRate G +
    nativeSignedGeneralWordRate G G (fun _ => true) (fun _ => true) +
    nativeSignedGeneralWordRate G G (fun _ => false) (fun _ => false)

theorem native_signed_word_general_ratio_tendsto (P : Finset Nat)
    (hP : forall p : Nat, Membership.mem P p -> Nat.Prime p)
    (A B : Finset (Prod Nat Nat))
    (hA : A <= nativePrimeVertexEdges P) (hB : B <= nativePrimeVertexEdges P)
    (a b : Prod Nat Nat -> Bool) :
    Tendsto (fun U : Nat =>
      nativeSignedWordMass A B a b (preciseCore U + 1) (preciseCore U * preciseCore U + 1) /
        reciprocalBand (preciseCore U + 1) (preciseCore U * preciseCore U + 1))
      atTop (nhds (nativeSignedGeneralWordRate A B a b)) := by
  let C : Real := 1 / (2 : Real) ^ (A.card + B.card)
  let F : Nat -> Real := fun U =>
    C * A.powerset.sum (fun O => B.powerset.sum (fun T =>
      nativeSignedWordMaskCoefficient O T a b *
        (nativeSignedRowMoment O T (preciseCore U + 1) (preciseCore U * preciseCore U + 1) /
          reciprocalBand (preciseCore U + 1) (preciseCore U * preciseCore U + 1))))
  have hlim : Tendsto F atTop (nhds (nativeSignedGeneralWordRate A B a b)) := by
    dsimp only [F, C, nativeSignedGeneralWordRate]
    apply Filter.Tendsto.const_mul
    apply tendsto_finsetSum A.powerset
    intro O hO
    apply tendsto_finsetSum B.powerset
    intro T hT
    have hm := native_signed_row_moment_general_ratio_tendsto O T
      (native_signed_row_product_ne_zero P hP O T
        ((Finset.mem_powerset.mp hO).trans hA) ((Finset.mem_powerset.mp hT).trans hB))
    exact Filter.Tendsto.const_mul (nativeSignedWordMaskCoefficient O T a b) hm
  apply hlim.congr'
  filter_upwards [native_signed_word_mass_expansion_eventually P hP A B hA hB a b] with U hU
  dsimp only [F, C]
  rw [hU]
  simp only [mul_div_assoc, Finset.sum_div]

theorem native_graph_zero_ratio_tendsto (P : Finset Nat)
    (hP : forall p : Nat, Membership.mem P p -> Nat.Prime p)
    (G : Finset (Prod Nat Nat)) (hG : G <= nativePrimeVertexEdges P) :
    Tendsto (fun U : Nat =>
      nativeGraphZeroTraceMass G (preciseCore U + 1) (preciseCore U * preciseCore U + 1) /
        reciprocalBand (preciseCore U + 1) (preciseCore U * preciseCore U + 1))
      atTop (nhds (nativeGraphZeroTraceRate G)) := by
  let C : Real := 1 / (2 : Real) ^ G.card
  let F : Nat -> Real := fun U =>
    C * G.powerset.sum (fun S => (-1 : Real) ^ S.card *
      (nativeSignedRowMoment S S (preciseCore U + 1) (preciseCore U * preciseCore U + 1) /
        reciprocalBand (preciseCore U + 1) (preciseCore U * preciseCore U + 1)))
  have hlim : Tendsto F atTop (nhds (nativeGraphZeroTraceRate G)) := by
    dsimp only [F, C, nativeGraphZeroTraceRate]
    apply Filter.Tendsto.const_mul
    apply tendsto_finsetSum G.powerset
    intro S hS
    have hsub := (Finset.mem_powerset.mp hS).trans hG
    exact Filter.Tendsto.const_mul ((-1 : Real) ^ S.card)
      (native_signed_row_moment_general_ratio_tendsto S S
        (native_signed_row_product_ne_zero P hP S S hsub hsub))
  apply hlim.congr'
  filter_upwards [native_graph_zero_mass_expansion_eventually P hP G hG] with U hU
  dsimp only [F, C]
  rw [hU]
  simp only [mul_div_assoc, Finset.sum_div]

theorem native_graph_agreement_ratio_tendsto (P : Finset Nat)
    (hP : forall p : Nat, Membership.mem P p -> Nat.Prime p)
    (G : Finset (Prod Nat Nat)) (hG : G <= nativePrimeVertexEdges P)
    (hne : G.Nonempty) :
    Tendsto (fun U : Nat =>
      nativeGraphAgreementMass G (preciseCore U + 1) (preciseCore U * preciseCore U + 1) /
        reciprocalBand (preciseCore U + 1) (preciseCore U * preciseCore U + 1))
      atTop (nhds (nativeGraphAgreementRate G)) := by
  have hz := native_graph_zero_ratio_tendsto P hP G hG
  have hp := native_signed_word_general_ratio_tendsto P hP G G hG hG
    (fun _ => true) (fun _ => true)
  have hn := native_signed_word_general_ratio_tendsto P hP G G hG hG
    (fun _ => false) (fun _ => false)
  apply ((hz.add hp).add hn).congr'
  filter_upwards [native_graph_agreement_mass_decomposition_eventually P hP G hG hne] with U hU
  rw [hU]
  simp only [add_div]

end PrimeFactorOscillations.FiniteFieldIntegerSignature

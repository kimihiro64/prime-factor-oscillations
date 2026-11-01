/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Assembly.FiniteFieldNativeSignedMoments
import PrimeFactorOscillations.Helpers.NativeWordBooleanAlgebra

/-! # Actual signed character word events and their full finite expansion

All field primes beyond the fixed vertex bound are units for every vertex
and gap factor. The exact word expansion retains every pair of masks.
-/

set_option autoImplicit false
set_option Elab.async false

noncomputable section
namespace PrimeFactorOscillations.FiniteFieldIntegerSignature
open Filter IntegerQuadraticCharacter
open FiniteFieldIntegerWindowTransfer
open scoped Classical
attribute [local instance] Classical.propDecidable

def nativeSignedWordEvent (A B : Finset (Prod Nat Nat))
    (a b : Prod Nat Nat -> Bool) (ell : Nat) : Prop :=
  And (forall e : Prod Nat Nat, Membership.mem A e ->
      (numeratorKernel (nativeSignedLowerCoefficient e) ell).re = nativeWordSign (a e))
    (forall e : Prod Nat Nat, Membership.mem B e ->
      (numeratorKernel (nativeSignedUpperCoefficient e) ell).re = nativeWordSign (b e))

def nativeSignedWordMass (A B : Finset (Prod Nat Nat))
    (a b : Prod Nat Nat -> Bool) (Y X : Nat) : Real :=
  ((Finset.Ico Y X).filter Nat.Prime).sum (fun ell =>
    (1 / (ell : Real)) * (if nativeSignedWordEvent A B a b ell then 1 else 0))

def nativeSignedWordMaskCoefficient (O T : Finset (Prod Nat Nat))
    (a b : Prod Nat Nat -> Bool) : Real :=
  O.prod (fun e => nativeWordSign (a e)) * T.prod (fun e => nativeWordSign (b e))

theorem native_signed_edge_kernel_squares (P : Finset Nat)
    (hP : forall p : Nat, Membership.mem P p -> Nat.Prime p)
    (e : Prod Nat Nat) (he : Membership.mem (nativePrimeVertexEdges P) e)
    (ell : Nat) (hell : Nat.Prime ell) (hell2 : 2 < ell)
    (hlarge : forall p : Nat, Membership.mem P p -> p < ell) :
    And ((numeratorKernel (nativeSignedLowerCoefficient e) ell).re ^ 2 = 1)
      ((numeratorKernel (nativeSignedUpperCoefficient e) ell).re ^ 2 = 1) := by
  let : Fact (Nat.Prime ell) := Fact.mk hell
  have hh := (native_gap_edges_mem_iff P e).mp he
  have hmod (n : Nat) (hn : 0 < n) (hnl : n < ell) : Not ((n : ZMod ell) = 0) := by
    intro hz
    exact (Nat.not_dvd_of_pos_of_lt hn hnl) ((ZMod.natCast_eq_zero_iff n ell).mp hz)
  have hp := hmod e.1 (hP e.1 hh.1).pos (hlarge e.1 hh.1)
  have hq := hmod e.2 (hP e.2 hh.2.1).pos (hlarge e.2 hh.2.1)
  have hgap := hmod (e.2 - e.1) (Nat.sub_pos_of_lt hh.2.2)
    ((Nat.sub_le e.2 e.1).trans_lt (hlarge e.2 hh.2.1))
  have hlow : Not ((nativeSignedLowerCoefficient e : ZMod ell) = 0) := by
    simpa only [nativeSignedLowerCoefficient, Int.cast_neg, Int.cast_mul, Int.cast_natCast, Nat.cast_mul] using
      neg_ne_zero.mpr (mul_ne_zero hp hgap)
  have hupp : Not ((nativeSignedUpperCoefficient e : ZMod ell) = 0) := by
    simpa only [nativeSignedUpperCoefficient, Int.cast_mul, Int.cast_natCast, Nat.cast_mul] using
      mul_ne_zero hq hgap
  exact And.intro (real_kernel_square_of_nonzero _ ell hell2 hlow)
    (real_kernel_square_of_nonzero _ ell hell2 hupp)

theorem native_signed_word_pointwise_selector (P : Finset Nat)
    (hP : forall p : Nat, Membership.mem P p -> Nat.Prime p)
    (A B : Finset (Prod Nat Nat))
    (hA : A <= nativePrimeVertexEdges P) (hB : B <= nativePrimeVertexEdges P)
    (a b : Prod Nat Nat -> Bool) (ell : Nat)
    (hell : Nat.Prime ell) (hell2 : 2 < ell)
    (hlarge : forall p : Nat, Membership.mem P p -> p < ell) :
    (if nativeSignedWordEvent A B a b ell then (1 : Real) else 0) =
      A.prod (fun e => nativeWordBit (a e)
        (numeratorKernel (nativeSignedLowerCoefficient e) ell).re) *
      B.prod (fun e => nativeWordBit (b e)
        (numeratorKernel (nativeSignedUpperCoefficient e) ell).re) := by
  rw [native_word_selector_product A a _
      (fun e he => (native_signed_edge_kernel_squares P hP e (hA he) ell hell hell2 hlarge).1),
    native_word_selector_product B b _
      (fun e he => (native_signed_edge_kernel_squares P hP e (hB he) ell hell hell2 hlarge).2)]
  by_cases ha : forall e : Prod Nat Nat, Membership.mem A e ->
      (numeratorKernel (nativeSignedLowerCoefficient e) ell).re = nativeWordSign (a e)
  . by_cases hb : forall e : Prod Nat Nat, Membership.mem B e ->
        (numeratorKernel (nativeSignedUpperCoefficient e) ell).re = nativeWordSign (b e)
    . have hev : nativeSignedWordEvent A B a b ell := And.intro ha hb
      rw [ite_eq_left hev, ite_eq_left ha, ite_eq_left hb, one_mul]
    . have hev : Not (nativeSignedWordEvent A B a b ell) := fun h => hb h.2
      rw [ite_eq_right hev, ite_eq_right hb, mul_zero]
  . have hev : Not (nativeSignedWordEvent A B a b ell) := fun h => ha h.1
    rw [ite_eq_right hev, ite_eq_right ha, zero_mul]

theorem native_signed_word_mass_expansion (P : Finset Nat)
    (hP : forall p : Nat, Membership.mem P p -> Nat.Prime p)
    (A B : Finset (Prod Nat Nat))
    (hA : A <= nativePrimeVertexEdges P) (hB : B <= nativePrimeVertexEdges P)
    (a b : Prod Nat Nat -> Bool) (Y X : Nat) (hY : 2 < Y)
    (hPY : forall p : Nat, Membership.mem P p -> p < Y) :
    nativeSignedWordMass A B a b Y X =
      (1 / (2 : Real) ^ (A.card + B.card)) *
        A.powerset.sum (fun O => B.powerset.sum (fun T =>
          nativeSignedWordMaskCoefficient O T a b * nativeSignedRowMoment O T Y X)) := by
  let Q := (Finset.Ico Y X).filter Nat.Prime
  let C : Real := 1 / (2 : Real) ^ (A.card + B.card)
  have hpoint : forall ell : Nat, Membership.mem Q ell ->
      (1 / (ell : Real)) * (if nativeSignedWordEvent A B a b ell then 1 else 0) =
        C * A.powerset.sum (fun O => B.powerset.sum (fun T =>
          nativeSignedWordMaskCoefficient O T a b *
            ((1 / (ell : Real)) *
              (O.prod (fun e => (numeratorKernel (nativeSignedLowerCoefficient e) ell).re) *
                T.prod (fun e => (numeratorKernel (nativeSignedUpperCoefficient e) ell).re))))) := by
    intro ell hell
    have hh := Finset.mem_filter.mp hell
    have hband := Finset.mem_Ico.mp hh.1
    have hlarge : forall p : Nat, Membership.mem P p -> p < ell := by
      intro p hp
      exact (hPY p hp).trans_le hband.1
    rw [native_signed_word_pointwise_selector P hP A B hA hB a b ell hh.2
      (by omega) hlarge, native_word_full_mask_expansion]
    dsimp only [C]
    simp only [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro O _
    apply Finset.sum_congr rfl
    intro T _
    unfold nativeSignedWordMaskCoefficient
    ring
  unfold nativeSignedWordMass
  change Q.sum (fun ell => (1 / (ell : Real)) *
    (if nativeSignedWordEvent A B a b ell then 1 else 0)) = _
  rw [Finset.sum_congr rfl hpoint, <- Finset.mul_sum]
  change C * _ = C * _
  congr 1
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro O _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro T _
  rw [<- Finset.mul_sum]
  rfl

theorem native_signed_word_mass_expansion_eventually (P : Finset Nat)
    (hP : forall p : Nat, Membership.mem P p -> Nat.Prime p)
    (A B : Finset (Prod Nat Nat))
    (hA : A <= nativePrimeVertexEdges P) (hB : B <= nativePrimeVertexEdges P)
    (a b : Prod Nat Nat -> Bool) :
    Filter.Eventually (fun U : Nat =>
      nativeSignedWordMass A B a b (preciseCore U + 1) (preciseCore U * preciseCore U + 1) =
        (1 / (2 : Real) ^ (A.card + B.card)) *
          A.powerset.sum (fun O => B.powerset.sum (fun T =>
            nativeSignedWordMaskCoefficient O T a b *
              nativeSignedRowMoment O T (preciseCore U + 1)
                (preciseCore U * preciseCore U + 1)))) atTop := by
  choose K hK using P.finite_toSet.bddAbove
  filter_upwards [precise_core_tendsto_atTop.eventually_ge_atTop (max K 3)] with U hU
  have hKC : K <= preciseCore U := (Nat.le_max_left K 3).trans hU
  have h3C : 3 <= preciseCore U := (Nat.le_max_right K 3).trans hU
  apply native_signed_word_mass_expansion P hP A B hA hB a b _ _ (by omega)
  intro p hp
  have hpK := hK hp
  omega

end PrimeFactorOscillations.FiniteFieldIntegerSignature

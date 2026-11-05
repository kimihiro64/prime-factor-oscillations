/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Assembly.FiniteFieldNativeNoncentralRecurrence

/-! # An explicit one-bit-per-vertex code for actual native centrality profiles -/

set_option autoImplicit false
set_option Elab.async false

noncomputable section
namespace PrimeFactorOscillations.FiniteFieldIntegerSignature
open Filter IntegerQuadraticCharacter FiniteFieldIntegerCharacter
open FiniteFieldIntegerWindowTransfer
open scoped Classical
attribute [local instance] Classical.propDecidable

def nativeProfileVertexBit (r : Nat) (S : Finset Nat) (p : Nat) : Bool :=
  if p = r then true else decide (Membership.mem S p)

def nativeProfileDecodedBit (r : Nat) (S : Finset Nat) (e : Prod Nat Nat) : Bool :=
  decide (Membership.mem S r) ==
    (nativeProfileVertexBit r S e.1 == nativeProfileVertexBit r S e.2)

def nativeProfileDecodedSet (r : Nat) (G : Finset (Prod Nat Nat)) (S : Finset Nat) :
    Finset (Prod Nat Nat) :=
  G.filter (fun e => nativeProfileDecodedBit r S e = true)

def nativeProfileCodeImage (r : Nat) (P : Finset Nat) (G : Finset (Prod Nat Nat)) :
    Finset (Finset (Prod Nat Nat)) :=
  P.powerset.image (fun S => nativeProfileDecodedSet r G S)

def nativeProfileSignCode (r : Nat) (P : Finset Nat) (sigma : Real) (u : Nat -> Real) :
    Finset Nat :=
  P.filter (fun p => if p = r then sigma = 1 else u p = 1)

theorem native_word_sign_bool_eq (b c : Bool) :
    nativeWordSign (b == c) = nativeWordSign b * nativeWordSign c := by
  cases b <;> cases c <;> norm_num [nativeWordSign]

theorem native_sign_decision_of_square_eq_one (z : Real) (hz : z ^ 2 = 1) :
    nativeWordSign (decide (z = 1)) = z := by
  have hf : (z - 1) * (z + 1) = 0 := by nlinarith only [hz]
  rcases mul_eq_zero.mp hf with h | h
  . have he : z = 1 := by linarith only [h]
    norm_num [he, nativeWordSign]
  . have he : z = -1 := by linarith only [h]
    norm_num [he, nativeWordSign]

theorem native_profile_decoded_bit_sign (r : Nat) (S : Finset Nat) (e : Prod Nat Nat) :
    nativeWordSign (nativeProfileDecodedBit r S e) =
      nativeWordSign (decide (Membership.mem S r)) *
        nativeWordSign (nativeProfileVertexBit r S e.1) *
          nativeWordSign (nativeProfileVertexBit r S e.2) := by
  unfold nativeProfileDecodedBit
  rw [native_word_sign_bool_eq, native_word_sign_bool_eq]
  ring

theorem native_profile_sign_code_phase (P : Finset Nat) (r : Nat)
    (hr : Membership.mem P r) (sigma : Real) (u : Nat -> Real) (hs : sigma ^ 2 = 1) :
    nativeWordSign (decide (Membership.mem (nativeProfileSignCode r P sigma u) r)) = sigma := by
  simpa only [nativeProfileSignCode, Finset.mem_filter, hr, true_and, ite_true] using
    native_sign_decision_of_square_eq_one sigma hs

theorem native_profile_sign_code_vertex (P : Finset Nat) (r : Nat)
    (u : Nat -> Real) (hur : u r = 1) (hu : forall p : Nat, Membership.mem P p -> u p ^ 2 = 1)
    (sigma : Real) (p : Nat) (hp : Membership.mem P p) :
    nativeWordSign (nativeProfileVertexBit r (nativeProfileSignCode r P sigma u) p) = u p := by
  by_cases hpr : p = r
  . rw [hpr, nativeProfileVertexBit, ite_eq_left rfl]
    change (1 : Real) = u r
    exact hur.symm
  . simpa only [nativeProfileVertexBit, hpr, ite_false, nativeProfileSignCode,
      Finset.mem_filter, hp, true_and] using native_sign_decision_of_square_eq_one (u p) (hu p hp)

theorem native_profile_sign_code_decoded_sign (P : Finset Nat) (r : Nat)
    (hr : Membership.mem P r) (sigma : Real) (hs : sigma ^ 2 = 1)
    (u : Nat -> Real) (hur : u r = 1)
    (hu : forall p : Nat, Membership.mem P p -> u p ^ 2 = 1)
    (e : Prod Nat Nat) (hp : Membership.mem P e.1) (hq : Membership.mem P e.2) :
    nativeWordSign (nativeProfileDecodedBit r (nativeProfileSignCode r P sigma u) e) =
      sigma * u e.1 * u e.2 := by
  rw [native_profile_decoded_bit_sign, native_profile_sign_code_phase P r hr sigma u hs,
    native_profile_sign_code_vertex P r u hur hu sigma e.1 hp,
    native_profile_sign_code_vertex P r u hur hu sigma e.2 hq]

theorem native_profile_code_image_card_le (r : Nat) (P : Finset Nat)
    (G : Finset (Prod Nat Nat)) :
    (nativeProfileCodeImage r P G).card <= 2 ^ P.card := by
  unfold nativeProfileCodeImage
  calc
    _ <= P.powerset.card := Finset.card_image_le
    _ = _ := by simp

theorem native_vertex_character_square (n ell : Nat) (hell : Nat.Prime ell)
    (hell2 : 2 < ell) (hn : 0 < n) (hnell : n < ell) :
    (numeratorKernel (n : Int) ell).re ^ 2 = 1 := by
  let : Fact (Nat.Prime ell) := Fact.mk hell
  apply real_kernel_square_of_nonzero (n : Int) ell hell2
  intro hz
  have hzNat : (n : ZMod ell) = 0 := by simpa only [Int.cast_natCast] using hz
  have hd : Dvd.dvd ell n := (ZMod.natCast_eq_zero_iff n ell).mp hzNat
  exact (Nat.not_dvd_of_pos_of_lt hn hnell) hd

theorem native_actual_profile_has_vertex_code (P : Finset Nat)
    (hP : forall p : Nat, Membership.mem P p -> Nat.Prime p)
    (r : Nat) (hr : Membership.mem P r)
    (G : Finset (Prod Nat Nat)) (hG : G <= nativePrimeVertexEdges P)
    (ell : Nat) (hell : Nat.Prime ell) (hell5 : 5 <= ell)
    (hlarge : forall p : Nat, Membership.mem P p -> p < ell) :
    Exists (fun S : Finset Nat => And (S <= P)
      (nativeCentralProfileEvent G (nativeProfileDecodedBit r S) ell)) := by
  let : Fact (Nat.Prime ell) := Fact.mk hell
  let x : Nat -> Real := fun p => (numeratorKernel (p : Int) ell).re
  let sigma : Real := (numeratorKernel (-1) ell).re
  let u : Nat -> Real := fun p => x p * x r
  have hx : forall p : Nat, Membership.mem P p -> x p ^ 2 = 1 := by
    intro p hp
    exact native_vertex_character_square p ell hell (by omega) (hP p hp).pos (hlarge p hp)
  have hxr := hx r hr
  have hs : sigma ^ 2 = 1 := by
    exact real_kernel_square_of_nonzero (-1) ell (by omega) (by norm_num)
  have hur : u r = 1 := by
    simpa only [u, pow_two] using hxr
  have hu : forall p : Nat, Membership.mem P p -> u p ^ 2 = 1 := by
    intro p hp
    dsimp only [u]
    rw [mul_pow, hx p hp, hxr, one_mul]
  let S := nativeProfileSignCode r P sigma u
  refine Exists.intro S (And.intro (Finset.filter_subset _ _) ?_)
  apply (native_central_profile_iff_vanishing P hP G hG (nativeProfileDecodedBit r S)
    ell hell hell5 hlarge).mpr
  intro e he
  have hed := (native_gap_edges_mem_iff P e).mp (hG he)
  have hadd : e.1 + (e.2 - e.1) = e.2 := Nat.add_sub_of_le hed.2.2.le
  have ht := native_trace_endpoint_readout e.1 (e.2 - e.1) ell
    (hP e.1 hed.1).pos (Nat.sub_pos_of_lt hed.2.2) (by omega)
    (by rw [hadd]; exact hlarge e.2 hed.2.1)
  rw [hadd] at ht
  have hkernel : (numeratorKernel (-((e.1 : Int) * (e.2 : Int))) ell).re =
      sigma * x e.1 * x e.2 := by
    have hf : -((e.1 : Int) * (e.2 : Int)) = (-1 : Int) * (e.1 : Int) * (e.2 : Int) := by ring
    rw [hf, real_kernel_mul, real_kernel_mul]
  have hdecode : nativeWordSign (nativeProfileDecodedBit r S e) =
      (numeratorKernel (-((e.1 : Int) * (e.2 : Int))) ell).re := by
    rw [native_profile_sign_code_decoded_sign P r hr sigma hs u hur hu e hed.1 hed.2.1,
      hkernel]
    calc
      sigma * u e.1 * u e.2 = (sigma * x e.1 * x e.2) * (x r ^ 2) := by dsimp [u]; ring
      _ = _ := by rw [hxr, mul_one]
  cases hb : nativeProfileDecodedBit r S e
  . change nativeTrace e.1 (e.2 - e.1) ell = 0
    have hk : (numeratorKernel (-((e.1 : Int) * (e.2 : Int))) ell).re = -1 := by
      simpa only [hb, nativeWordSign, Bool.false_eq_true, ite_false] using hdecode.symm
    rw [hk] at ht
    nlinarith only [ht]
  . change Not (nativeTrace e.1 (e.2 - e.1) ell = 0)
    intro hz
    have hk : (numeratorKernel (-((e.1 : Int) * (e.2 : Int))) ell).re = 1 := by
      simpa only [hb, nativeWordSign, ite_true] using hdecode.symm
    rw [hk, hz] at ht
    norm_num at ht


def nativeRealizableProfileSets (G : Finset (Prod Nat Nat)) (B : Nat) :
    Finset (Finset (Prod Nat Nat)) :=
  G.powerset.filter (fun T => Exists (fun ell : Nat =>
    And (Nat.Prime ell) (And (B < ell)
      (nativeCentralProfileEvent G (fun e => decide (Membership.mem T e)) ell))))

theorem native_central_profile_event_unique (G : Finset (Prod Nat Nat))
    (a b : Prod Nat Nat -> Bool) (ell : Nat)
    (ha : nativeCentralProfileEvent G a ell) (hb : nativeCentralProfileEvent G b ell)
    (e : Prod Nat Nat) (he : Membership.mem G e) : a e = b e := by
  cases hA : a e <;> cases hB : b e
  . rfl
  . have h1 := ha e he
    have h2 := hb e he
    simp only [hA, Bool.false_eq_true, ite_false] at h1
    simp only [hB, ite_true] at h2
    exact False.elim (h2 h1)
  . have h1 := ha e he
    have h2 := hb e he
    simp only [hA, ite_true] at h1
    simp only [hB, Bool.false_eq_true, ite_false] at h2
    exact False.elim (h1 h2)
  . rfl

theorem native_realizable_profiles_subset_vertex_code (P : Finset Nat)
    (hP : forall p : Nat, Membership.mem P p -> Nat.Prime p)
    (r : Nat) (hr : Membership.mem P r)
    (G : Finset (Prod Nat Nat)) (hG : G <= nativePrimeVertexEdges P)
    (B : Nat) (hB5 : 5 <= B) (hPB : forall p : Nat, Membership.mem P p -> p <= B) :
    nativeRealizableProfileSets G B <= nativeProfileCodeImage r P G := by
  intro T hT
  have hh := Finset.mem_filter.mp hT
  have hTG : T <= G := Finset.mem_powerset.mp hh.1
  choose ell hell using hh.2
  have hlarge : forall p : Nat, Membership.mem P p -> p < ell :=
    fun p hp => lt_of_le_of_lt (hPB p hp) hell.2.1
  choose S hS using native_actual_profile_has_vertex_code P hP r hr G hG ell hell.1
    (by omega) hlarge
  have heq : T = nativeProfileDecodedSet r G S := by
    apply Finset.Subset.antisymm
    . intro e he
      have hu := native_central_profile_event_unique G
        (fun f => decide (Membership.mem T f)) (nativeProfileDecodedBit r S) ell
          hell.2.2 hS.2 e (hTG he)
      apply Finset.mem_filter.mpr
      refine And.intro (hTG he) ?_
      have ht : (decide (Membership.mem T e) : Bool) = true := by simp [he]
      exact hu.symm.trans ht
    . intro e he
      have hd := Finset.mem_filter.mp he
      have hu := native_central_profile_event_unique G
        (fun f => decide (Membership.mem T f)) (nativeProfileDecodedBit r S) ell
          hell.2.2 hS.2 e hd.1
      exact of_decide_eq_true (hu.trans hd.2)
  apply Finset.mem_image.mpr
  exact Exists.intro S (And.intro (Finset.mem_powerset.mpr hS.1) heq.symm)

theorem native_realizable_profiles_card_le (P : Finset Nat)
    (hP : forall p : Nat, Membership.mem P p -> Nat.Prime p)
    (r : Nat) (hr : Membership.mem P r)
    (G : Finset (Prod Nat Nat)) (hG : G <= nativePrimeVertexEdges P)
    (B : Nat) (hB5 : 5 <= B) (hPB : forall p : Nat, Membership.mem P p -> p <= B) :
    (nativeRealizableProfileSets G B).card <= 2 ^ P.card := by
  exact (Finset.card_le_card
    (native_realizable_profiles_subset_vertex_code P hP r hr G hG B hB5 hPB)).trans
      (native_profile_code_image_card_le r P G)
end PrimeFactorOscillations.FiniteFieldIntegerSignature

/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Definitions.NativePrimeSquareMaskRelations
import PrimeFactorOscillations.Helpers.NativePrimePhaseRowKernel

/-! # Full square-mask translation with repeated factors retained -/

set_option autoImplicit false
set_option Elab.async false

namespace PrimeFactorOscillations.FiniteFieldIntegerSignature

theorem native_mask_product_symmDiff_square_factor {I : Type*} [DecidableEq I]
    (S T : Finset I) (f : I -> Nat) :
    S.prod f * T.prod f =
      (symmDiff S T).prod f * (Inter.inter S T).prod f ^ 2 := by
  have hd1 : Disjoint (SDiff.sdiff S T) (Inter.inter S T) := Finset.disjoint_left.mpr (by
    intro x hx hy
    exact (Finset.mem_sdiff.mp hx).2 (Finset.mem_inter.mp hy).2)
  have hd2 : Disjoint (SDiff.sdiff T S) (Inter.inter S T) := Finset.disjoint_left.mpr (by
    intro x hx hy
    exact (Finset.mem_sdiff.mp hx).2 (Finset.mem_inter.mp hy).1)
  have hd3 : Disjoint (SDiff.sdiff S T) (SDiff.sdiff T S) := Finset.disjoint_left.mpr (by
    intro x hx hy
    exact (Finset.mem_sdiff.mp hx).2 (Finset.mem_sdiff.mp hy).1)
  have hpT : Union.union (SDiff.sdiff T S) (Inter.inter S T) = T := by
    rw [Finset.inter_comm S T]
    exact Finset.sdiff_union_inter T S
  have h1 : S.prod f = (SDiff.sdiff S T).prod f * (Inter.inter S T).prod f := by
    calc
      _ = (Union.union (SDiff.sdiff S T) (Inter.inter S T)).prod f := by rw [Finset.sdiff_union_inter]
      _ = _ := Finset.prod_union hd1
  have h2 : T.prod f = (SDiff.sdiff T S).prod f * (Inter.inter S T).prod f := by
    calc
      _ = (Union.union (SDiff.sdiff T S) (Inter.inter S T)).prod f := by rw [hpT]
      _ = _ := Finset.prod_union hd2
  have h3 : (symmDiff S T).prod f = (SDiff.sdiff S T).prod f * (SDiff.sdiff T S).prod f := by
    rw [Finset.symmDiff_def]
    exact Finset.prod_union hd3
  rw [h1, h2, h3]
  ring

theorem native_mask_card_symmDiff_double_inter {I : Type*} [DecidableEq I]
    (S T : Finset I) :
    (symmDiff S T).card + 2 * (Inter.inter S T).card = S.card + T.card := by
  have hd1 : Disjoint (SDiff.sdiff S T) (Inter.inter S T) := Finset.disjoint_left.mpr (by
    intro x hx hy
    exact (Finset.mem_sdiff.mp hx).2 (Finset.mem_inter.mp hy).2)
  have hd2 : Disjoint (SDiff.sdiff T S) (Inter.inter S T) := Finset.disjoint_left.mpr (by
    intro x hx hy
    exact (Finset.mem_sdiff.mp hx).2 (Finset.mem_inter.mp hy).1)
  have hd3 : Disjoint (SDiff.sdiff S T) (SDiff.sdiff T S) := Finset.disjoint_left.mpr (by
    intro x hx hy
    exact (Finset.mem_sdiff.mp hx).2 (Finset.mem_sdiff.mp hy).1)
  have hpT : Union.union (SDiff.sdiff T S) (Inter.inter S T) = T := by
    rw [Finset.inter_comm S T]
    exact Finset.sdiff_union_inter T S
  have h1 : (SDiff.sdiff S T).card + (Inter.inter S T).card = S.card := by
    rw [<- Finset.card_union_of_disjoint hd1, Finset.sdiff_union_inter]
  have h2 : (SDiff.sdiff T S).card + (Inter.inter S T).card = T.card := by
    rw [<- Finset.card_union_of_disjoint hd2, hpT]
  have h3 : (symmDiff S T).card = (SDiff.sdiff S T).card + (SDiff.sdiff T S).card := by
    rw [Finset.symmDiff_def, Finset.card_union_of_disjoint hd3]
  omega

theorem native_positive_square_factor_cancel (a c : Nat) (hc : 0 < c) :
    IsSquare (a * c ^ 2) <-> IsSquare a := by
  constructor
  . intro h
    choose k hk using h
    have hd : Dvd.dvd (c ^ 2) (k ^ 2) := by
      refine Exists.intro a ?_
      calc
        k ^ 2 = k * k := by rw [pow_two]
        _ = a * c ^ 2 := hk.symm
        _ = c ^ 2 * a := mul_comm _ _
    have hck : Dvd.dvd c k := (Nat.pow_dvd_pow_iff (by decide : Not (2 = 0))).mp hd
    choose u hu using hck
    refine Exists.intro u ?_
    have heq : (c * c) * a = (c * c) * (u * u) := by
      calc
        _ = a * c ^ 2 := by ring
        _ = k * k := hk
        _ = (c * u) * (c * u) := by rw [hu]
        _ = _ := by ring
    exact Nat.eq_of_mul_eq_mul_left (Nat.mul_pos hc hc) heq
  . intro h
    choose k hk using h
    refine Exists.intro (k * c) ?_
    rw [hk]
    ring

theorem native_mask_symmDiff_right_cancel {I : Type*} [DecidableEq I]
    (S T C : Finset I) (h : symmDiff S C = symmDiff T C) : S = T := by
  have hh := congrArg (fun V : Finset I => symmDiff V C) h
  simpa only [symmDiff_symmDiff_cancel_right] using hh

theorem native_mask_symmDiff_left_injective {I : Type*} [DecidableEq I]
    (S : Finset I) : Function.Injective (fun T : Finset I => symmDiff S T) := by
  intro T U h
  have hh := congrArg (fun V : Finset I => symmDiff S V) h
  simpa only [symmDiff_symmDiff_cancel_left] using hh

theorem native_mask_symmDiff_subset {I : Type*} [DecidableEq I]
    (S T G : Finset I) (hS : S <= G) (hT : T <= G) : symmDiff S T <= G := by
  intro x hx
  rcases Finset.mem_symmDiff.mp hx with h | h
  . exact hS h.1
  . exact hT h.1

theorem native_unsigned_row_symmDiff_square_factor
    (O T A B : Finset (Prod Nat Nat)) :
    nativeUnsignedRowProduct O T * nativeUnsignedRowProduct A B =
      nativeUnsignedRowProduct (symmDiff O A) (symmDiff T B) *
        ((Inter.inter O A).prod (fun e => e.1 * (e.2 - e.1)) *
          (Inter.inter T B).prod (fun e => e.2 * (e.2 - e.1))) ^ 2 := by
  have hL := native_mask_product_symmDiff_square_factor O A
    (fun e => e.1 * (e.2 - e.1))
  have hR := native_mask_product_symmDiff_square_factor T B
    (fun e => e.2 * (e.2 - e.1))
  calc
    _ = (O.prod (fun e => e.1 * (e.2 - e.1)) *
          A.prod (fun e => e.1 * (e.2 - e.1))) *
        (T.prod (fun e => e.2 * (e.2 - e.1)) *
          B.prod (fun e => e.2 * (e.2 - e.1))) := by unfold nativeUnsignedRowProduct; ring
    _ = ((symmDiff O A).prod (fun e => e.1 * (e.2 - e.1)) *
          (Inter.inter O A).prod (fun e => e.1 * (e.2 - e.1)) ^ 2) *
        ((symmDiff T B).prod (fun e => e.2 * (e.2 - e.1)) *
          (Inter.inter T B).prod (fun e => e.2 * (e.2 - e.1)) ^ 2) := by rw [hL, hR]
    _ = _ := by unfold nativeUnsignedRowProduct; ring

theorem native_unsigned_square_pair_symmDiff_closed (P : Finset Nat)
    (hP : forall p : Nat, Membership.mem P p -> Nat.Prime p)
    (O T A B : Finset (Prod Nat Nat))
    (hO : O <= nativePrimeVertexEdges P) (hT : T <= nativePrimeVertexEdges P)
    (h0 : IsSquare (nativeUnsignedRowProduct O T))
    (h1 : IsSquare (nativeUnsignedRowProduct A B)) :
    IsSquare (nativeUnsignedRowProduct (symmDiff O A) (symmDiff T B)) := by
  have hL : 0 < (Inter.inter O A).prod (fun e => e.1 * (e.2 - e.1)) := by
    apply Finset.prod_pos
    intro e he
    have hh := (native_gap_edges_mem_iff P e).mp (hO (Finset.mem_inter.mp he).1)
    exact Nat.mul_pos (hP e.1 hh.1).pos (Nat.sub_pos_of_lt hh.2.2)
  have hR : 0 < (Inter.inter T B).prod (fun e => e.2 * (e.2 - e.1)) := by
    apply Finset.prod_pos
    intro e he
    have hh := (native_gap_edges_mem_iff P e).mp (hT (Finset.mem_inter.mp he).1)
    exact Nat.mul_pos (hP e.2 hh.2.1).pos (Nat.sub_pos_of_lt hh.2.2)
  have hs := IsSquare.mul h0 h1
  rw [native_unsigned_row_symmDiff_square_factor O T A B] at hs
  exact (native_positive_square_factor_cancel _ _ (Nat.mul_pos hL hR)).mp hs

theorem native_even_row_pair_symmDiff_parity (O T A B : Finset (Prod Nat Nat))
    (h0 : (O.card + T.card) % 2 = 0) (h1 : (A.card + B.card) % 2 = 0) :
    ((symmDiff O A).card + (symmDiff T B).card) % 2 = 0 := by
  have hL := native_mask_card_symmDiff_double_inter O A
  have hR := native_mask_card_symmDiff_double_inter T B
  omega

end PrimeFactorOscillations.FiniteFieldIntegerSignature

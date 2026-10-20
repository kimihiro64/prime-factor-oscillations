/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/

import PrimeFactorOscillations.Assembly.DetectorPackets.QuadraticProductBand

/-!
# QuadraticDyadicBand

Maintained extraction of completed detector/packet proof components.
All original theorem hypotheses and retained proof bodies are preserved.
This module alone asserts no improved zero-free boundary.
-/

set_option autoImplicit false
set_option Elab.async false

/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described by LICENSE.
Authors: Prime Factor Oscillations contributors
-/


noncomputable section
open scoped BigOperators Classical

namespace PrimeFactorOscillations.QuadraticDyadicBand

open QuadraticProductBand

def dyadicBlock (i : Nat) : Finset Nat := Finset.Ico (2 ^ i) (2 * 2 ^ i)

def dyadicBox (i : Prod Nat Nat) : Finset (Prod Nat Nat) :=
  (dyadicBlock i.1).product (dyadicBlock i.2)

def indexBound (D : Nat) : Nat := (2 * D).log2 + 1

def dyadicIndices (D : Nat) : Finset (Prod Nat Nat) :=
  ((Finset.range (indexBound D)).product (Finset.range (indexBound D))).filter
    (fun i => D < 4 * (2 ^ i.1 * 2 ^ i.2) /\ 2 ^ i.1 * 2 ^ i.2 <= 2 * D)

theorem dyadicBlock_card (i : Nat) : (dyadicBlock i).card = 2 ^ i := by
  unfold dyadicBlock
  rw [Nat.card_Ico]
  omega

theorem dyadic_box_log (i p : Prod Nat Nat) (hp : Membership.mem (dyadicBox i) p) :
    Prod.mk p.1.log2 p.2.log2 = i := by
  have h := Finset.mem_product.mp hp
  have hu := Finset.mem_Ico.mp h.1
  have hv := Finset.mem_Ico.mp h.2
  have hu0 : 0 < p.1 := (Nat.pow_pos (by decide : 0 < (2 : Nat))).trans_le hu.1
  have hv0 : 0 < p.2 := (Nat.pow_pos (by decide : 0 < (2 : Nat))).trans_le hv.1
  apply Prod.ext
  . apply (Nat.log2_eq_iff (Nat.ne_of_gt hu0)).mpr
    refine And.intro hu.1 ?_
    simpa only [pow_succ, mul_comm] using hu.2
  . apply (Nat.log2_eq_iff (Nat.ne_of_gt hv0)).mpr
    refine And.intro hv.1 ?_
    simpa only [pow_succ, mul_comm] using hv.2

theorem dyadic_boxes_disjoint (I : Finset (Prod Nat Nat)) :
    (I : Set (Prod Nat Nat)).PairwiseDisjoint dyadicBox := by
  intro i hi j hj hne
  apply Finset.disjoint_left.mpr
  intro p hpi hpj
  exact hne ((dyadic_box_log i p hpi).symm.trans (dyadic_box_log j p hpj))

theorem factorBand_cover (D : Nat) (p : Prod Nat Nat)
    (hp : Membership.mem (factorBand D) p) :
    exists i, Membership.mem (dyadicIndices D) i /\ Membership.mem (dyadicBox i) p := by
  have h := Finset.mem_filter.mp hp
  have hpair := Finset.mem_product.mp h.1
  have hu := Finset.mem_Icc.mp hpair.1
  have hv := Finset.mem_Icc.mp hpair.2
  have hu0 : 0 < p.1 := hu.1
  have hv0 : 0 < p.2 := hv.1
  have hH : Not (2 * D = 0) :=
    Nat.ne_of_gt ((Nat.mul_pos hu0 hv0).trans_le h.2.2)
  have hlogu : p.1.log2 < indexBound D :=
    Nat.lt_succ_iff.mpr ((Nat.le_log2 hH).mpr
      ((Nat.log2_self_le (Nat.ne_of_gt hu0)).trans hu.2))
  have hlogv : p.2.log2 < indexBound D :=
    Nat.lt_succ_iff.mpr ((Nat.le_log2 hH).mpr
      ((Nat.log2_self_le (Nat.ne_of_gt hv0)).trans hv.2))
  have hLu : 2 ^ p.1.log2 <= p.1 := Nat.log2_self_le (Nat.ne_of_gt hu0)
  have hLv : 2 ^ p.2.log2 <= p.2 := Nat.log2_self_le (Nat.ne_of_gt hv0)
  have hUu : p.1 < 2 * 2 ^ p.1.log2 := by
    simpa only [pow_succ, mul_comm] using (Nat.lt_log2_self (n := p.1))
  have hUv : p.2 < 2 * 2 ^ p.2.log2 := by
    simpa only [pow_succ, mul_comm] using (Nat.lt_log2_self (n := p.2))
  have hprodlo : D < 4 * (2 ^ p.1.log2 * 2 ^ p.2.log2) := by
    apply h.2.1.trans
    calc
      _ <= p.1 * (2 * 2 ^ p.2.log2) := Nat.mul_le_mul_left _ hUv.le
      _ < (2 * 2 ^ p.1.log2) * (2 * 2 ^ p.2.log2) :=
        Nat.mul_lt_mul_of_pos_right hUu (by positivity)
      _ = _ := by ring
  have hprodhi : 2 ^ p.1.log2 * 2 ^ p.2.log2 <= 2 * D :=
    (Nat.mul_le_mul hLu hLv).trans h.2.2
  refine Exists.intro (Prod.mk p.1.log2 p.2.log2) (And.intro ?_ ?_)
  . apply Finset.mem_filter.mpr
    exact And.intro
      (Finset.mem_product.mpr (And.intro (Finset.mem_range.mpr hlogu)
        (Finset.mem_range.mpr hlogv))) (And.intro hprodlo hprodhi)
  . exact Finset.mem_product.mpr (And.intro
      (Finset.mem_Ico.mpr (And.intro hLu hUu))
      (Finset.mem_Ico.mpr (And.intro hLv hUv)))

theorem dyadicIndices_nonempty (D : Nat) (hD : 0 < D) : (dyadicIndices D).Nonempty := by
  have hp : Membership.mem (factorBand D) (Prod.mk 1 (D + 1)) := by
    apply Finset.mem_filter.mpr
    refine And.intro (Finset.mem_product.mpr (And.intro ?_ ?_)) ?_
    . exact Finset.mem_Icc.mpr (And.intro le_rfl (by omega))
    . exact Finset.mem_Icc.mpr (And.intro (by omega) (by omega))
    . simp only [one_mul]
      exact And.intro (by omega) (by omega)
  choose i hi hpoint using factorBand_cover D (Prod.mk 1 (D + 1)) hp
  exact Exists.intro i hi

theorem dyadicIndices_card (D : Nat) :
    (dyadicIndices D).card <= (indexBound D) ^ 2 := by
  calc
    _ <= ((Finset.range (indexBound D)).product (Finset.range (indexBound D))).card :=
      Finset.card_filter_le _ _
    _ = (Finset.range (indexBound D)).card * (Finset.range (indexBound D)).card :=
      Finset.card_product _ _
    _ = _ := by rw [Finset.card_range]; ring

theorem factorBand_sum_le_boxes (D : Nat) (F : Prod Nat Nat -> Real)
    (hF : forall p, 0 <= F p) :
    (factorBand D).sum F <=
      (dyadicIndices D).sum (fun i => (dyadicBox i).sum F) := by
  have hcover : factorBand D <= (dyadicIndices D).biUnion dyadicBox := by
    intro p hp
    choose i hi hpi using factorBand_cover D p hp
    exact Finset.mem_biUnion.mpr (Exists.intro i (And.intro hi hpi))
  calc
    _ <= ((dyadicIndices D).biUnion dyadicBox).sum F :=
      Finset.sum_le_sum_of_subset_of_nonneg hcover (fun p _ _ => hF p)
    _ = _ := Finset.sum_biUnion (dyadic_boxes_disjoint (dyadicIndices D))

end PrimeFactorOscillations.QuadraticDyadicBand

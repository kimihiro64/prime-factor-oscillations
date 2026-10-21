/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Finset.Max
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Nat.Find

/-!
# Exact finite integer moment compression

The integer transfer between equal disjoint subset signatures preserves
all moments and strictly reduces the positive support. This supplies the
finite reduction step for sparse positive prime carriers.
-/

set_option autoImplicit false
set_option Elab.async false

namespace Finset

variable {I K : Type*} [Fintype I]

def positiveWeightSupport (w : I -> Nat) : Finset I :=
  Finset.univ.filter (fun i => 0 < w i)

def natWeightedMoment (v : I -> K -> Nat) (w : I -> Nat) (k : K) : Nat :=
  Finset.univ.sum (fun i => w i * v i k)

theorem mem_positiveWeightSupport (w : I -> Nat) (i : I) :
    Membership.mem (positiveWeightSupport w) i <-> 0 < w i := by
  simp [positiveWeightSupport]

private theorem sum_univ_ite_mem_eq [DecidableEq I] (A : Finset I) (f : I -> Nat) :
    Finset.univ.sum (fun i => if Membership.mem A i then f i else 0) = A.sum f := by
  classical
  symm
  calc
    A.sum f = A.sum (fun i => if Membership.mem A i then f i else 0) := by
      apply Finset.sum_congr rfl
      intro i hi
      simp only [ite_eq_left hi]
    _ = Finset.univ.sum (fun i => if Membership.mem A i then f i else 0) := by
      apply Finset.sum_subset (Finset.subset_univ A)
      intro i _ hi
      simp only [ite_eq_right hi]

/-- An exact transfer between disjoint equal signatures reduces support. -/
theorem exists_nat_weight_reduction (v : I -> K -> Nat) (w : I -> Nat)
    (A B : Finset I) (hA : A.Nonempty)
    (hAs : forall {i : I}, Membership.mem A i -> Membership.mem (positiveWeightSupport w) i)
    (hBs : forall {i : I}, Membership.mem B i -> Membership.mem (positiveWeightSupport w) i)
    (hd : Disjoint A B)
    (hm : forall k, A.sum (fun i => v i k) = B.sum (fun i => v i k)) :
    Exists (fun w' : I -> Nat =>
      And (forall k, natWeightedMoment v w' k = natWeightedMoment v w k)
        ((positiveWeightSupport w').card < (positiveWeightSupport w).card)) := by
  classical
  let ex := Finset.exists_min_image A w hA
  let i0 := ex.choose
  have hi0 : Membership.mem A i0 := ex.choose_spec.1
  have hmin : forall i, Membership.mem A i -> w i0 <= w i := ex.choose_spec.2
  let t := w i0
  let w' : I -> Nat := fun i =>
    if Membership.mem A i then w i - t else
      if Membership.mem B i then w i + t else w i
  have hbalance (i : I) :
      w' i + (if Membership.mem A i then t else 0) =
        w i + (if Membership.mem B i then t else 0) := by
    by_cases ha : Membership.mem A i
    next =>
      have hb : Not (Membership.mem B i) := fun h => Finset.disjoint_left.mp hd ha h
      simp only [w', ite_eq_left ha, ite_eq_right hb, add_zero]
      exact Nat.sub_add_cancel (hmin i ha)
    next =>
      by_cases hb : Membership.mem B i <;> simp [w', ha, hb]
  have hmoment : forall k, natWeightedMoment v w' k = natWeightedMoment v w k := by
    intro k
    have hpoint (i : I) :
        w' i * v i k + (if Membership.mem A i then t * v i k else 0) =
          w i * v i k + (if Membership.mem B i then t * v i k else 0) := by
      have h := congrArg (fun n : Nat => n * v i k) (hbalance i)
      by_cases ha : Membership.mem A i <;>
        by_cases hb : Membership.mem B i <;> simpa [ha, hb, add_mul] using h
    have hsum := Finset.sum_congr (rfl : Finset.univ = Finset.univ)
      (fun i _ => hpoint i)
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib,
      sum_univ_ite_mem_eq A, sum_univ_ite_mem_eq B,
      <- Finset.mul_sum, <- Finset.mul_sum, hm k] at hsum
    exact Nat.add_right_cancel hsum
  have hsub : forall {i : I}, Membership.mem (positiveWeightSupport w') i ->
      Membership.mem (positiveWeightSupport w) i := by
    intro i hi
    by_cases ha : Membership.mem A i
    next => exact hAs ha
    next =>
      by_cases hb : Membership.mem B i
      next => exact hBs hb
      next =>
        apply (mem_positiveWeightSupport w i).mpr
        have hp := (mem_positiveWeightSupport w' i).mp hi
        simpa [w', ha, hb] using hp
  have hzero : w' i0 = 0 := by simp [w', hi0, t]
  have hne : Not (positiveWeightSupport w' = positiveWeightSupport w) := by
    intro he
    have hi : Membership.mem (positiveWeightSupport w') i0 := by
      rw [he]
      exact hAs hi0
    have hp := (mem_positiveWeightSupport w' i0).mp hi
    rw [hzero] at hp
    exact Nat.lt_irrefl 0 hp
  exact Exists.intro w' (And.intro hmoment
    (Finset.card_lt_card (Finset.ssubset_iff_subset_ne.mpr (And.intro (@hsub) hne))))

omit [Fintype I] in
private theorem sum_diff_add_inter [DecidableEq I] (A B : Finset I) (f : I -> Nat) :
    (SDiff.sdiff A B).sum f + (Inter.inter A B).sum f = A.sum f := by
  have he : SDiff.sdiff A (Inter.inter A B) = SDiff.sdiff A B := by
    ext i
    simp only [Finset.mem_sdiff, Finset.mem_inter]
    constructor
    next =>
      intro h
      exact And.intro h.1 (fun hb => h.2 (And.intro h.1 hb))
    next =>
      intro h
      exact And.intro h.1 (fun hi => h.2 hi.2)
  have hC : forall {i : I}, Membership.mem (Inter.inter A B) i -> Membership.mem A i :=
    fun hi => (Finset.mem_inter.mp hi).1
  have hs := Finset.sum_sdiff (f := f) (@hC)
  rw [he] at hs
  exact hs

/-- Exact integer representatives can be chosen with no subset-signature collision. -/
theorem exists_nat_weights_subset_signature_injective (v : I -> K -> Nat) :
    Exists (fun w : I -> Nat =>
      And (forall k, natWeightedMoment v w k = Finset.univ.sum (fun i => v i k))
        (forall A B : Finset I,
          (forall {i : I}, Membership.mem A i -> Membership.mem (positiveWeightSupport w) i) ->
          (forall {i : I}, Membership.mem B i -> Membership.mem (positiveWeightSupport w) i) ->
          (forall k, A.sum (fun i => v i k) = B.sum (fun i => v i k)) -> A = B)) := by
  classical
  let P : Nat -> Prop := fun n => Exists (fun w : I -> Nat =>
    And (forall k, natWeightedMoment v w k = Finset.univ.sum (fun i => v i k))
      ((positiveWeightSupport w).card = n))
  have hex : Exists P := by
    refine Exists.intro (positiveWeightSupport (fun _ : I => 1)).card
      (Exists.intro (fun _ : I => 1) (And.intro ?_ rfl))
    intro k
    simp only [natWeightedMoment, one_mul]
  let spec := Nat.find_spec hex
  let w := spec.choose
  have hw : forall k, natWeightedMoment v w k = Finset.univ.sum (fun i => v i k) :=
    spec.choose_spec.1
  have hcard : (positiveWeightSupport w).card = Nat.find hex := spec.choose_spec.2
  refine Exists.intro w (And.intro hw ?_)
  intro A B hAs hBs hm
  by_contra hne
  let A0 : Finset I := SDiff.sdiff A B
  let B0 : Finset I := SDiff.sdiff B A
  have hAs0 : forall {i : I}, Membership.mem A0 i -> Membership.mem (positiveWeightSupport w) i :=
    fun hi => hAs (Finset.mem_sdiff.mp hi).1
  have hBs0 : forall {i : I}, Membership.mem B0 i -> Membership.mem (positiveWeightSupport w) i :=
    fun hi => hBs (Finset.mem_sdiff.mp hi).1
  have hd : Disjoint A0 B0 := by
    apply Finset.disjoint_left.mpr
    intro i hi hj
    exact (Finset.mem_sdiff.mp hi).2 (Finset.mem_sdiff.mp hj).1
  have hm0 : forall k, A0.sum (fun i => v i k) = B0.sum (fun i => v i k) := by
    intro k
    have h1 := sum_diff_add_inter A B (fun i => v i k)
    have h2 := sum_diff_add_inter B A (fun i => v i k)
    rw [Finset.inter_comm B A] at h2
    rw [hm k] at h1
    exact Nat.add_right_cancel (h1.trans h2.symm)
  have reduce (U V : Finset I) (hU : U.Nonempty)
      (hUs : forall {i : I}, Membership.mem U i -> Membership.mem (positiveWeightSupport w) i)
      (hVs : forall {i : I}, Membership.mem V i -> Membership.mem (positiveWeightSupport w) i)
      (hUV : Disjoint U V)
      (hM : forall k, U.sum (fun i => v i k) = V.sum (fun i => v i k)) : False := by
    let ex := exists_nat_weight_reduction v w U V hU (@hUs) (@hVs) hUV hM
    let w0 := ex.choose
    have hm0w : forall k, natWeightedMoment v w0 k = Finset.univ.sum (fun i => v i k) :=
      fun k => (ex.choose_spec.1 k).trans (hw k)
    have hP : P (positiveWeightSupport w0).card :=
      Exists.intro w0 (And.intro hm0w rfl)
    have hle := Nat.find_min' hex hP
    have hlt : (positiveWeightSupport w0).card < Nat.find hex :=
      lt_of_lt_of_le ex.choose_spec.2 hcard.le
    exact (not_lt_of_ge hle) hlt
  by_cases hA0 : A0.Nonempty
  next => exact reduce A0 B0 hA0 (@hAs0) (@hBs0) hd hm0
  next =>
    have hB0 : B0.Nonempty := by
      apply Finset.nonempty_iff_ne_empty.mpr
      intro hzero
      have hAz : A0 = EmptyCollection.emptyCollection :=
        Finset.not_nonempty_iff_eq_empty.mp hA0
      have hab (i : I) (hi : Membership.mem A i) : Membership.mem B i :=
        (Finset.sdiff_eq_empty_iff_subset.mp hAz) hi
      have hba (i : I) (hi : Membership.mem B i) : Membership.mem A i :=
        (Finset.sdiff_eq_empty_iff_subset.mp hzero) hi
      apply hne
      apply Finset.ext
      intro i
      exact Iff.intro (fun hi => hab i hi) (fun hi => hba i hi)
    exact reduce B0 A0 hB0 (@hBs0) (@hAs0) hd.symm (fun k => (hm0 k).symm)

/-- Integer moment representatives have support bounded by the subset-signature box. -/
theorem exists_nat_weights_card_pow_le [Fintype K] (v : I -> K -> Nat) :
    Exists (fun w : I -> Nat =>
      And (forall k, natWeightedMoment v w k = Finset.univ.sum (fun i => v i k))
        (2 ^ (positiveWeightSupport w).card <=
          Finset.univ.prod (fun k => Finset.univ.sum (fun i => v i k) + 1))) := by
  classical
  let ex := exists_nat_weights_subset_signature_injective v
  let w := ex.choose
  have hm := ex.choose_spec.1
  have hi := ex.choose_spec.2
  let enc :
      { A : Finset I // Membership.mem (positiveWeightSupport w).powerset A } ->
        ((k : K) -> Fin (Finset.univ.sum (fun i => v i k) + 1)) :=
    fun A k => Fin.mk (A.val.sum (fun i => v i k))
      (Nat.lt_succ_of_le (Finset.sum_le_sum_of_subset_of_nonneg
        (Finset.subset_univ A.val) (fun i _ _ => Nat.zero_le (v i k))))
  have henc : Function.Injective enc := by
    intro A B hab
    apply Subtype.ext
    apply hi A.val B.val
    next =>
      intro i hai
      exact (Finset.mem_powerset.mp A.property) hai
    next =>
      intro i hbi
      exact (Finset.mem_powerset.mp B.property) hbi
    next =>
      intro k
      exact congrArg (fun z => (z k).val) hab
  have hcard := Fintype.card_le_of_injective enc henc
  have hdom :
      Fintype.card { A : Finset I //
        Membership.mem (positiveWeightSupport w).powerset A } =
          2 ^ (positiveWeightSupport w).card := by
    rw [Fintype.card_coe, Finset.card_powerset]
  have hcod :
      Fintype.card ((k : K) -> Fin (Finset.univ.sum (fun i => v i k) + 1)) =
        Finset.univ.prod (fun k => Finset.univ.sum (fun i => v i k) + 1) := by
    simp only [Fintype.card_pi, Fintype.card_fin]
  rw [hdom, hcod] at hcard
  exact Exists.intro w (And.intro hm hcard)

end Finset

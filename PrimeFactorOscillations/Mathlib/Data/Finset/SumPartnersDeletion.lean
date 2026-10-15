/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Mathlib.Data.Finset.DeletionCodegree
import PrimeFactorOscillations.Mathlib.Data.Finset.SumPartners

/-!
# Joint control of failed sum targets after deleting inputs

The degree counts only missing inputs that actually represent the target.
The common-neighbor hypothesis concerns the complete intersection of two
representation sets. No prime distribution hypothesis is encoded as an axiom.
-/

set_option autoImplicit false
set_option Elab.async false

namespace Finset

theorem card_sumPartners_le_twice_deleted_add_one (P S : Finset Nat) (n : Nat)
    (hMissing : Not (exists p, exists q, And (Membership.mem S p)
      (And (Membership.mem S q) (And (Not (p = q)) (p + q = n))))) :
    (sumPartners P n).card <= 2 * (SDiff.sdiff (sumPartners P n) S).card + 1 := by
  classical
  let D := SDiff.sdiff (sumPartners P n) S
  have hCover : sumPartners P n <= Union.union (Union.union D (D.image (fun p => n - p))) {n / 2} := by
    intro p hp
    have hpd := Finset.mem_filter.mp hp
    by_cases hpS : Membership.mem S p
    next =>
      by_cases hqS : Membership.mem S (n - p)
      next =>
        have heq : p = n - p := by
          by_contra hne
          exact hMissing (Exists.intro p (Exists.intro (n - p)
            (And.intro hpS (And.intro hqS (And.intro hne (by omega))))))
        exact Finset.mem_union_right _ (Finset.mem_singleton.mpr (by omega))
      next =>
        have hqP : Membership.mem (sumPartners P n) (n - p) := by
          apply Finset.mem_filter.mpr
          refine And.intro hpd.2.1 (And.intro ?_ ?_)
          next => simpa only [Nat.sub_sub_self hpd.2.2] using hpd.1
          next => exact Nat.sub_le _ _
        have hqD : Membership.mem D (n - p) :=
          Finset.mem_sdiff.mpr (And.intro hqP hqS)
        have hi : Membership.mem (D.image (fun q => n - q)) p :=
          Finset.mem_image.mpr (Exists.intro (n - p) (And.intro hqD (by omega)))
        exact Finset.mem_union_left _ (Finset.mem_union_right _ hi)
    next =>
      exact Finset.mem_union_left _ (Finset.mem_union_left _
        (Finset.mem_sdiff.mpr (And.intro hp hpS)))
  have hCard := Finset.card_le_card hCover
  have hUnion := Finset.card_union_le (Union.union D (D.image (fun p => n - p))) {n / 2}
  have hInner := Finset.card_union_le D (D.image (fun p => n - p))
  have hImage := Finset.card_image_le (s := D) (f := fun p => n - p)
  have hSingle : ({n / 2} : Finset Nat).card = 1 := Finset.card_singleton _
  dsimp [D] at *
  omega

theorem failed_sum_target_card_le (P S B : Finset Nat) (L K : Real)
    (hL : 0 < L) (hK : 0 <= K)
    (hRepresentations : forall n, Membership.mem B n ->
      L + 1 <= ((sumPartners P n).card : Real))
    (hMissing : forall n, Membership.mem B n ->
      Not (exists p, exists q, And (Membership.mem S p)
        (And (Membership.mem S q) (And (Not (p = q)) (p + q = n)))))
    (hCross : forall n, Membership.mem B n -> forall m, Membership.mem B m ->
      Not (m = n) -> ((Inter.inter (sumPartners P n) (sumPartners P m)).card : Real) <= K)
    (hSmall : 8 * ((SDiff.sdiff P S).card : Real) * K <= L ^ 2) :
    (B.card : Real) <= 8 * ((SDiff.sdiff P S).card : Real) * (P.card : Real) / L ^ 2 := by
  classical
  let w : Nat -> Nat -> Real := fun p n => if Membership.mem (sumPartners P n) p then 1 else 0
  have hSubset : forall n, sumPartners P n <= P := fun n p hp => (Finset.mem_filter.mp hp).1
  have hSum : forall n, Finset.sum (SDiff.sdiff P S) (fun p => w p n) =
      ((SDiff.sdiff (sumPartners P n) S).card : Real) := by
    intro n
    have hFilter : (SDiff.sdiff P S).filter (fun p => Membership.mem (sumPartners P n) p) =
        SDiff.sdiff (sumPartners P n) S := by
      ext p
      simp only [Finset.mem_filter, Finset.mem_sdiff]
      constructor
      next =>
        intro h
        exact And.intro h.2 h.1.2
      next =>
        intro h
        exact And.intro (And.intro (hSubset n h.1) h.2) h.1
    have h := Finset.sum_filter (s := SDiff.sdiff P S)
      (p := fun p => Membership.mem (sumPartners P n) p) (f := fun _ => (1 : Real))
    simpa only [hFilter, Finset.sum_const, nsmul_eq_mul, mul_one] using h.symm
  have hCover : forall n, Membership.mem B n ->
      L <= 2 * Finset.sum (SDiff.sdiff P S) (fun p => w p n) := by
    intro n hn
    rw [hSum]
    have h := card_sumPartners_le_twice_deleted_add_one P S n (hMissing n hn)
    have hr : ((sumPartners P n).card : Real) <=
        2 * ((SDiff.sdiff (sumPartners P n) S).card : Real) + 1 := by exact_mod_cast h
    have hRep := hRepresentations n hn
    linarith
  have hDiag : forall n, Membership.mem B n ->
      Finset.sum P (fun p => (w p n) ^ 2) <= (P.card : Real) := by
    intro n hn
    calc
      _ <= Finset.sum P (fun _ => (1 : Real)) := by
        apply Finset.sum_le_sum
        intro p hp
        dsimp [w]
        split_ifs <;> norm_num
      _ = _ := by simp
  have hCrossSum : forall n, Membership.mem B n -> forall m, Membership.mem B m ->
      Not (m = n) -> Finset.sum P (fun p => w p n * w p m) <= K := by
    intro n hn m hm hne
    have hFilter : P.filter (fun p =>
        Membership.mem (sumPartners P n) p /\ Membership.mem (sumPartners P m) p) =
        Inter.inter (sumPartners P n) (sumPartners P m) := by
      ext p
      simp only [Finset.mem_filter, Finset.mem_inter]
      constructor
      next => intro h; exact h.2
      next => intro h; exact And.intro (hSubset n h.1) h
    have hEq : Finset.sum P (fun p => w p n * w p m) =
        ((Inter.inter (sumPartners P n) (sumPartners P m)).card : Real) := by
      rw [<- hFilter]
      have h := Finset.sum_filter (s := P)
        (p := fun p => Membership.mem (sumPartners P n) p /\ Membership.mem (sumPartners P m) p)
        (f := fun _ => (1 : Real))
      rw [show ((P.filter (fun p => Membership.mem (sumPartners P n) p /\
          Membership.mem (sumPartners P m) p)).card : Real) =
          Finset.sum P (fun p => if Membership.mem (sumPartners P n) p /\
            Membership.mem (sumPartners P m) p then 1 else 0) by simpa using h]
      apply Finset.sum_congr rfl
      intro p hp
      dsimp [w]
      split_ifs <;> simp_all
    rw [hEq]
    exact hCross n hn m hm hne
  exact covered_target_card_le P (SDiff.sdiff P S) B
    (fun p hp => (Finset.mem_sdiff.mp hp).1) w L (P.card : Real) K hL
    (Nat.cast_nonneg _) hK hCover hDiag hCrossSum hSmall

theorem weighted_failed_sum_target_card_le (P S B : Finset Nat)
    (v : Nat -> Real) (L U K : Real) (hL : 0 < L) (hU : 0 <= U) (hK : 0 <= K)
    (hv : forall n, Membership.mem B n -> 0 <= v n)
    (hRepresentations : forall n, Membership.mem B n ->
      L + v n <= v n * ((sumPartners P n).card : Real))
    (hMissing : forall n, Membership.mem B n ->
      Not (exists p, exists q, And (Membership.mem S p)
        (And (Membership.mem S q) (And (Not (p = q)) (p + q = n)))))
    (hDiag : forall n, Membership.mem B n ->
      ((sumPartners P n).card : Real) * (v n) ^ 2 <= U)
    (hCross : forall n, Membership.mem B n -> forall m, Membership.mem B m ->
      Not (m = n) ->
      ((Inter.inter (sumPartners P n) (sumPartners P m)).card : Real) * (v n * v m) <= K)
    (hSmall : 8 * ((SDiff.sdiff P S).card : Real) * K <= L ^ 2) :
    (B.card : Real) <= 8 * ((SDiff.sdiff P S).card : Real) * U / L ^ 2 := by
  classical
  let w : Nat -> Nat -> Real := fun p n =>
    if Membership.mem (sumPartners P n) p then v n else 0
  have hSubset : forall n, sumPartners P n <= P := fun n p hp => (Finset.mem_filter.mp hp).1
  have hSum : forall n, Finset.sum (SDiff.sdiff P S) (fun p => w p n) =
      ((SDiff.sdiff (sumPartners P n) S).card : Real) * v n := by
    intro n
    have hFilter : (SDiff.sdiff P S).filter (fun p => Membership.mem (sumPartners P n) p) =
        SDiff.sdiff (sumPartners P n) S := by
      ext p
      simp only [Finset.mem_filter, Finset.mem_sdiff]
      constructor
      next => intro h; exact And.intro h.2 h.1.2
      next => intro h; exact And.intro (And.intro (hSubset n h.1) h.2) h.1
    have h := Finset.sum_filter (s := SDiff.sdiff P S)
      (p := fun p => Membership.mem (sumPartners P n) p) (f := fun _ => v n)
    simpa only [hFilter, Finset.sum_const, nsmul_eq_mul] using h.symm
  have hCover : forall n, Membership.mem B n ->
      L <= 2 * Finset.sum (SDiff.sdiff P S) (fun p => w p n) := by
    intro n hn
    rw [hSum]
    have h := card_sumPartners_le_twice_deleted_add_one P S n (hMissing n hn)
    have hr : ((sumPartners P n).card : Real) <=
        2 * ((SDiff.sdiff (sumPartners P n) S).card : Real) + 1 := by exact_mod_cast h
    have hw := mul_le_mul_of_nonneg_left hr (hv n hn)
    have hRep := hRepresentations n hn
    nlinarith
  have hDiagSum : forall n, Membership.mem B n ->
      Finset.sum P (fun p => (w p n) ^ 2) <= U := by
    intro n hn
    have hFilter : P.filter (fun p => Membership.mem (sumPartners P n) p) =
        sumPartners P n := by
      ext p
      simp only [Finset.mem_filter]
      constructor
      next => intro h; exact h.2
      next => intro h; exact And.intro (hSubset n h) h
    have hEq : Finset.sum P (fun p => (w p n) ^ 2) =
        ((sumPartners P n).card : Real) * (v n) ^ 2 := by
      have h := Finset.sum_filter (s := P)
        (p := fun p => Membership.mem (sumPartners P n) p) (f := fun _ => (v n) ^ 2)
      rw [hFilter] at h
      simp only [Finset.sum_const, nsmul_eq_mul] at h
      rw [h]
      apply Finset.sum_congr rfl
      intro p hp
      dsimp [w]
      split_ifs <;> simp
    rw [hEq]
    exact hDiag n hn
  have hCrossSum : forall n, Membership.mem B n -> forall m, Membership.mem B m ->
      Not (m = n) -> Finset.sum P (fun p => w p n * w p m) <= K := by
    intro n hn m hm hne
    have hFilter : P.filter (fun p =>
        Membership.mem (sumPartners P n) p /\ Membership.mem (sumPartners P m) p) =
        Inter.inter (sumPartners P n) (sumPartners P m) := by
      ext p
      simp only [Finset.mem_filter, Finset.mem_inter]
      constructor
      next => intro h; exact h.2
      next => intro h; exact And.intro (hSubset n h.1) h
    have hEq : Finset.sum P (fun p => w p n * w p m) =
        ((Inter.inter (sumPartners P n) (sumPartners P m)).card : Real) * (v n * v m) := by
      have h := Finset.sum_filter (s := P)
        (p := fun p => Membership.mem (sumPartners P n) p /\ Membership.mem (sumPartners P m) p)
        (f := fun _ => v n * v m)
      rw [hFilter] at h
      simp only [Finset.sum_const, nsmul_eq_mul] at h
      rw [h]
      apply Finset.sum_congr rfl
      intro p hp
      dsimp [w]
      split_ifs <;> simp_all
    rw [hEq]
    exact hCross n hn m hm hne
  exact covered_target_card_le P (SDiff.sdiff P S) B
    (fun p hp => (Finset.mem_sdiff.mp hp).1) w L U K hL hU hK hCover hDiagSum hCrossSum hSmall

theorem weighted_failed_sum_target_card_le_of_energy (P S B : Finset Nat)
    (v : Nat -> Real) (L U K : Real) (hL : 0 < L) (hU : 0 <= U)
    (hv : forall n, Membership.mem B n -> 0 <= v n)
    (hRepresentations : forall n, Membership.mem B n ->
      L + v n <= v n * ((sumPartners P n).card : Real))
    (hMissing : forall n, Membership.mem B n ->
      Not (exists p, exists q, And (Membership.mem S p)
        (And (Membership.mem S q) (And (Not (p = q)) (p + q = n)))))
    (hEnergy : Finset.sum P (fun p =>
      (Finset.sum B (fun n => if Membership.mem (sumPartners P n) p then v n else 0)) ^ 2) <=
      (B.card : Real) * U + (B.card : Real) ^ 2 * K)
    (hSmall : 8 * ((SDiff.sdiff P S).card : Real) * K <= L ^ 2) :
    (B.card : Real) <= 8 * ((SDiff.sdiff P S).card : Real) * U / L ^ 2 := by
  classical
  let w : Nat -> Nat -> Real := fun p n =>
    if Membership.mem (sumPartners P n) p then v n else 0
  have hSubset : forall n, sumPartners P n <= P := fun n p hp => (Finset.mem_filter.mp hp).1
  have hSum : forall n, Finset.sum (SDiff.sdiff P S) (fun p => w p n) =
      ((SDiff.sdiff (sumPartners P n) S).card : Real) * v n := by
    intro n
    have hFilter : (SDiff.sdiff P S).filter (fun p => Membership.mem (sumPartners P n) p) =
        SDiff.sdiff (sumPartners P n) S := by
      ext p
      simp only [Finset.mem_filter, Finset.mem_sdiff]
      constructor
      next => intro h; exact And.intro h.2 h.1.2
      next => intro h; exact And.intro (And.intro (hSubset n h.1) h.2) h.1
    have h := Finset.sum_filter (s := SDiff.sdiff P S)
      (p := fun p => Membership.mem (sumPartners P n) p) (f := fun _ => v n)
    simpa only [hFilter, Finset.sum_const, nsmul_eq_mul] using h.symm
  have hCover : forall n, Membership.mem B n ->
      L <= 2 * Finset.sum (SDiff.sdiff P S) (fun p => w p n) := by
    intro n hn
    rw [hSum]
    have h := card_sumPartners_le_twice_deleted_add_one P S n (hMissing n hn)
    have hr : ((sumPartners P n).card : Real) <=
        2 * ((SDiff.sdiff (sumPartners P n) S).card : Real) + 1 := by exact_mod_cast h
    have hw := mul_le_mul_of_nonneg_left hr (hv n hn)
    have hRep := hRepresentations n hn
    nlinarith

  exact covered_target_card_le_of_energy P (SDiff.sdiff P S) B
    (fun p hp => (Finset.mem_sdiff.mp hp).1) w L U K hL hU hCover hEnergy hSmall

end Finset

/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Assembly.FiniteFieldNativeCleanPacking
import PrimeFactorOscillations.Mathlib.Data.Nat.DivSquareTail

/-!
# Actual prime-pair packing with an exact square-divisor deletion allowance

The two endpoint sets are arbitrary finite prime sets satisfying the stated
height and separation conditions. The positive product supply and the full
square-divisor deletion allowance occur in the same natural-number inequality.
-/

set_option autoImplicit false
set_option Elab.async false

namespace PrimeFactorOscillations.FiniteFieldIntegerSignature

theorem native_height_square_tail_packing (A B : Finset Nat) (Y T : Nat)
    (hT : 2 <= T)
    (hA : forall n : Nat, Membership.mem A n -> Nat.Prime n /\ Y < 2 * n)
    (hB : forall q : Nat, Membership.mem B q -> Nat.Prime q /\ q <= Y)
    (hAB : forall n : Nat, Membership.mem A n ->
      forall q : Nat, Membership.mem B q -> n < q) :
    exists M : Finset (Prod Nat Nat),
      (forall a : Prod Nat Nat, Membership.mem M a ->
        Membership.mem A a.1 /\ Membership.mem B (a.1 + a.2) /\
          0 < a.2 /\ a.2 < a.1) /\
      A.card * B.card <= 2 * (T - 1) * M.card + A.card * (Y / (T - 1)) /\
      forall a : Prod Nat Nat, Membership.mem M a ->
        forall b : Prod Nat Nat, Membership.mem M b -> Not (a = b) ->
          nativeAgreementRate a.1 a.2 b.1 b.2 = 3 / 8 := by
  classical
  let f : Prod Nat Nat -> Prod Nat Nat := fun z => Prod.mk z.1 (z.2 - z.1)
  let S := (A.product B).image f
  have hcoords (a : Prod Nat Nat) (ha : Membership.mem S a) :
      Membership.mem A a.1 /\ Membership.mem B (a.1 + a.2) /\
        0 < a.2 /\ a.2 < a.1 /\ a.2 <= Y := by
    choose z hz he using Finset.mem_image.mp ha
    have hzAB := Finset.mem_product.mp hz
    have hlt := hAB z.1 hzAB.1 z.2 hzAB.2
    have hheight := (hA z.1 hzAB.1).2
    have hupper := (hB z.2 hzAB.2).2
    have he1 : z.1 = a.1 := by
      have hp := congrArg (fun t : Prod Nat Nat => t.1) he
      exact hp
    have he2 : z.2 - z.1 = a.2 := by
      have hp := congrArg (fun t : Prod Nat Nat => t.2) he
      exact hp
    have hsum : a.1 + a.2 = z.2 := by omega
    have haA : Membership.mem A a.1 := by rw [<- he1]; exact hzAB.1
    refine And.intro haA ?_
    have haB : Membership.mem B (a.1 + a.2) := by rw [hsum]; exact hzAB.2
    refine And.intro haB ?_
    omega
  have hinj : Set.InjOn f (fun a => Membership.mem (A.product B) a) := by
    intro a ha b hb he
    have haAB := Finset.mem_product.mp ha
    have hbAB := Finset.mem_product.mp hb
    have hal := hAB a.1 haAB.1 a.2 haAB.2
    have hbl := hAB b.1 hbAB.1 b.2 hbAB.2
    have he1 : a.1 = b.1 := by
      have hp := congrArg (fun t : Prod Nat Nat => t.1) he
      exact hp
    have he2 : a.2 - a.1 = b.2 - b.1 := by
      have hp := congrArg (fun t : Prod Nat Nat => t.2) he
      exact hp
    exact Prod.ext he1 (by omega)
  have hcard : S.card = A.card * B.card := by
    dsimp only [S]
    rw [Finset.card_image_iff.mpr hinj]
    exact Finset.card_product A B
  let Q : Nat -> Finset (Prod Nat Nat) := fun u =>
    S.filter (fun a => Dvd.dvd (u ^ 2) a.2)
  have hQ (u : Nat) (huT : T <= u) :
      (Q u).card <= A.card * (Y / (u * u)) := by
    have hu : 0 < u := by omega
    have huu : 0 < u * u := Nat.mul_pos hu hu
    let g : Prod Nat Nat -> Prod Nat Nat := fun a => Prod.mk a.1 (a.2 / (u * u))
    have hc : (Q u).card <= (A.product (Finset.Icc 1 (Y / (u * u)))).card := by
      apply Finset.card_le_card_of_injOn g
      . intro a ha
        have haS := (Finset.mem_filter.mp ha).1
        have haC := hcoords a haS
        have hd : Dvd.dvd (u * u) a.2 := by
          simpa only [pow_two] using (Finset.mem_filter.mp ha).2
        have hpos : 0 < a.2 / (u * u) :=
          Nat.div_pos (Nat.le_of_dvd haC.2.2.1 hd) huu
        apply Finset.mem_product.mpr
        refine And.intro haC.1 ?_
        exact Finset.mem_Icc.mpr (And.intro hpos (Nat.div_le_div_right haC.2.2.2.2))
      . intro a ha b hb he
        have hda : Dvd.dvd (u * u) a.2 := by
          simpa only [pow_two] using (Finset.mem_filter.mp ha).2
        have hdb : Dvd.dvd (u * u) b.2 := by
          simpa only [pow_two] using (Finset.mem_filter.mp hb).2
        have he1 : a.1 = b.1 := by
          have hp := congrArg (fun t : Prod Nat Nat => t.1) he
          exact hp
        have he2 : a.2 / (u * u) = b.2 / (u * u) := by
          have hp := congrArg (fun t : Prod Nat Nat => t.2) he
          exact hp
        have heh : a.2 = b.2 := by
          calc
            a.2 = a.2 / (u * u) * (u * u) := (Nat.div_mul_cancel hda).symm
            _ = b.2 / (u * u) * (u * u) := by rw [he2]
            _ = b.2 := Nat.div_mul_cancel hdb
        exact Prod.ext he1 heh
    calc
      (Q u).card <= (A.product (Finset.Icc 1 (Y / (u * u)))).card := hc
      _ = A.card * (Finset.Icc 1 (Y / (u * u))).card :=
        Finset.card_product A (Finset.Icc 1 (Y / (u * u)))
      _ = A.card * (Y / (u * u)) := by
        simp only [Nat.card_Icc, Nat.add_sub_cancel]
  let C := S.filter (fun a => forall u : Nat, T <= u -> Not (Dvd.dvd (u ^ 2) a.2))
  let D := S.filter (fun a => exists u : Nat, T <= u /\ Dvd.dvd (u ^ 2) a.2)
  have hDcover : forall a : Prod Nat Nat, Membership.mem D a ->
      Membership.mem ((Finset.Ico T (Y + 1)).biUnion Q) a := by
    intro a ha
    have haS := (Finset.mem_filter.mp ha).1
    choose u hu hd using (Finset.mem_filter.mp ha).2
    have haC := hcoords a haS
    have hs : u ^ 2 <= a.2 := Nat.le_of_dvd haC.2.2.1 hd
    have huY : u <= Y := by nlinarith [haC.2.2.2.2]
    exact Finset.mem_biUnion.mpr (Exists.intro u
      (And.intro (Finset.mem_Ico.mpr (And.intro hu (by omega)))
        (Finset.mem_filter.mpr (And.intro haS hd))))
  have hD : D.card <= A.card * (Y / (T - 1)) := by
    calc
      D.card <= ((Finset.Ico T (Y + 1)).biUnion Q).card :=
        Finset.card_le_card hDcover
      _ <= Finset.sum (Finset.Ico T (Y + 1)) (fun u => (Q u).card) :=
        Finset.card_biUnion_le
      _ <= Finset.sum (Finset.Ico T (Y + 1)) (fun u => A.card * (Y / (u * u))) := by
        apply Finset.sum_le_sum
        intro u hu
        exact hQ u (Finset.mem_Ico.mp hu).1
      _ = A.card * Finset.sum (Finset.Ico T (Y + 1)) (fun u => Y / (u * u)) := by
        rw [Finset.mul_sum]
      _ <= A.card * (Y / (T - 1)) :=
        Nat.mul_le_mul_left A.card (Nat.sum_Ico_div_sq_le Y T (Y + 1) hT)
  have hsplit : S.card <= C.card + D.card := by
    have hcover : forall a : Prod Nat Nat, Membership.mem S a ->
        Membership.mem (Union.union C D) a := by
      intro a ha
      by_cases hg : forall u : Nat, T <= u -> Not (Dvd.dvd (u ^ 2) a.2)
      . exact Finset.mem_union.mpr
          (Or.inl (Finset.mem_filter.mpr (And.intro ha hg)))
      . have hex : exists u : Nat, T <= u /\ Dvd.dvd (u ^ 2) a.2 := by
          by_contra hn
          apply hg
          intro u hu hd
          exact hn (Exists.intro u (And.intro hu hd))
        exact Finset.mem_union.mpr
          (Or.inr (Finset.mem_filter.mpr (And.intro ha hex)))
    exact (Finset.card_le_card hcover).trans (Finset.card_union_le C D)
  have hprimeC : forall a : Prod Nat Nat, Membership.mem C a ->
      Nat.Prime a.1 /\ Nat.Prime (a.1 + a.2) /\ 0 < a.2 /\ a.2 < a.1 := by
    intro a ha
    have hc := hcoords a (Finset.mem_filter.mp ha).1
    exact And.intro (hA a.1 hc.1).1
      (And.intro (hB (a.1 + a.2) hc.2.1).1 (And.intro hc.2.2.1 hc.2.2.2.1))
  have hcleanC : forall a : Prod Nat Nat, Membership.mem C a ->
      forall u : Nat, T <= u -> Not (Dvd.dvd (u ^ 2) a.2) := by
    intro a ha
    exact (Finset.mem_filter.mp ha).2
  choose M hsub hMC hRate using native_clean_gap_packing C T hprimeC hcleanC
  refine Exists.intro M (And.intro ?_ (And.intro ?_ hRate))
  . intro a ha
    have hc := hcoords a (Finset.mem_filter.mp (hsub a ha)).1
    exact And.intro hc.1 (And.intro hc.2.1 (And.intro hc.2.2.1 hc.2.2.2.1))
  . rw [<- hcard]
    exact hsplit.trans (Nat.add_le_add hMC hD)

end PrimeFactorOscillations.FiniteFieldIntegerSignature

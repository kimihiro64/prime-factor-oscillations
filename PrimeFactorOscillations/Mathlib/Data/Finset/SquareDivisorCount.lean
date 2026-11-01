/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Finset.Union
import Mathlib.Tactic.Linarith
import PrimeFactorOscillations.Mathlib.Data.Nat.DivSquareTail

/-!
# A square-divisor deletion bound for finite fibres

Positive second coordinates are bounded by a common height. Dividing them
by a square gives an injective map on each divisor fibre. The full union
is controlled by the exact natural-quotient tail, without a rounding loss.
-/

set_option autoImplicit false
set_option Elab.async false

open scoped Classical

namespace Finset

/-- The complete square-divisor tail in bounded positive fibres. -/
theorem card_filter_exists_sq_dvd_le
    (S : Finset (Prod Nat Nat)) (A : Finset Nat) (Y T : Nat)
    (hT : 2 <= T)
    (hS : forall a : Prod Nat Nat, Membership.mem S a ->
      Membership.mem A a.1 /\ 0 < a.2 /\ a.2 <= Y) :
    (S.filter (fun (a : Prod Nat Nat) => exists u : Nat, T <= u /\ Dvd.dvd (u ^ 2) a.2)).card <=
      A.card * (Y / (T - 1)) := by
  classical
  let Q : Nat -> Finset (Prod Nat Nat) := fun u =>
    S.filter (fun (a : Prod Nat Nat) => Dvd.dvd (u ^ 2) a.2)
  have hQ (u : Nat) (huT : T <= u) :
      (Q u).card <= A.card * (Y / (u * u)) := by
    have hu : 0 < u := by omega
    have huu : 0 < u * u := Nat.mul_pos hu hu
    let g : Prod Nat Nat -> Prod Nat Nat := fun a => Prod.mk a.1 (a.2 / (u * u))
    have hc : (Q u).card <= (A.product (Finset.Icc 1 (Y / (u * u)))).card := by
      apply Finset.card_le_card_of_injOn g
      . intro a ha
        have haS := (Finset.mem_filter.mp ha).1
        have haC := hS a haS
        have hd : Dvd.dvd (u * u) a.2 := by
          simpa only [pow_two] using (Finset.mem_filter.mp ha).2
        have hpos : 0 < a.2 / (u * u) :=
          Nat.div_pos (Nat.le_of_dvd haC.2.1 hd) huu
        apply Finset.mem_product.mpr
        refine And.intro haC.1 ?_
        exact Finset.mem_Icc.mpr (And.intro hpos (Nat.div_le_div_right haC.2.2))
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
  let D := S.filter (fun (a : Prod Nat Nat) => exists u : Nat, T <= u /\ Dvd.dvd (u ^ 2) a.2)
  change D.card <= A.card * (Y / (T - 1))
  have hcover : forall a : Prod Nat Nat, Membership.mem D a ->
      Membership.mem ((Finset.Ico T (Y + 1)).biUnion Q) a := by
    intro a ha
    have haS := (Finset.mem_filter.mp ha).1
    choose u hu hd using (Finset.mem_filter.mp ha).2
    have haC := hS a haS
    have hs : u ^ 2 <= a.2 := Nat.le_of_dvd haC.2.1 hd
    have huY : u <= Y := by nlinarith [haC.2.2]
    exact Finset.mem_biUnion.mpr (Exists.intro u
      (And.intro (Finset.mem_Ico.mpr (And.intro hu (by omega)))
        (Finset.mem_filter.mpr (And.intro haS hd))))
  calc
    D.card <= ((Finset.Ico T (Y + 1)).biUnion Q).card :=
      Finset.card_le_card hcover
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

end Finset

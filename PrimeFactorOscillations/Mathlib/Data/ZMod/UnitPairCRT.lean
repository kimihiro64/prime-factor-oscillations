/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import Mathlib.Algebra.Group.Pi.Units
import Mathlib.Algebra.Group.Units.Equiv
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.ZMod.QuotientRing

/-! # Exact independent unit-pair patterns under the Chinese remainder theorem -/

set_option autoImplicit false
set_option Elab.async false

open scoped Classical

namespace ZMod

theorem card_unit_pair_crt_patterns {I : Type*} [Fintype I]
    (m : I -> Nat) [forall i : I, NeZero (m i)] [NeZero (Finset.univ.prod m)]
    (hc : Pairwise (fun i j : I => (m i).Coprime (m j)))
    (P : forall i : I, Prod (ZMod (m i)) (ZMod (m i)) -> Prop) :
    Fintype.card {ab : Prod (Units (ZMod (Finset.univ.prod m)))
        (Units (ZMod (Finset.univ.prod m))) // forall i : I,
      P i (((ZMod.prodEquivPi m hc) (ab.1 : ZMod (Finset.univ.prod m))) i,
        ((ZMod.prodEquivPi m hc) (ab.2 : ZMod (Finset.univ.prod m))) i)} =
    Finset.univ.prod (fun i : I => Fintype.card
      {ab : Prod (Units (ZMod (m i))) (Units (ZMod (m i))) //
        P i ((ab.1 : ZMod (m i)), (ab.2 : ZMod (m i)))}) := by
  let e : Equiv (Units (ZMod (Finset.univ.prod m)))
      (forall i : I, Units (ZMod (m i))) :=
    (Units.mapEquiv (ZMod.prodEquivPi m hc).toMulEquiv).toEquiv.trans
      MulEquiv.piUnits.toEquiv
  let A := {ab : Prod (Units (ZMod (Finset.univ.prod m)))
      (Units (ZMod (Finset.univ.prod m))) // forall i : I,
    P i ((e ab.1 i : ZMod (m i)), (e ab.2 i : ZMod (m i)))}
  let B := fun i : I => {ab : Prod (Units (ZMod (m i))) (Units (ZMod (m i))) //
    P i ((ab.1 : ZMod (m i)), (ab.2 : ZMod (m i)))}
  let E : Equiv A (forall i : I, B i) := {
    toFun := fun x i => Subtype.mk (Prod.mk (e x.val.1 i) (e x.val.2 i)) (x.property i)
    invFun := fun y => Subtype.mk
      (Prod.mk (e.symm (fun i => (y i).val.1)) (e.symm (fun i => (y i).val.2))) (by
        intro i
        change P i ((e (e.symm (fun j => (y j).val.1)) i : ZMod (m i)),
          (e (e.symm (fun j => (y j).val.2)) i : ZMod (m i)))
        rw [e.apply_symm_apply, e.apply_symm_apply]
        exact (y i).property)
    left_inv := by
      intro x
      apply Subtype.ext
      apply Prod.ext
      case fst => exact e.symm_apply_apply x.val.1
      case snd => exact e.symm_apply_apply x.val.2
    right_inv := by
      intro y
      funext i
      apply Subtype.ext
      change (e (e.symm (fun j => (y j).val.1)) i,
        e (e.symm (fun j => (y j).val.2)) i) = (y i).val
      rw [e.apply_symm_apply, e.apply_symm_apply]
  }
  change Fintype.card A = Finset.univ.prod (fun i => Fintype.card (B i))
  calc
    _ = Fintype.card (forall i : I, B i) := Fintype.card_congr E
    _ = _ := Fintype.card_pi

/-- Passing from reduced residue pairs to pairs of units preserves every
finite event count. -/
theorem card_unit_pair_event_eq_filter (q : Nat) [NeZero q]
    (P : Prod (ZMod q) (ZMod q) -> Prop) :
    ((Finset.univ.filter P).filter (fun ab => IsUnit ab.1 /\ IsUnit ab.2)).card =
      Fintype.card {ab : Prod (Units (ZMod q)) (Units (ZMod q)) //
        P ((ab.1 : ZMod q), (ab.2 : ZMod q))} := by
  let A := {ab : Prod (Units (ZMod q)) (Units (ZMod q)) //
    P ((ab.1 : ZMod q), (ab.2 : ZMod q))}
  let B := {ab : Prod (ZMod q) (ZMod q) // P ab /\ IsUnit ab.1 /\ IsUnit ab.2}
  let E : Equiv A B := {
    toFun := fun x => Subtype.mk (Prod.mk (x.val.1 : ZMod q) (x.val.2 : ZMod q))
      (And.intro x.property (And.intro x.val.1.isUnit x.val.2.isUnit))
    invFun := fun y => Subtype.mk
      (Prod.mk y.property.2.1.unit y.property.2.2.unit) (by
        simpa only [IsUnit.unit_spec, Prod.eta] using y.property.1)
    left_inv := by
      intro x
      apply Subtype.ext
      apply Prod.ext
      case fst =>
        apply Units.ext
        exact IsUnit.unit_spec _
      case snd =>
        apply Units.ext
        exact IsUnit.unit_spec _
    right_inv := by
      intro y
      apply Subtype.ext
      change (y.property.2.1.unit.val, y.property.2.2.unit.val) = y.val
      simp only [IsUnit.unit_spec, Prod.eta]
  }
  have hcard : ((Finset.univ.filter P).filter
      (fun ab => IsUnit ab.1 /\ IsUnit ab.2)).card = Fintype.card A := by
    calc
      _ = Fintype.card B := by
        rw [Fintype.card_subtype]
        simp only [Finset.filter_filter]
      _ = _ := (Fintype.card_congr E).symm
  exact hcard

theorem natCard_unit_pair_event_eq_filter (q : Nat) [NeZero q]
    (P : Prod (ZMod q) (ZMod q) -> Prop) :
    ((Finset.univ.filter P).filter (fun ab => IsUnit ab.1 /\ IsUnit ab.2)).card =
      Nat.card {ab : Prod (Units (ZMod q)) (Units (ZMod q)) //
        P ((ab.1 : ZMod q), (ab.2 : ZMod q))} := by
  rw [Nat.card_eq_fintype_card]
  exact card_unit_pair_event_eq_filter q P

theorem natCard_unit_pair_crt_patterns {I : Type*} [Fintype I]
    (m : I -> Nat) [forall i : I, NeZero (m i)] [NeZero (Finset.univ.prod m)]
    (hc : Pairwise (fun i j : I => (m i).Coprime (m j)))
    (P : forall i : I, Prod (ZMod (m i)) (ZMod (m i)) -> Prop) :
    Nat.card {ab : Prod (Units (ZMod (Finset.univ.prod m)))
        (Units (ZMod (Finset.univ.prod m))) // forall i : I,
      P i (((ZMod.prodEquivPi m hc) (ab.1 : ZMod (Finset.univ.prod m))) i,
        ((ZMod.prodEquivPi m hc) (ab.2 : ZMod (Finset.univ.prod m))) i)} =
    Finset.univ.prod (fun i : I => Nat.card
      {ab : Prod (Units (ZMod (m i))) (Units (ZMod (m i))) //
        P i ((ab.1 : ZMod (m i)), (ab.2 : ZMod (m i)))}) := by
  simp only [Nat.card_eq_fintype_card]
  exact card_unit_pair_crt_patterns m hc P

end ZMod

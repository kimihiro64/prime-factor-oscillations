/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Proof.PrimeClassDeletion.CappedPrimeWeights

/-!
# Actual finite prime coordinates ordered by ordinal rank

The rank value is used only under a bound by an actual finite prime count.
No infinitude assumption is imposed on the class. These coordinates feed
the complete capped-prime Bernoulli and odds comparisons.
-/

set_option autoImplicit false
set_option Elab.async false

namespace PrimeFactorOscillations.PrimeClassDeletion

open PrimeFactorOscillations.PrimeClassSampling

def primeClassValuePredicate (P : Set Nat) (p : Nat) : Prop :=
  And (Nat.Prime p) (Membership.mem P p)

noncomputable def primeClassRankValue (P : Set Nat) (r : Nat) : Nat :=
  Nat.nth (primeClassValuePredicate P) r

noncomputable def primeClassCoordinates {A : Type*} (P : Set Nat) (f : Nat -> A)
    (X : Nat) : List A :=
  List.ofFn (fun i : Fin (primeClassPrefix P X).card => f (primeClassRankValue P i.val))

theorem nat_count_eq_selectionCount (a : Nat -> Prop) [DecidablePred a] (n : Nat) :
    Nat.count a n = selectionCount a n := by
  classical
  rw [Nat.count_eq_card_filter_range, selectionCount_eq_card_selectionPrefix]
  apply congrArg Finset.card
  apply Finset.ext
  intro i
  simp only [selectionPrefix, Finset.mem_filter]

theorem selectionPrefix_primeClassValue_eq (P : Set Nat) (X : Nat) :
    selectionPrefix (primeClassValuePredicate P) (X + 1) = primeClassPrefix P X := by
  classical
  apply Finset.ext
  intro p
  simp only [selectionPrefix, primeClassPrefix, Finset.mem_filter, Finset.mem_range,
    Finset.mem_Icc]
  constructor
  case mp =>
    intro h
    have hp : Nat.Prime p := h.2.1
    exact And.intro (And.intro hp.two_le (by omega)) h.2
  case mpr =>
    intro h
    exact And.intro (by omega) h.2

theorem selectionCount_primeClassValue_eq (P : Set Nat) (X : Nat) :
    selectionCount (primeClassValuePredicate P) (X + 1) = (primeClassPrefix P X).card := by
  rw [selectionCount_eq_card_selectionPrefix, selectionPrefix_primeClassValue_eq]

theorem primeClassRankValue_eq_of_rank (P : Set Nat) (p r : Nat)
    (hp : Nat.Prime p) (hpP : Membership.mem P p)
    (hr : (primeClassPrefix P (p - 1)).card = r) :
    primeClassRankValue P r = p := by
  classical
  have hp1 : 1 <= p := Nat.le_of_lt hp.one_lt
  have hc : Nat.count (primeClassValuePredicate P) p = r := by
    rw [nat_count_eq_selectionCount]
    have h := selectionCount_primeClassValue_eq P (p - 1)
    rw [Nat.sub_add_cancel hp1] at h
    exact h.trans hr
  have h := Nat.nth_count (p := primeClassValuePredicate P) (n := p) (And.intro hp hpP)
  rw [hc] at h
  exact h

theorem primeClassRankValue_spec (P : Set Nat) (X r : Nat)
    (hr : r < (primeClassPrefix P X).card) :
    And (Nat.Prime (primeClassRankValue P r))
      (And (Membership.mem P (primeClassRankValue P r))
        (And (primeClassRankValue P r <= X)
          ((primeClassPrefix P (primeClassRankValue P r - 1)).card = r))) := by
  have hcount : r < selectionCount (primeClassValuePredicate P) (X + 1) := by
    rw [selectionCount_primeClassValue_eq]
    exact hr
  choose p hp using selection_rank_exists (primeClassValuePredicate P) (X + 1) r hcount
  have hprime : Nat.Prime p := hp.2.1.1
  have hpP : Membership.mem P p := hp.2.1.2
  have hp1 : 1 <= p := Nat.le_of_lt hprime.one_lt
  have hbefore : (primeClassPrefix P (p - 1)).card = r := by
    have h := selectionCount_primeClassValue_eq P (p - 1)
    rw [Nat.sub_add_cancel hp1] at h
    exact h.symm.trans hp.2.2
  have hvalue := primeClassRankValue_eq_of_rank P p r hprime hpP hbefore
  rw [hvalue]
  exact And.intro hprime (And.intro hpP (And.intro (by omega) hbefore))

theorem primeClassRankValue_injective_below (P : Set Nat) (X r s : Nat)
    (hr : r < (primeClassPrefix P X).card) (hs : s < (primeClassPrefix P X).card)
    (heq : primeClassRankValue P r = primeClassRankValue P s) : r = s := by
  have hrr := (primeClassRankValue_spec P X r hr).2.2.2
  have hss := (primeClassRankValue_spec P X s hs).2.2.2
  rw [heq] at hrr
  exact hrr.symm.trans hss

theorem primeClassCoordinates_length {A : Type*} (P : Set Nat) (f : Nat -> A) (X : Nat) :
    (primeClassCoordinates P f X).length = (primeClassPrefix P X).card := by
  exact List.length_ofFn

theorem primeClassCoordinates_mem_iff {A : Type*} (P : Set Nat) (f : Nat -> A)
    (X : Nat) (a : A) :
    List.Mem a (primeClassCoordinates P f X) <->
      exists r : Nat, And (r < (primeClassPrefix P X).card) (f (primeClassRankValue P r) = a) := by
  unfold primeClassCoordinates
  change Membership.mem
    (List.ofFn (fun i : Fin (primeClassPrefix P X).card => f (primeClassRankValue P i.val))) a <->
    exists r : Nat, And (r < (primeClassPrefix P X).card) (f (primeClassRankValue P r) = a)
  rw [List.mem_ofFn]
  constructor
  case mp =>
    intro h
    choose i hi using h
    exact Exists.intro i.val (And.intro i.isLt hi)
  case mpr =>
    intro h
    choose r hr using h
    exact Exists.intro (Fin.mk r hr.1) hr.2

theorem primeClassCoordinates_unit (P : Set Nat) (eta : Nat -> Real) (X : Nat)
    (heta : forall p : Nat, Nat.Prime p -> And (0 <= eta p) (eta p <= 1)) :
    forall a : Real, List.Mem a (primeClassCoordinates P eta X) -> And (0 <= a) (a <= 1) := by
  intro a ha
  choose r hr using (primeClassCoordinates_mem_iff P eta X a).mp ha
  have hunit := heta (primeClassRankValue P r) (primeClassRankValue_spec P X r hr.1).1
  simpa only [hr.2] using hunit

theorem greedyPrimeClass_local_rankValue_le
    (P : Set Nat) (x : Real) (hx : 2 <= x)
    (hP : forall t : Real, 2 <= t -> t <= x -> primeClassThetaReal P t <= t)
    (r : Nat) (hr : r < (primeClassPrefix P (Nat.floor x)).card) :
    primeClassRankValue greedyPrimeClass r <= primeClassRankValue P r := by
  have hcount := greedyPrimeClass_local_count_optimal P x hx hP
  have hp := primeClassRankValue_spec P (Nat.floor x) r hr
  have hs := primeClassRankValue_spec greedyPrimeClass (Nat.floor x) r (hr.trans_le hcount)
  exact greedyPrimeClass_local_rank_at P x hx hP r
    (primeClassRankValue P r) (primeClassRankValue greedyPrimeClass r)
    hp.1 hp.2.1
    ((Nat.cast_le.mpr hp.2.2.1).trans (Nat.floor_le (by linarith only [hx])))
    hp.2.2.2 hs.2.2.2

end PrimeFactorOscillations.PrimeClassDeletion

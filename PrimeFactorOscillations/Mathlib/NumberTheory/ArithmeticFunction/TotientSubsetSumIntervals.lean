/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Nat.Totient

/-!
# Indexed subset-sum intervals for totient families

The finite support consists of indices, so equal values at distinct indices
are retained. These interval-extension lemmas feed the complete stable
odd-totient spectrum and its actual finite signed-probe consumers.
-/

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 4096

namespace Finset

variable {alpha : Type*} [DecidableEq alpha]

def subsetSumInterval (T : Finset alpha) (w : alpha -> Nat) (A S : Nat) : Prop :=
  forall n : Nat, Membership.mem (Finset.range (S+1)) n ->
    A<=n -> n+A<=S ->
      exists U : Finset alpha, Membership.mem T.powerset U /\ U.sum w=n

def subsetSumAdmissibleBlock (w : alpha -> Nat) (A S : Nat) : List alpha -> Prop
  | [] => True
  | a::L => w a+2*A<=S+1 /\ subsetSumAdmissibleBlock w A (S+w a) L

theorem subset_sum_interval_insert (T : Finset alpha) (w : alpha -> Nat)
    (A S : Nat) (a : alpha) (ha : Not (Membership.mem T a))
    (hcover : subsetSumInterval T w A S) (hbound : w a+2*A<=S+1) :
    subsetSumInterval (Insert.insert a T) w A (S+w a) := by
  intro n hnrange hmin hmax
  by_cases hold : n+A<=S
  . choose U hU using hcover n (Finset.mem_range.mpr (by omega)) hmin hold
    apply Exists.intro U
    apply And.intro
    . apply Finset.mem_powerset.mpr
      intro i hi
      exact Finset.mem_insert.mpr (Or.inr ((Finset.mem_powerset.mp hU.1) hi))
    . exact hU.2
  . have hsmall : w a+A<=n := by omega
    have hrmin : A<=n-w a := by omega
    have hrmax : n-w a+A<=S := by omega
    choose U hU using hcover (n-w a) (Finset.mem_range.mpr (by omega)) hrmin hrmax
    have haU : Not (Membership.mem U a) := by
      intro hmem
      exact ha ((Finset.mem_powerset.mp hU.1) hmem)
    apply Exists.intro (Insert.insert a U)
    apply And.intro
    . apply Finset.mem_powerset.mpr
      intro i hi
      cases Finset.mem_insert.mp hi with
      | inl heq => exact Finset.mem_insert.mpr (Or.inl heq)
      | inr hmem =>
        exact Finset.mem_insert.mpr (Or.inr ((Finset.mem_powerset.mp hU.1) hmem))
    . rw [Finset.sum_insert haU,hU.2]
      omega

theorem subset_sum_interval_insert_block (T : Finset alpha) (w : alpha -> Nat)
    (A S : Nat) (L : List alpha) (hnodup : L.Nodup)
    (hnew : forall a, Membership.mem L a -> Not (Membership.mem T a))
    (hcover : subsetSumInterval T w A S)
    (hblock : subsetSumAdmissibleBlock w A S L) :
    subsetSumInterval (Union.union T L.toFinset) w A (S+(L.map w).sum) := by
  induction L generalizing T S with
  | nil =>
    simpa only [List.toFinset_nil,Finset.union_empty,List.map_nil,List.sum_nil,add_zero]
      using hcover
  | cons a L ih =>
    have hd := List.nodup_cons.mp hnodup
    change w a+2*A<=S+1 /\ subsetSumAdmissibleBlock w A (S+w a) L at hblock
    have ha : Not (Membership.mem T a) :=
      hnew a (List.mem_cons.mpr (Or.inl rfl))
    have hcovered := subset_sum_interval_insert T w A S a ha hcover hblock.1
    have htail : forall b, Membership.mem L b ->
        Not (Membership.mem (Insert.insert a T) b) := by
      intro b hb hmem
      cases Finset.mem_insert.mp hmem with
      | inl heq =>
        have haL : Membership.mem L a := by
          rw [<- heq]
          exact hb
        exact hd.1 haL
      | inr hmem =>
        exact hnew b (List.mem_cons.mpr (Or.inr hb)) hmem
    have hr := ih (T:=Insert.insert a T) (S:=S+w a) hd.2 htail hcovered hblock.2
    simpa only [List.toFinset_cons,Finset.insert_union,Finset.union_insert,
      List.map_cons,List.sum_cons,Nat.add_assoc] using hr

end Finset

namespace Nat

theorem oddTotient_base_three_interval :
    Finset.subsetSumInterval ({5,7,11,13,17,19} : Finset Nat)
      (fun d => d.totient/2) 5 33 := by
  unfold Finset.subsetSumInterval
  decide

theorem oddTotient_base_five_interval :
    Finset.subsetSumInterval ({3,7,9,11,13,17,19} : Finset Nat)
      (fun d => d.totient/2) 3 35 := by
  unfold Finset.subsetSumInterval
  decide

theorem oddTotient_base_other_interval :
    Finset.subsetSumInterval ({3,5} : Finset Nat)
      (fun d => d.totient/2) 0 3 := by
  unfold Finset.subsetSumInterval
  decide

end Nat

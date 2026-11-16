/-
Copyright (c) 2021 Alena Gusakov, Bhavik Mehta, Kyle Miller. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alena Gusakov, Bhavik Mehta, Kyle Miller
-/
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Set.Finite.Basic
import Mathlib.Tactic.Convert
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Push
import Mathlib.Tactic.SplitIfs

/-!
# Finite matching for the regular-factor consumer

This owned ASCII adaptation of Mathlib's finite Hall proof supplies the
finite matching dependency without rebuilding the pinned dependency cache.
The source argument is due to Gusakov, Mehta and Miller.
-/

set_option autoImplicit false
set_option Elab.async false

open Finset

universe u v

namespace HamiltonianFiniteHall

variable {Iota : Type u} {Alpha : Type v} [DecidableEq Alpha]
variable {t : Iota -> Finset Alpha}

section Fintype

variable [Fintype Iota]

theorem cond_erase {x : Iota} (a : Alpha)
    (ha : forall s : Finset Iota, s.Nonempty -> Not (s = univ) ->
      #s < #(s.biUnion t))
    (s' : Finset {x' : Iota // Not (x' = x)}) :
    #s' <= #(s'.biUnion fun x' => (t x').erase a) := by
  classical
  specialize ha (s'.image fun z => z.1)
  rw [image_nonempty, Finset.card_image_of_injective s' Subtype.coe_injective] at ha
  by_cases he : s'.Nonempty
  . have ha' : #s' < #(s'.biUnion fun x => t x) := by
      convert! ha he (fun h => by simpa [<- h] using mem_univ x) using 2
      ext y
      simp only [mem_image, mem_biUnion]
      constructor
      . intro hy
        choose z hz using hy
        exact Exists.intro z.val
          (And.intro (Exists.intro z (And.intro hz.1 rfl)) hz.2)
      . intro hy
        choose z hz using hy
        choose w hw using hz.1
        exact Exists.intro w (And.intro hw.1 (Eq.mp (congrArg (fun v => Membership.mem (t v) y) hw.2.symm) hz.2))
    rw [<- erase_biUnion]
    by_cases hb : Membership.mem (s'.biUnion fun x => t x) a
    . rw [card_erase_of_mem hb]
      exact Nat.le_sub_one_of_lt ha'
    . rw [erase_eq_of_notMem hb]
      exact Nat.le_of_lt ha'
  . have he' : s' = {} := not_nonempty_iff_eq_empty.mp he
    rw [he']
    simp

theorem inductive_strict {n : Nat} (hn : Fintype.card Iota = n + 1)
    (ht : forall s : Finset Iota, #s <= #(s.biUnion t))
    (ih : forall {J : Type u} [Fintype J] (t' : J -> Finset Alpha),
      Fintype.card J <= n ->
      (forall s' : Finset J, #s' <= #(s'.biUnion t')) ->
      Exists (fun f : J -> Alpha =>
        Function.Injective f /\ forall x, Membership.mem (t' x) (f x)))
    (ha : forall s : Finset Iota, s.Nonempty -> Not (s = univ) ->
      #s < #(s.biUnion t)) :
    Exists (fun f : Iota -> Alpha =>
      Function.Injective f /\ forall x, Membership.mem (t x) (f x)) := by
  classical
  have : Nonempty Iota := Fintype.card_pos_iff.mp (Eq.mp (congrArg (fun k : Nat => 0 < k) hn.symm) (Nat.succ_pos _))
  let x := Classical.arbitrary Iota
  have tx_ne : (t x).Nonempty := by
    rw [<- Finset.card_pos]
    calc
      0 < 1 := Nat.one_pos
      _ <= #(.biUnion {x} t) := ht {x}
      _ = (t x).card := by rw [Finset.singleton_biUnion]
  choose y hy using tx_ne
  let J := {x' : Iota // Not (x' = x)}
  let t' : J -> Finset Alpha := fun x' => (t x').erase y
  have card_J : Fintype.card J = n := by
    calc
      Fintype.card J = Fintype.card Iota - 1 := Set.card_ne_eq _
      _ = n := by rw [hn, Nat.add_succ_sub_one, add_zero]
  choose f' hf' using ih t' card_J.le (cond_erase y ha)
  have hfinj := hf'.1
  have hfr := hf'.2
  refine Exists.intro (fun z => if h : z = x then y else f' (Subtype.mk z h)) ?_
  constructor
  . intro z1 z2
    have key : forall {z}, Not (y = f' z) := by
      intro z h
      simpa [t', <- h] using hfr z
    have key' : forall {z}, Not (f' z = y) := by
      intro z h
      exact key h.symm
    by_cases h1 : z1 = x <;> by_cases h2 : z2 = x <;>
      simp [h1, h2, hfinj.eq_iff, key, key']
    intro hz
    exact congrArg Subtype.val hz
  . intro z
    simp only
    split_ifs with hz
    . rwa [hz]
    . specialize hfr (Subtype.mk z hz)
      rw [mem_erase] at hfr
      exact hfr.2

theorem cond_restrict {J : Type u} {t : J -> Finset Alpha} {s : Finset J}
    (ht : forall s : Finset J, #s <= #(s.biUnion t))
    (s' : Finset (s : Set J)) :
    #s' <= #(s'.biUnion fun a' => t a') := by
  classical
  rw [<- card_image_of_injective s' Subtype.coe_injective]
  convert! ht (s'.image fun z => z.1) using 1
  apply congr_arg
  ext y
  simp

theorem cond_compl {J : Type u} {t : J -> Finset Alpha} {s : Finset J}
    (hus : #s = #(s.biUnion t))
    (ht : forall s : Finset J, #s <= #(s.biUnion t))
    (s' : Finset (Compl.compl s : Set J)) :
    #s' <= #(s'.biUnion fun x' => t x' \ s.biUnion t) := by
  classical
  have disj : Disjoint s (s'.image fun z => z.1) := by
    simp only [disjoint_left, not_exists, mem_image, SetCoe.exists, exists_and_right,
      exists_eq_right]
    intro x hx hc _
    exact absurd hx hc
  have hc : #s' = #(Union.union s (s'.image fun z => z.1)) - #s := by
    simp [disj, card_image_of_injective _ Subtype.coe_injective, Nat.add_sub_cancel_left]
  rw [hc, hus]
  refine (Nat.sub_le_sub_right (ht _) _).trans ?_
  rw [<- card_sdiff_of_subset]
  . gcongr
    intro y
    simp only [mem_biUnion, mem_sdiff, not_exists, mem_image, and_imp, mem_union,
      exists_imp]
    intro x hx rat hs
    rcases hx with hx | hx
    . exact False.elim ((hs x) (And.intro hx rat))
    . choose x' hx' using hx
      rcases hx' with hx'
      have hxmem := hx'.1
      have hxeq := hx'.2
      subst x
      exact Exists.intro x' (And.intro hxmem (And.intro rat hs))
  . apply biUnion_subset_biUnion_of_subset_left
    exact subset_union_left

theorem inductive_tight {n : Nat} (hn : Fintype.card Iota = n + 1)
    (ht : forall s : Finset Iota, #s <= #(s.biUnion t))
    (ih : forall {J : Type u} [Fintype J] (t' : J -> Finset Alpha),
      Fintype.card J <= n ->
      (forall s' : Finset J, #s' <= #(s'.biUnion t')) ->
      Exists (fun f : J -> Alpha =>
        Function.Injective f /\ forall x, Membership.mem (t' x) (f x)))
    (s : Finset Iota) (hs : s.Nonempty) (hns : Not (s = univ))
    (hus : #s = #(s.biUnion t)) :
    Exists (fun f : Iota -> Alpha =>
      Function.Injective f /\ forall x, Membership.mem (t x) (f x)) := by
  classical
  rw [Nat.add_one] at hn
  have card_J_le : Fintype.card s <= n := by
    apply Nat.le_of_lt_succ
    calc
      Fintype.card s = #s := Fintype.card_coe _
      _ < Fintype.card Iota := (card_lt_iff_ne_univ _).mpr hns
      _ = n.succ := hn
  let t' : s -> Finset Alpha := fun x' => t x'
  choose f' hf' using ih t' card_J_le (cond_restrict ht)
  have hinj' := hf'.1
  have hsf' := hf'.2
  let J := (s : Set Iota).compl
  let t'' : J -> Finset Alpha := fun a'' => t a'' \ s.biUnion t
  have card_K_le : Fintype.card J <= n := by
    have hJ : J = ((Compl.compl s : Finset Iota) : Set Iota) := by
      ext x
      simp only [J, Finset.mem_coe, Finset.mem_compl]
      rfl
    simp only [hJ, Finset.coe_sort_coe, Fintype.card_coe]
    apply Nat.le_of_lt_succ
    rw [<- hn]
    rwa [card_compl_lt_iff_nonempty]
  choose f'' hf'' using ih t'' card_K_le (cond_compl hus ht)
  have hinj'' := hf''.1
  have hsf'' := hf''.2
  have f''_outside : forall (x'') (hx'' : Not (Membership.mem s x'')),
      Not (Membership.mem (s.biUnion t) (f'' (Subtype.mk x'' hx''))) := by
    intro x'' hx''
    have h := hsf'' (Subtype.mk x'' hx'')
    rw [mem_sdiff] at h
    exact h.2
  have im_disj : forall (x' x'' : Iota) (hx' : Membership.mem s x')
      (hx'' : Not (Membership.mem s x'')),
      Not (f' (Subtype.mk x' hx') = f'' (Subtype.mk x'' hx'')) := by
    intro x' x'' hx' hx'' he
    apply f''_outside x'' hx''
    rw [<- he]
    exact mem_biUnion.mpr (Exists.intro x' (And.intro hx' (hsf' (Subtype.mk x' hx'))))
  refine Exists.intro (fun x => if h : Membership.mem s x then
      f' (Subtype.mk x h) else f'' (Subtype.mk x h)) ?_
  constructor
  . exact hinj'.dite _ hinj'' (@fun x x' => im_disj x x' _ _)
  . intro x
    simp only
    split_ifs with h
    . exact hsf' (Subtype.mk x h)
    . exact sdiff_subset (hsf'' (Subtype.mk x h))

end Fintype

variable [Finite Iota]

theorem exists_matching (ht : forall s : Finset Iota, #s <= #(s.biUnion t)) :
    Exists (fun f : Iota -> Alpha =>
      Function.Injective f /\ forall x, Membership.mem (t x) (f x)) := by
  cases nonempty_fintype Iota
  generalize hn : Fintype.card Iota = m
  induction m using Nat.strongRecOn generalizing Iota with
  | ind n ih =>
    rcases n with _ | n
    . rw [Fintype.card_eq_zero_iff] at hn
      exact Exists.intro isEmptyElim (And.intro isEmptyElim isEmptyElim)
    . have ih' : forall (J : Type u) [Fintype J] (t' : J -> Finset Alpha),
          Fintype.card J <= n ->
          (forall s' : Finset J, #s' <= #(s'.biUnion t')) ->
          Exists (fun f : J -> Alpha =>
            Function.Injective f /\ forall x, Membership.mem (t' x) (f x)) := by
        intro J _ _ hJ ht'
        exact ih _ (Nat.lt_succ_of_le hJ) ht' _ rfl
      by_cases h : forall s : Finset Iota, s.Nonempty -> Not (s = univ) ->
          #s < #(s.biUnion t)
      . exact inductive_strict hn ht (@fun J => ih' J) h
      . push Not at h
        choose s hs using h
        have sne := hs.1
        have snu := hs.2.1
        have sle := hs.2.2
        exact inductive_tight hn ht (@fun J => ih' J) s sne snu
          (Nat.le_antisymm (ht _) sle)

end HamiltonianFiniteHall

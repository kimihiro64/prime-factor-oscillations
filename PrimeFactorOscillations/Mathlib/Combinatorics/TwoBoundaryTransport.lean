/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/

import PrimeFactorOscillations.Mathlib.Combinatorics.FinitePrefixDisplacement

/-!
# Signed transport cost of two prefix crossings

Two distinct entering coordinates pay at least the two nearest exterior
weights against the two nearest interior weights. Common coordinates are
cancelled first; all other crossing contributions remain nonnegative.
This is the finite signed input for the second probability-profile cutoff
threshold, beyond the earlier linear displacement bound.
-/

set_option autoImplicit false
set_option Elab.async false

noncomputable section

namespace Finset

theorem exists_mem_ge_succ_of_two_le_card
    (s : Finset Nat) (k : Nat) (hc : 2 <= s.card)
    (hs : forall j, Membership.mem s j -> k <= j) :
    exists j, Membership.mem s j /\ k + 1 <= j := by
  classical
  by_contra hn
  have hsub : forall j, Membership.mem s j -> Membership.mem ({k} : Finset Nat) j := by
    intro j hj
    have hjk : j = k := by
      by_contra hne
      exact hn (Exists.intro j (And.intro hj (by have := hs j hj; omega)))
    exact mem_singleton.mpr hjk
  have hcard := card_le_card hsub
  simp only [card_singleton] at hcard
  omega

theorem exists_mem_le_of_two_le_card
    (s : Finset Nat) (k : Nat) (hc : 2 <= s.card)
    (hs : forall j, Membership.mem s j -> j <= k + 1) :
    exists j, Membership.mem s j /\ j <= k := by
  classical
  by_contra hn
  have hsub : forall j, Membership.mem s j ->
      Membership.mem ({k + 1} : Finset Nat) j := by
    intro j hj
    have hjk : j = k + 1 := by
      by_contra hne
      exact hn (Exists.intro j (And.intro hj (by have := hs j hj; omega)))
    exact mem_singleton.mpr hjk
  have hcard := card_le_card hsub
  simp only [card_singleton] at hcard
  omega

theorem two_boundary_cost_le_sum_sub_sum
    (s u : Finset Nat) (w : Nat -> Real) (hw : Monotone w) (k : Nat)
    (hc : s.card = u.card) (hm : 2 <= (s \ u).card)
    (hs : forall j, Membership.mem (s \ u) j -> k + 2 <= j)
    (hu : forall j, Membership.mem (u \ s) j -> j <= k + 1) :
    w (k + 2) + w (k + 3) - w (k + 1) - w k <=
      s.sum w - u.sum w := by
  classical
  let E := s \ u
  let L := u \ s
  have hcard : E.card = L.card := card_sdiff_comm hc
  have hex := exists_mem_ge_succ_of_two_le_card E (k + 2) hm hs
  let je := Classical.choose hex
  have hje : Membership.mem E je /\ k + 3 <= je := by
    simpa only [Nat.add_assoc] using Classical.choose_spec hex
  have hmL : 2 <= L.card := by
    rw [<- hcard]
    exact hm
  have hlx := exists_mem_le_of_two_le_card L k hmL hu
  let jl := Classical.choose hlx
  have hjl : Membership.mem L jl /\ jl <= k := Classical.choose_spec hlx
  have hlo : w je - w (k + 2) <= E.sum (fun j => w j - w (k + 2)) :=
    single_le_sum (fun j hj => sub_nonneg.mpr (hw (hs j hj))) hje.1
  have hup : w (k + 1) - w jl <= L.sum (fun j => w (k + 1) - w j) :=
    single_le_sum (fun j hj => sub_nonneg.mpr (hw (hu j hj))) hjl.1
  simp only [sum_sub_distrib, sum_const, nsmul_eq_mul] at hlo hup
  have htwo : (2 : Real) <= E.card := by exact_mod_cast hm
  have hcardr : (E.card : Real) = L.card := by exact_mod_cast hcard
  rw [<- hcardr] at hup
  have hprod := mul_le_mul_of_nonneg_right htwo
    (sub_nonneg.mpr (hw (show k + 1 <= k + 2 by omega)))
  have hew := hw hje.2
  have hlw := hw hjl.2
  have hid := @sum_sdiff_sub_sum_sdiff Nat Real u s inferInstance inferInstance w
  rw [<- hid]
  change w (k + 2) + w (k + 3) - w (k + 1) - w k <= E.sum w - L.sum w
  nlinarith only [hlo, hup, hprod, hew, hlw]

theorem two_boundary_cost_le_prefixDefect
    (w : Nat -> Real) (hw : Monotone w) (e : Equiv.Perm Nat) (k : Nat)
    (hm : 2 <= prefixDisplacement e (k + 2)) :
    w (k + 2) + w (k + 3) - w (k + 1) - w k <=
      prefixDefect w e (k + 2) := by
  have hc : ((range (k + 2)).image e).card = (range (k + 2)).card :=
    card_image_iff.mpr (fun _ _ _ _ h => e.injective h)
  have hbound := two_boundary_cost_le_sum_sub_sum
    ((range (k + 2)).image e) (range (k + 2)) w hw k hc hm
    (fun j hj => by
      have hn := (mem_sdiff.mp hj).2
      rw [mem_range] at hn
      omega)
    (fun j hj => by
      have hn := (mem_sdiff.mp hj).1
      rw [mem_range] at hn
      omega)
  rw [sum_image (fun _ _ _ _ h => e.injective h)] at hbound
  exact hbound

end Finset

/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.NormNum
import PrimeFactorOscillations.Mathlib.Probability.Distributions.FiniteBernoulliOdds

/-!
# Exact forced-coordinate interpretation of the family ratio

Replacing each forced probability by zero preserves its field-valued odds.
The probability mass shifts by precisely the number of forced coordinates.
Excluded zero coordinates require no shift.
-/

set_option autoImplicit false
set_option Elab.async false

namespace PrimeFactorOscillations

noncomputable def familyUnforcedList (s : List Real) : List Real := by
  classical
  exact s.map (fun a => if a = 1 then 0 else a)

theorem familyUnforcedList_mass (s : List Real) (r : Nat) :
    List.bernoulliMass (familyUnforcedList s) r =
      List.bernoulliMass (s.filter (fun a => decide (Not (a = 1)))) r := by
  classical
  induction s generalizing r with
  | nil => simp [familyUnforcedList]
  | cons a s ih =>
      simp only [familyUnforcedList] at ih
      by_cases ha : a = 1
      . subst a
        simpa [familyUnforcedList, List.bernoulliMass_zero_cons] using ih r
      . cases r with
        | zero => simp [familyUnforcedList, ha, List.bernoulliMass, ih]
        | succ r => simp [familyUnforcedList, ha, List.bernoulliMass, ih]

theorem familyUnforcedList_odds (s : List Real) :
    (familyUnforcedList s).map (fun a => a / (1 - a)) =
      s.map (fun a => a / (1 - a)) := by
  classical
  simp only [familyUnforcedList, List.map_map]
  apply List.map_congr_left
  intro a _
  by_cases ha : a = 1
  . simp [ha]
  . simp [ha]

theorem familyUnforcedList_lt_one (s : List Real)
    (hs : forall a, List.Mem a s -> a <= 1) :
    forall a, List.Mem a (familyUnforcedList s) -> a < 1 := by
  classical
  intro a ha
  choose b hb using List.mem_map.mp ha
  by_cases h : b = 1
  . have he : a = 0 := by simpa [h] using hb.2.symm
    rw [he]
    norm_num
  . have he : a = b := by simpa [h] using hb.2.symm
    rw [he]
    exact lt_of_le_of_ne (hs b hb.1) h

theorem familyUnforcedList_survival_pos (s : List Real)
    (hs : forall a, List.Mem a s -> a <= 1) :
    0 < ((familyUnforcedList s).map (fun a => 1 - a)).prod := by
  have hlt := familyUnforcedList_lt_one s hs
  have hprod : forall t : List Real, (forall a, List.Mem a t -> a < 1) ->
      0 < (t.map (fun a => 1 - a)).prod := by
    intro t
    induction t with
    | nil => intro _; simp
    | cons a t ih =>
        intro ht
        simp only [List.map_cons, List.prod_cons]
        exact mul_pos (sub_pos.mpr (ht a (List.Mem.head _)))
          (ih (fun b hb => ht b (List.Mem.tail _ hb)))
  exact hprod _ hlt

theorem familyMass_eq_survival_mul_odds (s : List Real)
    (hs : forall a, List.Mem a s -> a <= 1) (r : Nat) :
    List.bernoulliMass s (s.count 1 + r) =
      ((familyUnforcedList s).map (fun a => 1 - a)).prod *
        ((s.map (fun a => a / (1 - a)) : List Real) : Multiset Real).esymm r := by
  classical
  rw [List.bernoulliMass_count_one_add, <- familyUnforcedList_mass,
    List.bernoulliMass_eq_survival_mul_esymm _ (fun a ha =>
      (ne_of_lt (familyUnforcedList_lt_one s hs a ha))), familyUnforcedList_odds]

theorem familyMass_ratio_eq_full_odds (s : List Real)
    (hs : forall a, List.Mem a s -> a <= 1) (r : Nat) (hr : 1 <= r) :
    List.bernoulliMass s (s.count 1 + r - 1) /
        List.bernoulliMass s (s.count 1 + r) =
      ((s.map (fun a => a / (1 - a)) : List Real) : Multiset Real).esymm (r - 1) /
        ((s.map (fun a => a / (1 - a)) : List Real) : Multiset Real).esymm r := by
  rw [show s.count 1 + r - 1 = s.count 1 + (r - 1) by omega,
    familyMass_eq_survival_mul_odds s hs (r - 1), familyMass_eq_survival_mul_odds s hs r]
  exact mul_div_mul_left _ _ (familyUnforcedList_survival_pos s hs).ne'

end PrimeFactorOscillations

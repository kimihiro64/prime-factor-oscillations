/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.PrimeOrderReturnRigidity

/-!
# Quantitative rigidity of gated vacancy profiles

Closed gates cost a separate reciprocal-prime-minus-one penalty.
Open coordinates retain their actual image defect. The normalized
product keeps every cross term before the additive budget is taken.
-/

set_option autoImplicit false
set_option Elab.async false

noncomputable section

namespace PrimeFactorOscillations.PrimeOrderGatedRigidity

open PrimeOrderReturnRigidity

def gatedCoordinateDefect (l d : Real) (gate : Bool) : Real :=
  if gate then coordinateDefect l d else 1 / (l - 1)

def gatedVacancy (S : Finset Nat.Primes) (gates : S -> Bool) (d : S -> Real) : Real :=
  Finset.univ.prod (fun l : S => if gates l then 1 - 1 / d l else 1)

def gatedPenalty (l d : Real) (gate : Bool) : Real := by
  classical
  exact if gate then if l ^ 2 <= d then 1 / l else 0 else 1 / (l - 1)

theorem gated_coordinate_factorization (l d : Real) (gate : Bool) (hl : 1 < l)
    (hOpen : gate = true -> l <= d) :
    (if gate then 1 - 1 / d else 1) =
      (1 - 1 / l) * (1 + gatedCoordinateDefect l d gate) := by
  cases gate
  { change 1 = (1 - 1 / l) * (1 + 1 / (l - 1))
    have hl0 : Not (l = 0) := by linarith
    have hsub : Not (l - 1 = 0) := by linarith
    field_simp
    <;> ring }
  { exact coordinate_factorization l d hl (hOpen rfl) }

theorem gatedCoordinateDefect_nonneg (l d : Real) (gate : Bool) (hl : 1 < l)
    (hOpen : gate = true -> l <= d) : 0 <= gatedCoordinateDefect l d gate := by
  cases gate
  { exact div_nonneg zero_le_one (sub_pos.mpr hl).le }
  { exact coordinateDefect_nonneg l d hl (hOpen rfl) }

theorem gatedPenalty_le_defect (l d : Real) (gate : Bool) (hl : 1 < l)
    (hOpen : gate = true -> l <= d) :
    gatedPenalty l d gate <= gatedCoordinateDefect l d gate := by
  classical
  cases gate
  { exact le_rfl }
  { change (if l ^ 2 <= d then 1 / l else 0) <= coordinateDefect l d
    split_ifs with h
    { exact coordinateDefect_ge_reciprocal l d hl h }
    { exact coordinateDefect_nonneg l d hl (hOpen rfl) } }

theorem gated_ratio_eq_product (S : Finset Nat.Primes) (gates : S -> Bool) (d : S -> Real)
    (hOpen : forall l : S, gates l = true -> ((l.val : Nat) : Real) <= d l) :
    gatedVacancy S gates d / vacancyFloor S =
      Finset.univ.prod (fun l : S =>
        1 + gatedCoordinateDefect ((l.val : Nat) : Real) (d l) (gates l)) := by
  classical
  have hBase := vacancyFloor_pos S
  have hFactor (l : S) :
      (if gates l then 1 - 1 / d l else 1) =
        (1 - 1 / ((l.val : Nat) : Real)) *
          (1 + gatedCoordinateDefect ((l.val : Nat) : Real) (d l) (gates l)) :=
    gated_coordinate_factorization _ _ _ (by exact_mod_cast l.val.property.one_lt) (hOpen l)
  unfold gatedVacancy
  simp_rw [hFactor]
  rw [Finset.prod_mul_distrib]
  change (vacancyFloor S * _) / vacancyFloor S = _
  field_simp

theorem gated_excess_ge_defect_sum (S : Finset Nat.Primes)
    (gates : S -> Bool) (d : S -> Real)
    (hOpen : forall l : S, gates l = true -> ((l.val : Nat) : Real) <= d l) :
    Finset.univ.sum (fun l : S =>
      gatedCoordinateDefect ((l.val : Nat) : Real) (d l) (gates l)) <=
      gatedVacancy S gates d / vacancyFloor S - 1 := by
  classical
  rw [gated_ratio_eq_product S gates d hOpen]
  have h := one_add_sum_le_product Finset.univ
    (fun l : S => gatedCoordinateDefect ((l.val : Nat) : Real) (d l) (gates l))
    (by
      intro l _
      exact gatedCoordinateDefect_nonneg _ _ _
        (by exact_mod_cast l.val.property.one_lt) (hOpen l))
  linarith

theorem gated_excess_ge_penalty_sum (S : Finset Nat.Primes)
    (gates : S -> Bool) (d : S -> Real)
    (hOpen : forall l : S, gates l = true -> ((l.val : Nat) : Real) <= d l) :
    Finset.univ.sum (fun l : S =>
      gatedPenalty ((l.val : Nat) : Real) (d l) (gates l)) <=
      gatedVacancy S gates d / vacancyFloor S - 1 := by
  classical
  apply le_trans _ (gated_excess_ge_defect_sum S gates d hOpen)
  apply Finset.sum_le_sum
  intro l _
  exact gatedPenalty_le_defect _ _ _ (by exact_mod_cast l.val.property.one_lt) (hOpen l)

theorem gated_defect_le_excess (S : Finset Nat.Primes)
    (gates : S -> Bool) (d : S -> Real)
    (hOpen : forall l : S, gates l = true -> ((l.val : Nat) : Real) <= d l)
    (l : S) :
    gatedCoordinateDefect ((l.val : Nat) : Real) (d l) (gates l) <=
      gatedVacancy S gates d / vacancyFloor S - 1 := by
  classical
  apply le_trans _ (gated_excess_ge_defect_sum S gates d hOpen)
  exact Finset.single_le_sum
    (fun p _ => gatedCoordinateDefect_nonneg _ _ _
      (by exact_mod_cast p.val.property.one_lt) (hOpen p)) (Finset.mem_univ l)

theorem gated_vacancy_ge_floor (S : Finset Nat.Primes)
    (gates : S -> Bool) (d : S -> Real)
    (hOpen : forall l : S, gates l = true -> ((l.val : Nat) : Real) <= d l) :
    vacancyFloor S <= gatedVacancy S gates d := by
  have hNonneg : 0 <= Finset.univ.sum (fun l : S =>
      gatedCoordinateDefect ((l.val : Nat) : Real) (d l) (gates l)) :=
    Finset.sum_nonneg (fun l _ => gatedCoordinateDefect_nonneg _ _ _
      (by exact_mod_cast l.val.property.one_lt) (hOpen l))
  have h := gated_excess_ge_defect_sum S gates d hOpen
  have hRatio : 1 <= gatedVacancy S gates d / vacancyFloor S := by linarith
  have hMul := mul_le_mul_of_nonneg_right hRatio (vacancyFloor_pos S).le
  have hIdentity : (gatedVacancy S gates d / vacancyFloor S) * vacancyFloor S =
      gatedVacancy S gates d := by
    field_simp [ne_of_gt (vacancyFloor_pos S)]
  rwa [one_mul, hIdentity] at hMul

theorem near_minimal_gate_and_index_small (S : Finset Nat.Primes)
    (gates : S -> Bool) (d : S -> Real)
    (hOpen : forall l : S, gates l = true -> ((l.val : Nat) : Real) <= d l)
    (Y : Real) (hY : 0 < Y)
    (hSmall : gatedVacancy S gates d / vacancyFloor S - 1 < 1 / Y)
    (l : S) (hlY : ((l.val : Nat) : Real) <= Y) :
    And (gates l = true) (d l < ((l.val : Nat) : Real) ^ 2) := by
  have hl : (1 : Real) < ((l.val : Nat) : Real) := by
    exact_mod_cast l.val.property.one_lt
  have hBudget := gated_defect_le_excess S gates d hOpen l
  have hGate : gates l = true := by
    cases h : gates l
    { have hRec : 1 / Y <= 1 / (((l.val : Nat) : Real) - 1) :=
        one_div_le_one_div_of_le (sub_pos.mpr hl) (by linarith)
      have hClosed : gatedCoordinateDefect ((l.val : Nat) : Real) (d l) (gates l) =
          1 / (((l.val : Nat) : Real) - 1) := by rw [h]; rfl
      rw [hClosed] at hBudget
      linarith }
    { rfl }
  refine And.intro hGate ?_
  apply lt_of_not_ge
  intro hLarge
  have hRec : 1 / Y <= 1 / ((l.val : Nat) : Real) :=
    one_div_le_one_div_of_le (by linarith) hlY
  have hDefect := coordinateDefect_ge_reciprocal _ _ hl hLarge
  have hIdentity : gatedCoordinateDefect ((l.val : Nat) : Real) (d l) (gates l) =
      coordinateDefect ((l.val : Nat) : Real) (d l) := by rw [hGate]; rfl
  rw [hIdentity] at hBudget
  linarith

end PrimeFactorOscillations.PrimeOrderGatedRigidity

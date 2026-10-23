/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import PrimeFactorOscillations.Helpers.PrimeOrderReturnIndex

/-!
# Quantitative rigidity of native prime-order vacancy probabilities

The exact native vacancy ratio bounds a reciprocal-prime weighted count
of repeated local periods. Thus a single probability observable controls
which prime labels may have more than one surviving maximal coordinate.
Every result is finite and unconditional.
-/

set_option autoImplicit false
set_option Elab.async false

noncomputable section

namespace PrimeFactorOscillations.PrimeOrderReturnRigidity

open PrimeOrderReturnLaw PrimeOrderReturnIndex

/-- The positive prime-product vacancy floor, including the empty packet. -/
def vacancyFloor (S : Finset Nat.Primes) : Real :=
  Finset.univ.prod (fun l : S => 1 - 1 / ((l.val : Nat) : Real))

/-- Relative coordinate inflation over the minimal prime-order image. -/
def coordinateDefect (l d : Real) : Real :=
  (d - l) / (d * (l - 1))

theorem coordinate_factorization (l d : Real) (hl : 1 < l) (hd : l <= d) :
    1 - 1 / d = (1 - 1 / l) * (1 + coordinateDefect l d) := by
  have hl0 : Not (l = 0) := by linarith
  have hd0 : Not (d = 0) := by linarith
  have hsub : Not (l - 1 = 0) := by linarith
  dsimp [coordinateDefect]
  field_simp
  <;> ring

theorem coordinateDefect_nonneg (l d : Real) (hl : 1 < l) (hd : l <= d) :
    0 <= coordinateDefect l d := by
  apply div_nonneg (sub_nonneg.mpr hd)
  exact (mul_pos (by linarith : 0 < d) (sub_pos.mpr hl)).le

/-- A second local coordinate costs at least one reciprocal prime. -/
theorem coordinateDefect_ge_reciprocal (l d : Real)
    (hl : 1 < l) (hd : l ^ 2 <= d) :
    1 / l <= coordinateDefect l d := by
  have hlPos : 0 < l := by linarith
  have hdPos : 0 < d := by nlinarith
  have hl0 : Not (l = 0) := by linarith
  have hd0 : Not (d = 0) := by linarith
  have hsub : Not (l - 1 = 0) := by linarith
  have hIdentity : coordinateDefect l d - 1 / l =
      (d - l ^ 2) / (l * d * (l - 1)) := by
    dsimp [coordinateDefect]
    field_simp
    <;> ring
  have hNonneg : 0 <= (d - l ^ 2) / (l * d * (l - 1)) :=
    div_nonneg (sub_nonneg.mpr hd) (mul_pos (mul_pos hlPos hdPos) (sub_pos.mpr hl)).le
  rw [<- hIdentity] at hNonneg
  linarith

theorem vacancyFloor_pos (S : Finset Nat.Primes) : 0 < vacancyFloor S := by
  apply Finset.prod_pos
  intro l _
  have hl : (1 : Real) < ((l.val : Nat) : Real) := by
    exact_mod_cast l.val.property.one_lt
  have hRec := one_div_lt_one_div_of_lt (by norm_num : (0 : Real) < 1) hl
  simpa only [div_one] using sub_pos.mpr hRec

/-- All nonnegative product cross terms are retained before taking the bound. -/
theorem one_add_sum_le_product {I : Type*} [DecidableEq I]
    (S : Finset I) (t : I -> Real) (ht : forall i, Membership.mem S i -> 0 <= t i) :
    1 + S.sum t <= S.prod (fun i => 1 + t i) := by
  induction S using Finset.induction_on with
  | empty => simp
  | @insert i S hi ih =>
    rw [Finset.sum_insert hi, Finset.prod_insert hi]
    have hi0 : 0 <= t i := ht i (Finset.mem_insert_self i S)
    have hS : forall j, Membership.mem S j -> 0 <= t j := by
      intro j hj
      exact ht j (Finset.mem_insert_of_mem hj)
    have hSum : 0 <= S.sum t := Finset.sum_nonneg hS
    have hMul := mul_le_mul_of_nonneg_left (ih hS) (by linarith : 0 <= 1 + t i)
    nlinarith [mul_nonneg hi0 hSum]

variable {G : Type*} [CommGroup G] [Fintype G]

theorem vacancy_ratio_eq_product (S : Finset Nat.Primes)
    (hDiv : forall l : S, Dvd.dvd (l.val : Nat) (Monoid.exponent G)) :
    returnPatternProbability (G := G) (Monoid.exponent G) S (fun _ => false) /
        vacancyFloor S =
      Finset.univ.prod (fun l : S => 1 + coordinateDefect ((l.val : Nat) : Real)
        (returnIndex (G := G) (Monoid.exponent G) (l.val : Nat) : Real)) := by
  classical
  have hB := vacancyFloor_pos S
  have hFactor : forall l : S,
      1 - 1 / (returnIndex (G := G) (Monoid.exponent G) (l.val : Nat) : Real) =
        (1 - 1 / ((l.val : Nat) : Real)) *
          (1 + coordinateDefect ((l.val : Nat) : Real)
            (returnIndex (G := G) (Monoid.exponent G) (l.val : Nat) : Real)) := by
    intro l
    apply coordinate_factorization
    { exact_mod_cast l.val.property.one_lt }
    { exact_mod_cast divisor_le_returnIndex (G := G) (l.val : Nat) (hDiv l) }
  rw [returnPatternProbability_eq_product _ S hDiv
    (fun g => Monoid.pow_exponent_eq_one g)]
  simp only [Bool.false_eq_true, ite_false]
  simp_rw [hFactor]
  rw [Finset.prod_mul_distrib]
  change (vacancyFloor S * _) / vacancyFloor S = _
  field_simp

theorem vacancy_excess_ge_defect_sum (S : Finset Nat.Primes)
    (hDiv : forall l : S, Dvd.dvd (l.val : Nat) (Monoid.exponent G)) :
    Finset.univ.sum (fun l : S => coordinateDefect ((l.val : Nat) : Real)
        (returnIndex (G := G) (Monoid.exponent G) (l.val : Nat) : Real)) <=
      returnPatternProbability (G := G) (Monoid.exponent G) S (fun _ => false) /
        vacancyFloor S - 1 := by
  classical
  rw [vacancy_ratio_eq_product S hDiv]
  have h := one_add_sum_le_product Finset.univ
    (fun l : S => coordinateDefect ((l.val : Nat) : Real)
      (returnIndex (G := G) (Monoid.exponent G) (l.val : Nat) : Real)) (by
        intro l _
        apply coordinateDefect_nonneg
        { exact_mod_cast l.val.property.one_lt }
        { exact_mod_cast divisor_le_returnIndex (G := G) (l.val : Nat) (hDiv l) })
  linarith

/-- At a canonical prime label at least one local period must be lost. -/
theorem returnMultiplicity_pos (c : Nat) [NeZero c] (hSq : Squarefree c)
    (l : Nat.Primes) (hl : Dvd.dvd (l : Nat) (Monoid.exponent (Units (ZMod c)))) :
    0 < returnMultiplicity c (Monoid.exponent (Units (ZMod c))) l := by
  have hLe := divisor_le_returnIndex (G := Units (ZMod c)) (l : Nat) hl
  rw [canonical_squarefree_returnIndex c hSq l hl] at hLe
  by_contra h
  have hZero : returnMultiplicity c (Monoid.exponent (Units (ZMod c))) l = 0 := by omega
  rw [hZero, pow_zero] at hLe
  have hTwo := l.property.two_le
  omega

theorem prime_square_le_index_of_repeated (c : Nat) [NeZero c] (hSq : Squarefree c)
    (l : Nat.Primes) (hl : Dvd.dvd (l : Nat) (Monoid.exponent (Units (ZMod c))))
    (hRepeated : 2 <= returnMultiplicity c (Monoid.exponent (Units (ZMod c))) l) :
    (l : Nat) ^ 2 <=
      returnIndex (G := Units (ZMod c)) (Monoid.exponent (Units (ZMod c))) (l : Nat) := by
  let r := returnMultiplicity c (Monoid.exponent (Units (ZMod c))) l
  have hRepr : r = (r - 2) + 2 := by dsimp [r]; omega
  have hPowPos : 0 < (l : Nat) ^ (r - 2) := pow_pos l.property.pos _
  have hPowOne : 1 <= (l : Nat) ^ (r - 2) := by omega
  rw [canonical_squarefree_returnIndex c hSq l hl]
  change (l : Nat) ^ 2 <= (l : Nat) ^ r
  calc
    (l : Nat) ^ 2 <= (l : Nat) ^ (r - 2) * (l : Nat) ^ 2 := by
      simpa only [one_mul] using Nat.mul_le_mul_right ((l : Nat) ^ 2) hPowOne
    _ = (l : Nat) ^ r := by rw [<- pow_add, <- hRepr]

/-- A single native vacancy probability bounds the full weighted redundancy. -/
theorem reciprocal_redundancy_budget (c : Nat) [NeZero c] (hSq : Squarefree c)
    (S : Finset Nat.Primes)
    (hDiv : forall l : S, Dvd.dvd (l.val : Nat) (Monoid.exponent (Units (ZMod c)))) :
    Finset.univ.sum (fun l : S =>
        if 2 <= returnMultiplicity c (Monoid.exponent (Units (ZMod c))) l.val
        then 1 / ((l.val : Nat) : Real) else 0) <=
      returnPatternProbability (G := Units (ZMod c))
          (Monoid.exponent (Units (ZMod c))) S (fun _ => false) / vacancyFloor S - 1 := by
  classical
  have hEach : forall l : S,
      (if 2 <= returnMultiplicity c (Monoid.exponent (Units (ZMod c))) l.val
        then 1 / ((l.val : Nat) : Real) else 0) <=
      coordinateDefect ((l.val : Nat) : Real)
        (returnIndex (G := Units (ZMod c)) (Monoid.exponent (Units (ZMod c)))
          (l.val : Nat) : Real) := by
    intro l
    split_ifs with hRepeated
    { apply coordinateDefect_ge_reciprocal
      { exact_mod_cast l.val.property.one_lt }
      { exact_mod_cast prime_square_le_index_of_repeated c hSq l.val (hDiv l) hRepeated } }
    { apply coordinateDefect_nonneg
      { exact_mod_cast l.val.property.one_lt }
      { exact_mod_cast divisor_le_returnIndex (G := Units (ZMod c)) (l.val : Nat) (hDiv l) } }
  exact le_trans (Finset.sum_le_sum (fun l _ => hEach l))
    (vacancy_excess_ge_defect_sum (G := Units (ZMod c)) S hDiv)

theorem repeated_period_forces_excess (c : Nat) [NeZero c] (hSq : Squarefree c)
    (S : Finset Nat.Primes)
    (hDiv : forall l : S, Dvd.dvd (l.val : Nat) (Monoid.exponent (Units (ZMod c))))
    (l : S) (hRepeated : 2 <= returnMultiplicity c (Monoid.exponent (Units (ZMod c))) l.val) :
    1 / ((l.val : Nat) : Real) <=
      returnPatternProbability (G := Units (ZMod c))
          (Monoid.exponent (Units (ZMod c))) S (fun _ => false) / vacancyFloor S - 1 := by
  classical
  have hSingle :
      (if 2 <= returnMultiplicity c (Monoid.exponent (Units (ZMod c))) l.val
        then 1 / ((l.val : Nat) : Real) else 0) <=
      Finset.univ.sum (fun j : S =>
        if 2 <= returnMultiplicity c (Monoid.exponent (Units (ZMod c))) j.val
        then 1 / ((j.val : Nat) : Real) else 0) := by
    apply Finset.single_le_sum _ (Finset.mem_univ l)
    intro j _
    split_ifs
    { exact div_nonneg (by norm_num) (Nat.cast_nonneg _) }
    { exact le_rfl }
  rw [ite_eq_left hRepeated] at hSingle
  exact hSingle.trans (reciprocal_redundancy_budget c hSq S hDiv)

theorem small_excess_forces_unique_period (c : Nat) [NeZero c] (hSq : Squarefree c)
    (S : Finset Nat.Primes)
    (hDiv : forall l : S, Dvd.dvd (l.val : Nat) (Monoid.exponent (Units (ZMod c))))
    (l : S)
    (hSmall : returnPatternProbability (G := Units (ZMod c))
        (Monoid.exponent (Units (ZMod c))) S (fun _ => false) / vacancyFloor S - 1 <
          1 / ((l.val : Nat) : Real)) :
    returnMultiplicity c (Monoid.exponent (Units (ZMod c))) l.val = 1 := by
  have hPos := returnMultiplicity_pos c hSq l.val (hDiv l)
  by_contra hNe
  have hRepeated : 2 <= returnMultiplicity c (Monoid.exponent (Units (ZMod c))) l.val := by omega
  exact (not_lt_of_ge (repeated_period_forces_excess c hSq S hDiv l hRepeated)) hSmall

/-- Near-minimal vacancy resolves all selected prime labels below a scale. -/
theorem near_minimal_small_labels_unique (c : Nat) [NeZero c] (hSq : Squarefree c)
    (S : Finset Nat.Primes)
    (hDiv : forall l : S, Dvd.dvd (l.val : Nat) (Monoid.exponent (Units (ZMod c))))
    (Y : Real) (_hY : 0 < Y)
    (hSmall : returnPatternProbability (G := Units (ZMod c))
        (Monoid.exponent (Units (ZMod c))) S (fun _ => false) / vacancyFloor S - 1 < 1 / Y) :
    forall l : S, ((l.val : Nat) : Real) <= Y ->
      returnMultiplicity c (Monoid.exponent (Units (ZMod c))) l.val = 1 := by
  intro l hlY
  apply small_excess_forces_unique_period c hSq S hDiv l
  exact lt_of_lt_of_le hSmall
    (one_div_le_one_div_of_le (by exact_mod_cast l.val.property.pos) hlY)

/-- Equality detects exactly one lost prime-factor period at every label. -/
theorem vacancy_eq_floor_iff_unique_periods (c : Nat) [NeZero c] (hSq : Squarefree c)
    (S : Finset Nat.Primes)
    (hDiv : forall l : S, Dvd.dvd (l.val : Nat) (Monoid.exponent (Units (ZMod c)))) :
    returnPatternProbability (G := Units (ZMod c))
        (Monoid.exponent (Units (ZMod c))) S (fun _ => false) = vacancyFloor S <->
      forall l : S, returnMultiplicity c (Monoid.exponent (Units (ZMod c))) l.val = 1 := by
  classical
  constructor
  { intro hEq l
    apply small_excess_forces_unique_period c hSq S hDiv l
    rw [hEq]
    have hB := vacancyFloor_pos S
    have hNorm : vacancyFloor S / vacancyFloor S = 1 := by field_simp
    rw [hNorm, sub_self]
    exact one_div_pos.mpr (by exact_mod_cast l.val.property.pos) }
  { intro hUnique
    rw [modular_unit_returnPatternProbability c S hDiv]
    simp only [Bool.false_eq_true, ite_false]
    unfold vacancyFloor
    apply Finset.prod_congr rfl
    intro l _
    rw [canonical_squarefree_returnIndex c hSq l.val (hDiv l), hUnique l, pow_one] }

end PrimeFactorOscillations.PrimeOrderReturnRigidity

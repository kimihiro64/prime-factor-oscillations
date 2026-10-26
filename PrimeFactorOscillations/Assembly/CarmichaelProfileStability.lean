/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.PrimeOrderReturnRigidity
import PrimeFactorOscillations.Proof.PrimeClassDeletion.RepairHellinger

/-!
# A single vacancy probability controls the complete native return profile

The canonical image indices dominate the prime labels. The resulting
pointwise comparison controls every binary pattern and every event by
the ratio of the actual vacancy to its prime-product minimum. The
normalized laws then give total-variation and Hellinger bounds without
discarding a signed mass discrepancy. These finite statements apply to
actual modular-unit groups; they assert no new RH exponent.
-/

set_option autoImplicit false
set_option Elab.async false

noncomputable section

namespace PrimeFactorOscillations.CarmichaelProfileStability

open PrimeOrderReturnLaw PrimeOrderReturnRigidity PrimeClassDeletion

def minimalPatternProbability (S : Finset Nat.Primes) (bits : S -> Bool) : Real :=
  Finset.univ.prod (fun p : S =>
    if bits p then 1 / ((p.val : Nat) : Real)
    else 1 - 1 / ((p.val : Nat) : Real))

theorem minimal_pattern_nonneg (S : Finset Nat.Primes) (bits : S -> Bool) :
    0 <= minimalPatternProbability S bits := by
  apply Finset.prod_nonneg
  intro p _
  have hp : (1 : Real) < ((p.val : Nat) : Real) := by
    exact_mod_cast p.val.property.one_lt
  have hq : 1 / ((p.val : Nat) : Real) < 1 :=
    (div_lt_one (zero_lt_one.trans hp)).mpr hp
  cases bits p <;> simp only [Bool.false_eq_true, ite_false, ite_true]
  { linarith }
  { exact (one_div_pos.mpr (zero_lt_one.trans hp)).le }

theorem minimal_patterns_sum_one (S : Finset Nat.Primes) :
    Finset.univ.sum (minimalPatternProbability S) = 1 := by
  classical
  unfold minimalPatternProbability
  calc
    _ = Finset.univ.prod (fun p : S => Finset.univ.sum (fun bit : Bool =>
        if bit then 1 / ((p.val : Nat) : Real)
        else 1 - 1 / ((p.val : Nat) : Real))) :=
      (Fintype.prod_sum (fun (p : S) (bit : Bool) =>
        if bit then 1 / ((p.val : Nat) : Real)
        else 1 - 1 / ((p.val : Nat) : Real))).symm
    _ = 1 := by simp

variable {G : Type*} [CommGroup G] [Fintype G]

omit [Fintype G] in
theorem native_pattern_nonneg (S : Finset Nat.Primes) (bits : S -> Bool) :
    0 <= returnPatternProbability (G := G) (Monoid.exponent G) S bits := by
  unfold returnPatternProbability FiniteHomProbability.uniformProbability
  exact div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)

theorem native_patterns_sum_one (S : Finset Nat.Primes)
    (hDiv : forall p : S, Dvd.dvd (p.val : Nat) (Monoid.exponent G)) :
    Finset.univ.sum (fun bits : S -> Bool =>
      returnPatternProbability (G := G) (Monoid.exponent G) S bits) = 1 := by
  classical
  simp_rw [returnPatternProbability_eq_product _ S hDiv
    (fun g => Monoid.pow_exponent_eq_one g)]
  calc
    _ = Finset.univ.prod (fun p : S => Finset.univ.sum (fun bit : Bool =>
        if bit then 1 / (returnIndex (G := G) (Monoid.exponent G) (p.val : Nat) : Real)
        else 1 - 1 / (returnIndex (G := G) (Monoid.exponent G) (p.val : Nat) : Real))) :=
      (Fintype.prod_sum (fun (p : S) (bit : Bool) =>
        if bit then 1 / (returnIndex (G := G) (Monoid.exponent G) (p.val : Nat) : Real)
        else 1 - 1 / (returnIndex (G := G) (Monoid.exponent G) (p.val : Nat) : Real))).symm
    _ = 1 := by simp

/-- Pointwise likelihood comparison in a division-free form. -/
theorem native_pattern_cross_comparison (S : Finset Nat.Primes)
    (hDiv : forall p : S, Dvd.dvd (p.val : Nat) (Monoid.exponent G))
    (bits : S -> Bool) :
    returnPatternProbability (G := G) (Monoid.exponent G) S bits * vacancyFloor S <=
      minimalPatternProbability S bits *
        returnPatternProbability (G := G) (Monoid.exponent G) S (fun _ => false) := by
  classical
  let a : S -> Real := fun p => 1 / ((p.val : Nat) : Real)
  let b : S -> Real := fun p =>
    1 / (returnIndex (G := G) (Monoid.exponent G) (p.val : Nat) : Real)
  have hBounds : forall p : S, And (0 <= b p) (And (b p <= a p) (a p < 1)) := by
    intro p
    have hp : (1 : Real) < ((p.val : Nat) : Real) := by
      exact_mod_cast p.val.property.one_lt
    have hd : ((p.val : Nat) : Real) <=
        (returnIndex (G := G) (Monoid.exponent G) (p.val : Nat) : Real) := by
      exact_mod_cast divisor_le_returnIndex (G := G) (p.val : Nat) (hDiv p)
    have hdPos : (0 : Real) <
        (returnIndex (G := G) (Monoid.exponent G) (p.val : Nat) : Real) := by linarith
    exact And.intro (one_div_pos.mpr hdPos).le
      (And.intro (one_div_le_one_div_of_le (zero_lt_one.trans hp) hd)
        ((div_lt_one (zero_lt_one.trans hp)).mpr hp))
  let f : S -> Real := fun p =>
    (if bits p then b p else 1 - b p) * (1 - a p)
  let g : S -> Real := fun p =>
    (if bits p then a p else 1 - a p) * (1 - b p)
  have hf : forall p : S, 0 <= f p := by
    intro p
    have hb := hBounds p
    have hbOne : b p <= 1 := hb.2.1.trans hb.2.2.le
    dsimp only [f]
    cases bits p <;> simp only [Bool.false_eq_true, ite_false, ite_true]
    { exact mul_nonneg (sub_nonneg.mpr hbOne) (sub_nonneg.mpr hb.2.2.le) }
    { exact mul_nonneg hb.1 (sub_nonneg.mpr hb.2.2.le) }
  have hfg : forall p : S, f p <= g p := by
    intro p
    have hb := hBounds p
    dsimp only [f, g]
    cases bits p <;> simp only [Bool.false_eq_true, ite_false, ite_true] <;> nlinarith
  have hProduct : forall T : Finset S, T.prod f <= T.prod g := by
    intro T
    induction T using Finset.induction_on with
    | empty => simp
    | @insert p T hp ih =>
      rw [Finset.prod_insert hp, Finset.prod_insert hp]
      exact mul_le_mul (hfg p) ih
        (Finset.prod_nonneg (fun q _ => hf q)) ((hf p).trans (hfg p))
  have h := hProduct Finset.univ
  dsimp only [f, g] at h
  rw [Finset.prod_mul_distrib, Finset.prod_mul_distrib] at h
  simpa only [returnPatternProbability_eq_product _ S hDiv
    (fun g => Monoid.pow_exponent_eq_one g), Bool.false_eq_true, ite_false,
    minimalPatternProbability, vacancyFloor, a, b] using h

/-- Every event in the entire binary return profile obeys the same comparison. -/
theorem native_event_cross_comparison (S : Finset Nat.Primes)
    (hDiv : forall p : S, Dvd.dvd (p.val : Nat) (Monoid.exponent G))
    (A : Finset (S -> Bool)) :
    A.sum (fun bits =>
        returnPatternProbability (G := G) (Monoid.exponent G) S bits) * vacancyFloor S <=
      A.sum (minimalPatternProbability S) *
        returnPatternProbability (G := G) (Monoid.exponent G) S (fun _ => false) := by
  rw [Finset.sum_mul, Finset.sum_mul]
  apply Finset.sum_le_sum
  intro bits _
  exact native_pattern_cross_comparison S hDiv bits

/-- Normalized event comparison; its denominator is always strictly positive. -/
theorem native_event_le_vacancy_ratio (S : Finset Nat.Primes)
    (hDiv : forall p : S, Dvd.dvd (p.val : Nat) (Monoid.exponent G))
    (A : Finset (S -> Bool)) :
    A.sum (fun bits =>
        returnPatternProbability (G := G) (Monoid.exponent G) S bits) <=
      (returnPatternProbability (G := G) (Monoid.exponent G) S (fun _ => false) /
        vacancyFloor S) * A.sum (minimalPatternProbability S) := by
  let V : Real :=
    returnPatternProbability (G := G) (Monoid.exponent G) S (fun _ => false)
  have hB : 0 < vacancyFloor S := vacancyFloor_pos S
  have h := native_event_cross_comparison S hDiv A
  have hScaled :
      A.sum (fun bits =>
        returnPatternProbability (G := G) (Monoid.exponent G) S bits) * vacancyFloor S <=
      ((V / vacancyFloor S) * A.sum (minimalPatternProbability S)) * vacancyFloor S := by
    calc
      _ <= A.sum (minimalPatternProbability S) * V := h
      _ = _ := by field_simp [ne_of_gt hB]
  exact le_of_mul_le_mul_right hScaled hB

def profileTotalVariation (S : Finset Nat.Primes) : Real :=
  (1 / 2 : Real) * Finset.univ.sum (fun bits : S -> Bool =>
    abs (returnPatternProbability (G := G) (Monoid.exponent G) S bits -
      minimalPatternProbability S bits))

def profileHellingerEnergy (S : Finset Nat.Primes) : Real :=
  Finset.univ.sum (fun bits : S -> Bool =>
    repairHellingerEnergy (minimalPatternProbability S bits)
      (returnPatternProbability (G := G) (Monoid.exponent G) S bits) 0)

/-- One vacancy atom controls total variation of the entire joint return law. -/
theorem native_profile_variation_le_vacancy_ratio (S : Finset Nat.Primes)
    (hDiv : forall p : S, Dvd.dvd (p.val : Nat) (Monoid.exponent G)) :
    profileTotalVariation (G := G) S <=
      1 - vacancyFloor S /
        returnPatternProbability (G := G) (Monoid.exponent G) S (fun _ => false) := by
  classical
  let p : (S -> Bool) -> Real := fun bits =>
    returnPatternProbability (G := G) (Monoid.exponent G) S bits
  let q : (S -> Bool) -> Real := minimalPatternProbability S
  let V : Real := p (fun _ => false)
  let B : Real := vacancyFloor S
  let O : Real := Finset.univ.sum (fun bits : S -> Bool => max (p bits - q bits) 0)
  let A : Finset (S -> Bool) := Finset.univ.filter (fun bits => q bits < p bits)
  have hB : 0 < B := vacancyFloor_pos S
  have hBV : B <= V := canonical_vacancy_ge_prime_product (G := G) S hDiv
  have hV : 0 < V := hB.trans_le hBV
  have hp : forall bits, 0 <= p bits := native_pattern_nonneg S
  have hpSum : Finset.univ.sum p = 1 := native_patterns_sum_one S hDiv
  have hqSum : Finset.univ.sum q = 1 := minimal_patterns_sum_one S
  have hLedger := abs_sub_sum_overweight_ledger Finset.univ q p
  rw [hqSum, hpSum] at hLedger
  have hTV : profileTotalVariation (G := G) S = O := by
    change (1 / 2 : Real) * Finset.univ.sum
      (fun bits : S -> Bool => abs (p bits - q bits)) = O
    change Finset.univ.sum (fun bits : S -> Bool => abs (p bits - q bits)) =
      2 * O + 1 - 1 at hLedger
    linarith
  have hO : O = A.sum p - A.sum q := by
    dsimp only [O, A]
    rw [<- Finset.sum_sub_distrib, Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro bits _
    by_cases h : q bits < p bits
    { rw [ite_eq_left h, max_eq_left (sub_nonneg.mpr h.le)] }
    { rw [ite_eq_right h, max_eq_right (sub_nonpos.mpr (not_lt.mp h))] }
  have hA : A.sum p <= 1 := by
    dsimp only [A]
    rw [Finset.sum_filter]
    calc
      _ <= Finset.univ.sum p := by
        apply Finset.sum_le_sum
        intro bits _
        split_ifs
        { exact le_rfl }
        { exact hp bits }
      _ = 1 := hpSum
  have hCross : A.sum p * B <= A.sum q * V :=
    native_event_cross_comparison S hDiv A
  have hRaw : V * profileTotalVariation (G := G) S <= V - B := by
    rw [hTV, hO]
    have hSupply := mul_nonneg (sub_nonneg.mpr hBV) (sub_nonneg.mpr hA)
    nlinarith [hCross]
  have hIdentity : V * (1 - B / V) = V - B := by
    field_simp [ne_of_gt hV]
  have hScaled : V * profileTotalVariation (G := G) S <= V * (1 - B / V) := by
    rw [hIdentity]
    exact hRaw
  exact le_of_mul_le_mul_left hScaled hV

/-- The existing signed repair ledger loses no mass term on these normalized laws. -/
theorem native_profile_energy_le_twice_variation (S : Finset Nat.Primes)
    (hDiv : forall p : S, Dvd.dvd (p.val : Nat) (Monoid.exponent G)) :
    profileHellingerEnergy (G := G) S <= 2 * profileTotalVariation (G := G) S := by
  classical
  let p : (S -> Bool) -> Real := fun bits =>
    returnPatternProbability (G := G) (Monoid.exponent G) S bits
  let q : (S -> Bool) -> Real := minimalPatternProbability S
  have hpSum : Finset.univ.sum p = 1 := native_patterns_sum_one S hDiv
  have hqSum : Finset.univ.sum q = 1 := minimal_patterns_sum_one S
  have hEnergy := repairHellingerEnergy_sum_le_ledger Finset.univ q p (fun _ => 0)
    (fun bits _ => minimal_pattern_nonneg S bits)
    (fun bits _ => native_pattern_nonneg S bits) (fun _ _ => le_rfl)
  have hLedger := abs_sub_sum_overweight_ledger Finset.univ q p
  rw [hqSum, hpSum] at hEnergy hLedger
  change Finset.univ.sum (fun bits : S -> Bool =>
      repairHellingerEnergy (q bits) (p bits) 0) <=
    2 * ((1 / 2 : Real) * Finset.univ.sum
      (fun bits : S -> Bool => abs (p bits - q bits)))
  linarith

theorem native_profile_energy_le_vacancy_ratio (S : Finset Nat.Primes)
    (hDiv : forall p : S, Dvd.dvd (p.val : Nat) (Monoid.exponent G)) :
    profileHellingerEnergy (G := G) S <=
      2 * (1 - vacancyFloor S /
        returnPatternProbability (G := G) (Monoid.exponent G) S (fun _ => false)) := by
  exact (native_profile_energy_le_twice_variation S hDiv).trans
    (mul_le_mul_of_nonneg_left (native_profile_variation_le_vacancy_ratio S hDiv)
      (by norm_num : (0 : Real) <= 2))

end PrimeFactorOscillations.CarmichaelProfileStability

/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Assembly.CarmichaelProfileStability
import PrimeFactorOscillations.Helpers.CarmichaelConditionalRigidity

/-!
# Conditional return-profile stability for arbitrary coprime extensions

A feasible maximal-order lift supplies a nontrivial prime-order auxiliary
return at every open gate. Thus the image-size bound needs no squarefree
hypothesis, even at powers of two. The zero-vacancy branch is kept separate
from every normalized comparison.
-/

set_option autoImplicit false
set_option Elab.async false

noncomputable section

namespace PrimeFactorOscillations.CarmichaelConditionalStability

open FiniteHomProbability PrimeOrderReturnLaw PrimeOrderReturnRigidity
  PrimeOrderGatedRigidity CarmichaelProfileLifts CarmichaelProfileCriterion
  CarmichaelProfileKernel CarmichaelMaximalOrderLifts CarmichaelEvenThinning
  CarmichaelProfileStability

local instance imageFintype {G : Type*} [CommGroup G] [Fintype G] (L l : Nat) :
    Fintype (returnImage (G := G) L l) :=
  PrimeOrderReturnLaw.imageFintype L l

/-- Feasibility alone forces every open auxiliary image to contain a full prime cycle. -/
theorem feasible_open_auxiliary_index_ge_prime (m B : Nat)
    [NeZero m] [NeZero B] [NeZero (m * B)] (hCoprime : Nat.Coprime m B)
    (a : Units (ZMod m))
    (hFeasible : Nat.lcm (orderOf a) (Monoid.exponent (Units (ZMod B))) =
      Monoid.exponent (Units (ZMod (m * B))))
    (l : Nat.Primes)
    (hl : Dvd.dvd (l : Nat) (Monoid.exponent (Units (ZMod (m * B)))))
    (hOpen : returnGate m B a (l : Nat) = true) :
    (l : Nat) <= returnIndex (G := Units (ZMod B))
      (Monoid.exponent (Units (ZMod (m * B)))) (l : Nat) := by
  classical
  let E := Monoid.exponent (Units (ZMod (m * B)))
  choose u hu using (maximal_order_lift_exists_iff m B hCoprime a).mpr hFeasible
  let b := unitReduction (dvd_mul_left B m) u
  have hMem : Membership.mem (exponentPrimePacket (m * B)) l :=
    (exponentPrimePacket_mem (m * B) l).mpr hl
  have hNonreturn : Not (u ^ (E / (l : Nat)) = 1) :=
    (maximal_order_iff_full_nonreturn (m * B) u).mp hu.2 (Subtype.mk l hMem)
  have hAux : Not (b ^ (E / (l : Nat)) = 1) := by
    intro h
    apply hNonreturn
    apply (reduction_return_gate_all_labels m B hCoprime l hl u).mpr
    apply And.intro
    { rw [hu.1]
      exact (returnGate_eq_true m B a (l : Nat)).mp hOpen }
    { exact h }
  have hPower : (b ^ (E / (l : Nat))) ^ (l : Nat) = 1 := by
    rw [<- pow_mul, Nat.div_mul_cancel hl]
    exact auxiliary_exponent_annihilates m B hCoprime b
  have hOrderDiv : Dvd.dvd (orderOf (b ^ (E / (l : Nat)))) (l : Nat) :=
    orderOf_dvd_of_pow_eq_one hPower
  have hOrder : orderOf (b ^ (E / (l : Nat))) = (l : Nat) :=
    ((Nat.dvd_prime l.property).mp hOrderDiv).resolve_left
      (fun h => hAux (orderOf_eq_one_iff.mp h))
  have hMember : Membership.mem (returnImage (G := Units (ZMod B)) E (l : Nat))
      (b ^ (E / (l : Nat))) := Exists.intro b rfl
  have hBound := (returnImage (G := Units (ZMod B)) E (l : Nat)).orderOf_le_card
    (Set.toFinite _) hMember
  rw [hOrder, Nat.card_eq_fintype_card] at hBound
  exact hBound

theorem feasible_open_indices (m B : Nat)
    [NeZero m] [NeZero B] [NeZero (m * B)] (hCoprime : Nat.Coprime m B)
    (a : Units (ZMod m))
    (hFeasible : Nat.lcm (orderOf a) (Monoid.exponent (Units (ZMod B))) =
      Monoid.exponent (Units (ZMod (m * B)))) :
    forall l : exponentPrimePacket (m * B), returnGate m B a (l.val : Nat) = true ->
      ((l.val : Nat) : Real) <= (returnIndex (G := Units (ZMod B))
        (Monoid.exponent (Units (ZMod (m * B)))) (l.val : Nat) : Real) := by
  intro l hOpen
  exact_mod_cast feasible_open_auxiliary_index_ge_prime m B hCoprime a hFeasible l.val
    ((exponentPrimePacket_mem (m * B) l.val).mp l.property) hOpen

/-- The conditional vacancy floor holds without squarefree restrictions. -/
theorem feasible_density_ge_floor (m B : Nat)
    [NeZero m] [NeZero B] [NeZero (m * B)] (hCoprime : Nat.Coprime m B)
    (a : Units (ZMod m))
    (hFeasible : Nat.lcm (orderOf a) (Monoid.exponent (Units (ZMod B))) =
      Monoid.exponent (Units (ZMod (m * B)))) :
    vacancyFloor (exponentPrimePacket (m * B)) <= maximalOrderLiftProbability m B a := by
  rw [CarmichaelConditionalRigidity.maximalProbability_eq_gatedVacancy m B hCoprime a]
  exact gated_vacancy_ge_floor _ _ _ (feasible_open_indices m B hCoprime a hFeasible)

/-- Zero vacancy or a universal positive floor, for all coprime nonzero moduli. -/
theorem conditional_density_dichotomy (m B : Nat)
    [NeZero m] [NeZero B] [NeZero (m * B)] (hCoprime : Nat.Coprime m B)
    (a : Units (ZMod m)) :
    Or (maximalOrderLiftProbability m B a = 0)
      (vacancyFloor (exponentPrimePacket (m * B)) <= maximalOrderLiftProbability m B a) := by
  classical
  by_cases h : Nat.lcm (orderOf a) (Monoid.exponent (Units (ZMod B))) =
      Monoid.exponent (Units (ZMod (m * B)))
  { exact Or.inr (feasible_density_ge_floor m B hCoprime a h) }
  { exact Or.inl (CarmichaelConditionalRigidity.infeasible_density_zero m B hCoprime a h) }

def conditionalReturnRate (m B : Nat) [NeZero B] (a : Units (ZMod m)) (l : Nat) : Real :=
  if returnGate m B a l then
    1 / (returnIndex (G := Units (ZMod B))
      (Monoid.exponent (Units (ZMod (m * B)))) l : Real)
  else 0

theorem conditional_profile_eq_product (m B : Nat)
    [NeZero m] [NeZero B] [NeZero (m * B)] (hCoprime : Nat.Coprime m B)
    (a : Units (ZMod m)) (bits : exponentPrimePacket (m * B) -> Bool) :
    fiberProfileProbability m B a (exponentPrimePacket (m * B)) bits =
      Finset.univ.prod (fun l : exponentPrimePacket (m * B) =>
        if bits l then conditionalReturnRate m B a (l.val : Nat)
        else 1 - conditionalReturnRate m B a (l.val : Nat)) := by
  classical
  rw [fiberProfileProbability_eq_product m B hCoprime a _
    (fun l => (exponentPrimePacket_mem (m * B) l.val).mp l.property) bits]
  apply Finset.prod_congr rfl
  intro l _
  cases hg : returnGate m B a (l.val : Nat) <;>
    cases bits l <;> simp [conditionalReturnRate, hg]

theorem feasible_rate_bounds (m B : Nat)
    [NeZero m] [NeZero B] [NeZero (m * B)] (hCoprime : Nat.Coprime m B)
    (a : Units (ZMod m))
    (hFeasible : Nat.lcm (orderOf a) (Monoid.exponent (Units (ZMod B))) =
      Monoid.exponent (Units (ZMod (m * B))))
    (l : exponentPrimePacket (m * B)) :
    And (0 <= conditionalReturnRate m B a (l.val : Nat))
      (And (conditionalReturnRate m B a (l.val : Nat) <=
        1 / ((l.val : Nat) : Real)) (1 / ((l.val : Nat) : Real) < 1)) := by
  have hl : (1 : Real) < ((l.val : Nat) : Real) := by
    exact_mod_cast l.val.property.one_lt
  have hq : 1 / ((l.val : Nat) : Real) < 1 :=
    (div_lt_one (zero_lt_one.trans hl)).mpr hl
  unfold conditionalReturnRate
  split_ifs with hOpen
  { have hd := feasible_open_indices m B hCoprime a hFeasible l hOpen
    have hdPos : (0 : Real) <
        (returnIndex (G := Units (ZMod B))
          (Monoid.exponent (Units (ZMod (m * B)))) (l.val : Nat) : Real) := by linarith
    exact And.intro (one_div_pos.mpr hdPos).le
      (And.intro (one_div_le_one_div_of_le (zero_lt_one.trans hl) hd) hq) }
  { exact And.intro le_rfl
      (And.intro (one_div_pos.mpr (zero_lt_one.trans hl)).le hq) }

theorem conditional_pattern_nonneg (m B : Nat) (a : Units (ZMod m))
    (bits : exponentPrimePacket (m * B) -> Bool) :
    0 <= fiberProfileProbability m B a (exponentPrimePacket (m * B)) bits := by
  unfold fiberProfileProbability uniformProbability
  exact div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)

theorem conditional_patterns_sum_one (m B : Nat)
    [NeZero m] [NeZero B] [NeZero (m * B)] (hCoprime : Nat.Coprime m B)
    (a : Units (ZMod m)) :
    Finset.univ.sum (fiberProfileProbability m B a (exponentPrimePacket (m * B))) = 1 := by
  classical
  simp_rw [conditional_profile_eq_product m B hCoprime a]
  calc
    _ = Finset.univ.prod (fun l : exponentPrimePacket (m * B) =>
        Finset.univ.sum (fun bit : Bool =>
          if bit then conditionalReturnRate m B a (l.val : Nat)
          else 1 - conditionalReturnRate m B a (l.val : Nat))) :=
      (Fintype.prod_sum (fun (l : exponentPrimePacket (m * B)) (bit : Bool) =>
        if bit then conditionalReturnRate m B a (l.val : Nat)
        else 1 - conditionalReturnRate m B a (l.val : Nat))).symm
    _ = 1 := by simp

/-- Every conditional pattern is dominated by the same vacancy likelihood ratio. -/
theorem conditional_pattern_cross_comparison (m B : Nat)
    [NeZero m] [NeZero B] [NeZero (m * B)] (hCoprime : Nat.Coprime m B)
    (a : Units (ZMod m))
    (hFeasible : Nat.lcm (orderOf a) (Monoid.exponent (Units (ZMod B))) =
      Monoid.exponent (Units (ZMod (m * B))))
    (bits : exponentPrimePacket (m * B) -> Bool) :
    fiberProfileProbability m B a (exponentPrimePacket (m * B)) bits *
        vacancyFloor (exponentPrimePacket (m * B)) <=
      minimalPatternProbability (exponentPrimePacket (m * B)) bits *
        maximalOrderLiftProbability m B a := by
  classical
  let S := exponentPrimePacket (m * B)
  let r : S -> Real := fun l => conditionalReturnRate m B a (l.val : Nat)
  let s : S -> Real := fun l => 1 / ((l.val : Nat) : Real)
  have hBounds : forall l : S, And (0 <= r l) (And (r l <= s l) (s l < 1)) :=
    feasible_rate_bounds m B hCoprime a hFeasible
  let f : S -> Real := fun l => (if bits l then r l else 1 - r l) * (1 - s l)
  let g : S -> Real := fun l => (if bits l then s l else 1 - s l) * (1 - r l)
  have hf : forall l : S, 0 <= f l := by
    intro l
    have hb := hBounds l
    have hbOne : r l <= 1 := hb.2.1.trans hb.2.2.le
    dsimp only [f]
    cases bits l <;> simp only [Bool.false_eq_true, ite_false, ite_true]
    { exact mul_nonneg (sub_nonneg.mpr hbOne) (sub_nonneg.mpr hb.2.2.le) }
    { exact mul_nonneg hb.1 (sub_nonneg.mpr hb.2.2.le) }
  have hfg : forall l : S, f l <= g l := by
    intro l
    have hb := hBounds l
    dsimp only [f, g]
    cases bits l <;> simp only [Bool.false_eq_true, ite_false, ite_true] <;> nlinarith
  have hProduct : forall T : Finset S, T.prod f <= T.prod g := by
    intro T
    induction T using Finset.induction_on with
    | empty => simp
    | @insert l T hl ih =>
      rw [Finset.prod_insert hl, Finset.prod_insert hl]
      exact mul_le_mul (hfg l) ih
        (Finset.prod_nonneg (fun q _ => hf q)) ((hf l).trans (hfg l))
  have h := hProduct Finset.univ
  dsimp only [f, g] at h
  rw [Finset.prod_mul_distrib, Finset.prod_mul_distrib] at h
  rw [maximalOrderLiftProbability_eq_profile m B a,
    conditional_profile_eq_product m B hCoprime a bits,
    conditional_profile_eq_product m B hCoprime a (fun _ => false)]
  simpa only [Bool.false_eq_true, ite_false, minimalPatternProbability, vacancyFloor,
    r, s, S] using h

theorem conditional_event_cross_comparison (m B : Nat)
    [NeZero m] [NeZero B] [NeZero (m * B)] (hCoprime : Nat.Coprime m B)
    (a : Units (ZMod m))
    (hFeasible : Nat.lcm (orderOf a) (Monoid.exponent (Units (ZMod B))) =
      Monoid.exponent (Units (ZMod (m * B))))
    (A : Finset (exponentPrimePacket (m * B) -> Bool)) :
    A.sum (fiberProfileProbability m B a (exponentPrimePacket (m * B))) *
        vacancyFloor (exponentPrimePacket (m * B)) <=
      A.sum (minimalPatternProbability (exponentPrimePacket (m * B))) *
        maximalOrderLiftProbability m B a := by
  rw [Finset.sum_mul, Finset.sum_mul]
  apply Finset.sum_le_sum
  intro bits _
  exact conditional_pattern_cross_comparison m B hCoprime a hFeasible bits

theorem conditional_event_le_vacancy_ratio (m B : Nat)
    [NeZero m] [NeZero B] [NeZero (m * B)] (hCoprime : Nat.Coprime m B)
    (a : Units (ZMod m))
    (hFeasible : Nat.lcm (orderOf a) (Monoid.exponent (Units (ZMod B))) =
      Monoid.exponent (Units (ZMod (m * B))))
    (A : Finset (exponentPrimePacket (m * B) -> Bool)) :
    A.sum (fiberProfileProbability m B a (exponentPrimePacket (m * B))) <=
      (maximalOrderLiftProbability m B a / vacancyFloor (exponentPrimePacket (m * B))) *
        A.sum (minimalPatternProbability (exponentPrimePacket (m * B))) := by
  let V := maximalOrderLiftProbability m B a
  let B0 := vacancyFloor (exponentPrimePacket (m * B))
  have hB : 0 < B0 := vacancyFloor_pos _
  have h := conditional_event_cross_comparison m B hCoprime a hFeasible A
  have hScaled :
      A.sum (fiberProfileProbability m B a (exponentPrimePacket (m * B))) * B0 <=
        ((V / B0) * A.sum (minimalPatternProbability (exponentPrimePacket (m * B)))) *
          B0 := by
    calc
      _ <= A.sum (minimalPatternProbability (exponentPrimePacket (m * B))) * V := h
      _ = _ := by field_simp [ne_of_gt hB]
  exact le_of_mul_le_mul_right hScaled hB

def conditionalProfileTotalVariation (m B : Nat) (a : Units (ZMod m)) : Real :=
  (1 / 2 : Real) * Finset.univ.sum (fun bits : exponentPrimePacket (m * B) -> Bool =>
    abs (fiberProfileProbability m B a (exponentPrimePacket (m * B)) bits -
      minimalPatternProbability (exponentPrimePacket (m * B)) bits))

def conditionalProfileHellingerEnergy (m B : Nat) (a : Units (ZMod m)) : Real :=
  Finset.univ.sum (fun bits : exponentPrimePacket (m * B) -> Bool =>
    PrimeClassDeletion.repairHellingerEnergy
      (minimalPatternProbability (exponentPrimePacket (m * B)) bits)
      (fiberProfileProbability m B a (exponentPrimePacket (m * B)) bits) 0)

/-- Feasible conditional fibers obey a dimension-free total-variation bound. -/
theorem conditional_profile_variation_le_vacancy_ratio (m B : Nat)
    [NeZero m] [NeZero B] [NeZero (m * B)] (hCoprime : Nat.Coprime m B)
    (a : Units (ZMod m))
    (hFeasible : Nat.lcm (orderOf a) (Monoid.exponent (Units (ZMod B))) =
      Monoid.exponent (Units (ZMod (m * B)))) :
    conditionalProfileTotalVariation m B a <=
      1 - vacancyFloor (exponentPrimePacket (m * B)) / maximalOrderLiftProbability m B a := by
  classical
  let S := exponentPrimePacket (m * B)
  let p : (S -> Bool) -> Real := fiberProfileProbability m B a S
  let q : (S -> Bool) -> Real := minimalPatternProbability S
  let V := maximalOrderLiftProbability m B a
  let B0 := vacancyFloor S
  let O : Real := Finset.univ.sum (fun bits : S -> Bool => max (p bits - q bits) 0)
  let A : Finset (S -> Bool) := Finset.univ.filter (fun bits => q bits < p bits)
  have hB : 0 < B0 := vacancyFloor_pos S
  have hBV : B0 <= V := feasible_density_ge_floor m B hCoprime a hFeasible
  have hV : 0 < V := hB.trans_le hBV
  have hp : forall bits, 0 <= p bits := conditional_pattern_nonneg m B a
  have hpSum : Finset.univ.sum p = 1 := conditional_patterns_sum_one m B hCoprime a
  have hqSum : Finset.univ.sum q = 1 := minimal_patterns_sum_one S
  have hLedger := PrimeClassDeletion.abs_sub_sum_overweight_ledger Finset.univ q p
  rw [hqSum, hpSum] at hLedger
  have hTV : conditionalProfileTotalVariation m B a = O := by
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
  have hCross : A.sum p * B0 <= A.sum q * V :=
    conditional_event_cross_comparison m B hCoprime a hFeasible A
  have hRaw : V * conditionalProfileTotalVariation m B a <= V - B0 := by
    rw [hTV, hO]
    have hSupply := mul_nonneg (sub_nonneg.mpr hBV) (sub_nonneg.mpr hA)
    nlinarith [hCross]
  have hIdentity : V * (1 - B0 / V) = V - B0 := by
    field_simp [ne_of_gt hV]
  have hScaled :
      V * conditionalProfileTotalVariation m B a <= V * (1 - B0 / V) := by
    rw [hIdentity]
    exact hRaw
  exact le_of_mul_le_mul_left hScaled hV

theorem conditional_profile_energy_le_twice_variation (m B : Nat)
    [NeZero m] [NeZero B] [NeZero (m * B)] (hCoprime : Nat.Coprime m B)
    (a : Units (ZMod m)) :
    conditionalProfileHellingerEnergy m B a <= 2 * conditionalProfileTotalVariation m B a := by
  classical
  let S := exponentPrimePacket (m * B)
  let p : (S -> Bool) -> Real := fiberProfileProbability m B a S
  let q : (S -> Bool) -> Real := minimalPatternProbability S
  have hpSum : Finset.univ.sum p = 1 := conditional_patterns_sum_one m B hCoprime a
  have hqSum : Finset.univ.sum q = 1 := minimal_patterns_sum_one S
  have hEnergy := PrimeClassDeletion.repairHellingerEnergy_sum_le_ledger
    Finset.univ q p (fun _ => 0)
    (fun bits _ => minimal_pattern_nonneg S bits)
    (fun bits _ => conditional_pattern_nonneg m B a bits) (fun _ _ => le_rfl)
  have hLedger := PrimeClassDeletion.abs_sub_sum_overweight_ledger Finset.univ q p
  rw [hqSum, hpSum] at hEnergy hLedger
  change Finset.univ.sum (fun bits : S -> Bool =>
      PrimeClassDeletion.repairHellingerEnergy (q bits) (p bits) 0) <=
    2 * ((1 / 2 : Real) * Finset.univ.sum
      (fun bits : S -> Bool => abs (p bits - q bits)))
  linarith

theorem conditional_profile_energy_le_vacancy_ratio (m B : Nat)
    [NeZero m] [NeZero B] [NeZero (m * B)] (hCoprime : Nat.Coprime m B)
    (a : Units (ZMod m))
    (hFeasible : Nat.lcm (orderOf a) (Monoid.exponent (Units (ZMod B))) =
      Monoid.exponent (Units (ZMod (m * B)))) :
    conditionalProfileHellingerEnergy m B a <=
      2 * (1 - vacancyFloor (exponentPrimePacket (m * B)) /
        maximalOrderLiftProbability m B a) := by
  exact (conditional_profile_energy_le_twice_variation m B hCoprime a).trans
    (mul_le_mul_of_nonneg_left
      (conditional_profile_variation_le_vacancy_ratio m B hCoprime a hFeasible)
      (by norm_num : (0 : Real) <= 2))

/-- The normalized branch is exactly the branch admitting a maximal-order lift. -/
theorem conditional_density_pos_iff_feasible (m B : Nat)
    [NeZero m] [NeZero B] [NeZero (m * B)] (hCoprime : Nat.Coprime m B)
    (a : Units (ZMod m)) :
    0 < maximalOrderLiftProbability m B a <->
      Nat.lcm (orderOf a) (Monoid.exponent (Units (ZMod B))) =
        Monoid.exponent (Units (ZMod (m * B))) := by
  classical
  constructor
  { intro h
    by_contra hNot
    have hZero := CarmichaelConditionalRigidity.infeasible_density_zero m B hCoprime a hNot
    linarith }
  { intro h
    exact (vacancyFloor_pos _).trans_le (feasible_density_ge_floor m B hCoprime a h) }

end PrimeFactorOscillations.CarmichaelConditionalStability

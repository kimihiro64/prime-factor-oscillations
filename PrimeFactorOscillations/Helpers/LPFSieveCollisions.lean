/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.LPFPrimeTargetFull
import PrimeFactorOscillations.Helpers.LPFSievePrimeCutoff

/-!
# Exact local collision factors for the two- and three-form upper sieves

All coincidences among the forbidden residues are retained. These factors
will be multiplied and converted to the maintained singular divisor products.
-/

namespace PrimeFactorOscillations.LPF

private theorem three_distinct_factor (x : Real) (hx : 5 <= x) :
    (x / (x - 1)) ^ 3 <= 1 + 3 / (x - 3) := by
  have h1 : 0 < x - 1 := by linarith
  have h3 : 0 < x - 3 := by linarith
  apply (mul_le_mul_iff_of_pos_right (mul_pos (pow_pos h1 3) h3)).mp
  field_simp
  nlinarith [sq_nonneg x]

private theorem three_double_factor (x : Real) (hx : 5 <= x) :
    (x / (x - 1)) ^ 3 <=
      (1 + 2 / (x - 2)) * (1 + 1 / (x - 2)) := by
  have h1 : 0 < x - 1 := by linarith
  have h2 : 0 < x - 2 := by linarith
  apply (mul_le_mul_iff_of_pos_right (mul_pos (pow_pos h1 3) (pow_pos h2 2))).mp
  field_simp
  have hRest : 0 <= 2 * x ^ 2 - 4 * x + 1 := by nlinarith [sq_nonneg (x - 2)]
  have hProd := mul_nonneg (show 0 <= x by linarith) hRest
  nlinarith only [hProd]

private theorem three_single_factor (x : Real) (hx : 5 <= x) :
    (x / (x - 1)) ^ 3 <=
      (1 + 1 / (x - 1)) * (1 + 1 / (x - 2)) ^ 3 := by
  have h1 : 0 < x - 1 := by linarith
  have h2 : 0 < x - 2 := by linarith
  have hG : 1 <= 1 + 1 / (x - 2) := by
    have h : 0 <= 1 / (x - 2) := by positivity
    linarith
  have hPow : (1 + 1 / (x - 2)) ^ 2 <= (1 + 1 / (x - 2)) ^ 3 := by
    have h := mul_nonneg (sq_nonneg (1 + 1 / (x - 2))) (sub_nonneg.mpr hG)
    nlinarith only [h]
  calc
    _ <= (1 + 2 / (x - 2)) * (1 + 1 / (x - 2)) := three_double_factor x hx
    _ = (1 + 1 / (x - 1)) * (1 + 1 / (x - 2)) ^ 2 := by field_simp; ring
    _ <= _ := mul_le_mul_of_nonneg_left hPow (by positivity)

private theorem two_distinct_factor (x : Real) (hx : 5 <= x) :
    (x / (x - 1)) ^ 2 <= 1 + 2 / (x - 2) := by
  have h1 : 0 < x - 1 := by linarith
  have h2 : 0 < x - 2 := by linarith
  apply (mul_le_mul_iff_of_pos_right (mul_pos (pow_pos h1 2) h2)).mp
  field_simp
  nlinarith

private theorem two_single_factor (x : Real) (hx : 5 <= x) :
    (x / (x - 1)) ^ 2 <=
      (1 + 1 / (x - 1)) * (1 + 1 / (x - 2)) := by
  have h1 : 0 < x - 1 := by linarith
  have h2 : 0 < x - 2 := by linarith
  calc
    _ <= 1 + 2 / (x - 2) := two_distinct_factor x hx
    _ = _ := by field_simp; ring

noncomputable def sieveCollisionFactor (p : Nat) (a b : ZMod p) : Real :=
  (if a = 0 then singularFactor p else 1) *
  (if b = 0 then singularFactor p else 1) *
  (if a = b then singularFactor p else 1)

/-- Every root collision is counted, including all three pair coincidences. -/
theorem threeResidue_euler_factor_lower_bound (p : Nat) (hp : 5 <= p)
    (a b : ZMod p) :
    ((p : Real) / ((p : Real) - 1)) ^ 3 <=
      (1 + (({0, a, b} : Finset (ZMod p)).card : Real) /
        ((p : Real) - (({0, a, b} : Finset (ZMod p)).card : Real))) *
      sieveCollisionFactor p a b := by
  classical
  have hpR : (5 : Real) <= (p : Real) := by exact_mod_cast hp
  by_cases ha : a = 0
  next =>
    subst a
    by_cases hb : b = 0
    next =>
      subst b
      simpa [sieveCollisionFactor, singularFactor, pow_succ, mul_assoc] using
        three_single_factor (p : Real) hpR
    next =>
      simpa [sieveCollisionFactor, singularFactor, hb, Ne.symm hb] using
        three_double_factor (p : Real) hpR
  next =>
    by_cases hb : b = 0
    next =>
      subst b
      simpa [sieveCollisionFactor, singularFactor, ha, Ne.symm ha] using
        three_double_factor (p : Real) hpR
    next =>
      by_cases hab : a = b
      next =>
        subst b
        simpa [sieveCollisionFactor, singularFactor, ha, Ne.symm ha] using
          three_double_factor (p : Real) hpR
      next =>
        simpa [sieveCollisionFactor, singularFactor, ha, hb, hab,
          Ne.symm ha, Ne.symm hb, Ne.symm hab] using three_distinct_factor (p : Real) hpR

/-- The two-root local comparison retains its collision factor as well. -/
theorem twoResidue_euler_factor_lower_bound (p : Nat) (hp : 5 <= p) (a : ZMod p) :
    ((p : Real) / ((p : Real) - 1)) ^ 2 <=
      (1 + (({0, a} : Finset (ZMod p)).card : Real) /
        ((p : Real) - (({0, a} : Finset (ZMod p)).card : Real))) *
      (if a = 0 then singularFactor p else 1) := by
  classical
  have hpR : (5 : Real) <= (p : Real) := by exact_mod_cast hp
  by_cases ha : a = 0
  next =>
    subst a
    simpa [singularFactor] using two_single_factor (p : Real) hpR
  next =>
    simpa [ha, Ne.symm ha] using two_distinct_factor (p : Real) hpR

theorem threeResidue_card_bounds (p : Nat) (a b : ZMod p) :
    And (0 < ({0, a, b} : Finset (ZMod p)).card)
      (({0, a, b} : Finset (ZMod p)).card <= 3) := by
  classical
  have hPair : ({a, b} : Finset (ZMod p)).card <= 2 := by
    simpa using Finset.card_insert_le a ({b} : Finset (ZMod p))
  have hTriple := Finset.card_insert_le 0 ({a, b} : Finset (ZMod p))
  exact And.intro (Finset.card_pos.mpr (Exists.intro 0 (by simp))) (by omega)

theorem twoResidue_card_bounds (p : Nat) (a : ZMod p) :
    And (0 < ({0, a} : Finset (ZMod p)).card)
      (({0, a} : Finset (ZMod p)).card <= 2) := by
  classical
  exact And.intro (Finset.card_pos.mpr (Exists.intro 0 (by simp)))
    (by simpa using Finset.card_insert_le 0 ({a} : Finset (ZMod p)))

/-- Natural separation, with both subtraction branches retained. -/
theorem natCast_eq_iff_dvd_separation (p t s : Nat) :
    ((t : ZMod p) = (s : ZMod p)) <-> Dvd.dvd p ((t - s) + (s - t)) := by
  by_cases h : t <= s
  next =>
    simpa only [Nat.sub_eq_zero_of_le h, zero_add] using
      (ZMod.natCast_eq_natCast_iff t s p).trans (Nat.modEq_iff_dvd' h)
  next =>
    have h' : s <= t := by omega
    have hSymm : ((t : ZMod p) = (s : ZMod p)) <-> ((s : ZMod p) = (t : ZMod p)) :=
      eq_comm
    simpa only [Nat.sub_eq_zero_of_le h', add_zero] using
      hSymm.trans ((ZMod.natCast_eq_natCast_iff s t p).trans (Nat.modEq_iff_dvd' h'))

private theorem factor_one_le (p : Nat) (hp : 3 <= p) : 1 <= singularFactor p := by
  have hpR : (3 : Real) <= (p : Real) := by exact_mod_cast hp
  have hDen : 0 < (p : Real) - 2 := by linarith
  have h : 0 <= 1 / ((p : Real) - 2) := by positivity
  dsimp [singularFactor]
  linarith

private theorem product_compare (P : Finset Nat) (f g : Nat -> Real)
    (hf : forall p, Membership.mem P p -> 0 <= f p)
    (hfg : forall p, Membership.mem P p -> f p <= g p) :
    Finset.prod P f <= Finset.prod P g := by
  classical
  induction P using Finset.induction_on with
  | empty => simp
  | @insert p P hp ih =>
    rw [Finset.prod_insert hp, Finset.prod_insert hp]
    have hfP := fun q hq => hf q (Finset.mem_insert_of_mem hq)
    have hfgP := fun q hq => hfg q (Finset.mem_insert_of_mem hq)
    exact mul_le_mul (hfg p (Finset.mem_insert_self p P)) (ih hfP hfgP)
      (Finset.prod_nonneg hfP)
      (le_trans (hf p (Finset.mem_insert_self p P)) (hfg p (Finset.mem_insert_self p P)))

private theorem product_subset_compare {P R : Finset Nat} (f : Nat -> Real)
    (hSub : P <= R) (hf : forall p, Membership.mem R p -> 1 <= f p) :
    Finset.prod P f <= Finset.prod R f := by
  classical
  have hRest : 1 <= Finset.prod (R \ P) f := by
    have h := product_compare (R \ P) (fun _ => 1) f
      (fun _ _ => zero_le_one) (fun p hp => hf p (Finset.mem_sdiff.mp hp).1)
    simpa using h
  have hNonneg : 0 <= Finset.prod P f := Finset.prod_nonneg
    (fun p hp => le_trans zero_le_one (hf p (hSub hp)))
  have h := mul_le_mul_of_nonneg_right hRest hNonneg
  simpa only [one_mul, Finset.prod_sdiff hSub] using h

private theorem full_singular_nonneg (v : Nat) : 0 <= singularDivisorProduct v := by
  apply Finset.prod_nonneg
  intro p hp
  exact le_trans zero_le_one (factor_one_le p (Finset.mem_filter.mp hp).2)

/-- Selected divisor factors extend monotonically to the complete positive argument. -/
theorem selected_singular_product_le (P : Finset Nat) (v : Nat) (hv : 0 < v)
    (hP : forall p, Membership.mem P p -> And (Nat.Prime p) (3 <= p)) :
    Finset.prod (P.filter (fun p => Dvd.dvd p v)) singularFactor <=
      singularDivisorProduct v := by
  classical
  apply product_subset_compare
  next =>
    intro p hp
    have hs := Finset.mem_filter.mp hp
    exact Finset.mem_filter.mpr (And.intro
      (Nat.mem_primeFactors.mpr
        (And.intro (hP p hs.1).1 (And.intro hs.2 (Nat.ne_of_gt hv)))) (hP p hs.1).2)
  next =>
    intro p hp
    exact factor_one_le p (Finset.mem_filter.mp hp).2

/-- The exact three-root correction is bounded by all three full singular products. -/
theorem sieveCollisionFactor_product_le (P : Finset Nat) (t s : Nat)
    (ht : 0 < t) (hs : 0 < s) (hne : Not (t = s))
    (hP : forall p, Membership.mem P p -> And (Nat.Prime p) (3 <= p)) :
    Finset.prod P (fun p => sieveCollisionFactor p (t : ZMod p) (s : ZMod p)) <=
      singularDivisorProduct t * singularDivisorProduct s *
        singularDivisorProduct ((t - s) + (s - t)) := by
  classical
  have hDiff : 0 < (t - s) + (s - t) := by omega
  have htBound := selected_singular_product_le P t ht hP
  have hsBound := selected_singular_product_le P s hs hP
  have hdBound := selected_singular_product_le P _ hDiff hP
  have hNonneg : forall v, 0 <= Finset.prod (P.filter (fun p => Dvd.dvd p v)) singularFactor :=
    fun v => Finset.prod_nonneg (fun p hp =>
      le_trans zero_le_one (factor_one_le p (hP p (Finset.mem_filter.mp hp).1).2))
  have hPair := mul_le_mul htBound hsBound (hNonneg s) (full_singular_nonneg t)
  have hTriple := mul_le_mul hPair hdBound (hNonneg _)
    (mul_nonneg (full_singular_nonneg t) (full_singular_nonneg s))
  convert hTriple using 1
  simp only [sieveCollisionFactor, ZMod.natCast_eq_zero_iff,
    natCast_eq_iff_dvd_separation, Finset.prod_mul_distrib, Finset.prod_filter]

/-- Three-form Euler factors retain the complete arithmetic collision allowance. -/
theorem threeResidue_eulerProduct_lower_bound (P : Finset Nat) (t s : Nat)
    (ht : 0 < t) (hs : 0 < s) (hne : Not (t = s))
    (hP : forall p, Membership.mem P p -> And (Nat.Prime p) (5 <= p)) :
    Finset.prod P (fun p => ((p : Real) / ((p : Real) - 1)) ^ 3) <=
      sieveEulerProduct P (fun p => ({0, (t : ZMod p), (s : ZMod p)} : Finset (ZMod p))) *
        (singularDivisorProduct t * singularDivisorProduct s *
          singularDivisorProduct ((t - s) + (s - t))) := by
  classical
  let A := fun p => ({0, (t : ZMod p), (s : ZMod p)} : Finset (ZMod p))
  have hA : forall p, Membership.mem P p -> And (0 < (A p).card) ((A p).card < p) := by
    intro p hp
    have h := threeResidue_card_bounds p (t : ZMod p) (s : ZMod p)
    exact And.intro h.1 (by have h5 := (hP p hp).2; dsimp [A]; omega)
  have hLocal := product_compare P
    (fun p => ((p : Real) / ((p : Real) - 1)) ^ 3)
    (fun p => (1 + ((A p).card : Real) / ((p : Real) - (A p).card)) *
      sieveCollisionFactor p (t : ZMod p) (s : ZMod p))
    (fun p hp => by
      have h5 : (5 : Real) <= (p : Real) := by exact_mod_cast (hP p hp).2
      have hDen : 0 < (p : Real) - 1 := by linarith
      positivity)
    (fun p hp => threeResidue_euler_factor_lower_bound p (hP p hp).2 _ _)
  rw [Finset.prod_mul_distrib] at hLocal
  have hCollision := sieveCollisionFactor_product_le P t s ht hs hne
    (fun p hp => And.intro (hP p hp).1 (by have h5 := (hP p hp).2; omega))
  exact hLocal.trans (mul_le_mul_of_nonneg_left hCollision
    (le_of_lt (sieveEulerProduct_pos P A hA)))

/-- The two-form Euler comparison uses the single complete singular product. -/
theorem twoResidue_eulerProduct_lower_bound (P : Finset Nat) (t : Nat) (ht : 0 < t)
    (hP : forall p, Membership.mem P p -> And (Nat.Prime p) (5 <= p)) :
    Finset.prod P (fun p => ((p : Real) / ((p : Real) - 1)) ^ 2) <=
      sieveEulerProduct P (fun p => ({0, (t : ZMod p)} : Finset (ZMod p))) *
        singularDivisorProduct t := by
  classical
  let A := fun p => ({0, (t : ZMod p)} : Finset (ZMod p))
  have hA : forall p, Membership.mem P p -> And (0 < (A p).card) ((A p).card < p) := by
    intro p hp
    have h := twoResidue_card_bounds p (t : ZMod p)
    exact And.intro h.1 (by have h5 := (hP p hp).2; dsimp [A]; omega)
  have hLocal := product_compare P
    (fun p => ((p : Real) / ((p : Real) - 1)) ^ 2)
    (fun p => (1 + ((A p).card : Real) / ((p : Real) - (A p).card)) *
      (if (t : ZMod p) = 0 then singularFactor p else 1))
    (fun p hp => sq_nonneg _)
    (fun p hp => twoResidue_euler_factor_lower_bound p (hP p hp).2 _)
  rw [Finset.prod_mul_distrib] at hLocal
  have hCollision := selected_singular_product_le P t ht
    (fun p hp => And.intro (hP p hp).1 (by have h5 := (hP p hp).2; omega))
  simp only [ZMod.natCast_eq_zero_iff, <- Finset.prod_filter] at hLocal
  exact hLocal.trans (mul_le_mul_of_nonneg_left hCollision
    (le_of_lt (sieveEulerProduct_pos P A hA)))

end PrimeFactorOscillations.LPF

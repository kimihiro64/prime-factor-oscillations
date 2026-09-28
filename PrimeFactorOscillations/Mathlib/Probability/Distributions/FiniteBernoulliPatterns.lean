/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Polynomial.Coeff
import PrimeFactorOscillations.Mathlib.Probability.Distributions.FiniteBernoulliMass

/-! # Exact finite Bernoulli coefficients as sums over cardinality patterns -/

set_option autoImplicit false
set_option Elab.async false

namespace List

theorem bernoulliMass_eq_coeff_product {R : Type*} [CommRing R] (s : List R) (r : Nat) :
    bernoulliMass s r =
      ((s.map (fun a => Polynomial.C a * Polynomial.X + Polynomial.C (1 - a))).prod).coeff r := by
  induction s generalizing r with
  | nil => cases r <;> simp [bernoulliMass, Polynomial.coeff_one]
  | cons a s ih =>
    cases r with
    | zero =>
      simp only [bernoulliMass, map_cons, prod_cons, add_mul, mul_assoc,
        Polynomial.coeff_add, Polynomial.coeff_C_mul, Polynomial.coeff_X_mul_zero,
        mul_zero, zero_add, <- ih 0]
    | succ r =>
      simp only [bernoulliMass, map_cons, prod_cons, add_mul, mul_assoc,
        Polynomial.coeff_add, Polynomial.coeff_C_mul, Polynomial.coeff_X_mul,
        <- ih r, <- ih (r + 1)]
      ring

end List

namespace Finset

theorem coeff_product_bernoulli_eq_sum {A R : Type*} [DecidableEq A] [CommRing R]
    (s : Finset A) (eta : A -> R) (r : Nat) :
    (s.prod (fun a => Polynomial.C (eta a) * Polynomial.X + Polynomial.C (1 - eta a))).coeff r =
      (s.powersetCard r).sum (fun t =>
        t.prod eta * (SDiff.sdiff s t).prod (fun a => 1 - eta a)) := by
  classical
  have hterm (t : Finset A) :
      ((t.prod (fun a => Polynomial.C (eta a) * Polynomial.X)) *
        (SDiff.sdiff s t).prod (fun a => Polynomial.C (1 - eta a))).coeff r =
      if t.card = r then t.prod eta * (SDiff.sdiff s t).prod (fun a => 1 - eta a) else 0 := by
    have hpoly : (t.prod (fun a => Polynomial.C (eta a) * Polynomial.X)) *
        (SDiff.sdiff s t).prod (fun a => Polynomial.C (1 - eta a)) =
        Polynomial.C (t.prod eta * (SDiff.sdiff s t).prod (fun a => 1 - eta a)) *
          Polynomial.X ^ t.card := by
      rw [prod_mul_distrib, prod_const, <- map_prod, <- map_prod, map_mul]
      ring
    rw [hpoly, Polynomial.coeff_C_mul_X_pow]
    simp only [eq_comm]
  have hset : s.powerset.filter (fun t => t.card = r) = s.powersetCard r := by
    apply Finset.ext
    intro t
    simp only [mem_filter, mem_powerset, mem_powersetCard]
  rw [prod_add, Polynomial.finsetSum_coeff]
  calc
    _ = s.powerset.sum (fun t =>
        if t.card = r then t.prod eta * (SDiff.sdiff s t).prod (fun a => 1 - eta a) else 0) :=
      sum_congr rfl (fun t _ => hterm t)
    _ = _ := by rw [<- sum_filter, hset]

theorem bernoulliMass_eq_pattern_sum {A R : Type*} [DecidableEq A] [CommRing R]
    (s : Finset A) (eta : A -> R) (r : Nat) :
    List.bernoulliMass (s.toList.map eta) r =
      (s.powersetCard r).sum (fun t =>
        s.prod (fun a => if Membership.mem t a then eta a else 1 - eta a)) := by
  classical
  rw [List.bernoulliMass_eq_coeff_product, List.map_map, prod_map_toList]
  simp only [Function.comp_def]
  rw [coeff_product_bernoulli_eq_sum]
  apply sum_congr rfl
  intro t ht
  have hts := (mem_powersetCard.mp ht).1
  have hp := prod_piecewise s t eta (fun a => 1 - eta a)
  rw [inter_eq_right.mpr hts] at hp
  simpa only [Finset.piecewise] using hp.symm

end Finset

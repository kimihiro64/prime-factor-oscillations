/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/

import Mathlib.Topology.Algebra.InfiniteSum.Order
import PrimeFactorOscillations.Proof.PrimeClassDeletion.CappedPrimeWeights

/-! # Infinite missing-cost optimality from exact finite complements

All sums retain the prime filter and the class complement. A convergent
competitor missing cost bounds every finite greedy missing cost, forcing
summability of the greedy series before either infinite sum is compared.
-/

set_option autoImplicit false
set_option Elab.async false

namespace PrimeFactorOscillations.PrimeClassDeletion

open PrimeFactorOscillations.PrimeClassSampling

noncomputable def primeClassMissingWeight (P : Set Nat) (w : Nat -> Real)
    (p : Nat) : Real := by
  classical
  exact if And (Nat.Prime p) (Not (Membership.mem P p)) then w p else 0

theorem primeClassPrefix_complement_weight_sum (P : Set Nat) (w : Nat -> Real)
    (X : Nat) :
    (primeClassPrefix P X).sum w +
      (primeClassPrefix (fun p => Not (Membership.mem P p)) X).sum w =
        (primeClassPrefix Set.univ X).sum w := by
  classical
  have hP : primeClassPrefix P X =
      ((Finset.Icc 2 X).filter Nat.Prime).filter (fun p => Membership.mem P p) := by
    ext p
    simp [primeClassPrefix, and_assoc]
  have hC : primeClassPrefix (fun p => Not (Membership.mem P p)) X =
      ((Finset.Icc 2 X).filter Nat.Prime).filter
        (fun p => Not (Membership.mem P p)) := by
    ext p
    simp only [primeClassPrefix, Finset.mem_filter]
    change And (Membership.mem (Finset.Icc 2 X) p)
      (And (Nat.Prime p) (Not (Membership.mem P p))) <->
      And (And (Membership.mem (Finset.Icc 2 X) p) (Nat.Prime p))
        (Not (Membership.mem P p))
    exact and_assoc.symm
  rw [hP, hC]
  simpa only [primeClassPrefix, Set.mem_univ, and_true] using
    Finset.sum_filter_add_sum_filter_not
      ((Finset.Icc 2 X).filter Nat.Prime) (fun p => Membership.mem P p) w

theorem greedyPrimeClass_missing_weight_prefix_le (P : Set Nat)
    (hP : forall t : Real, 2 <= t -> primeClassThetaReal P t <= t)
    (w : Nat -> Real)
    (hw0 : forall p : Nat, Nat.Prime p -> 0 <= w p)
    (hw : forall p q : Nat, Nat.Prime p -> Nat.Prime q -> p <= q -> w q <= w p)
    (X : Nat) :
    (primeClassPrefix (fun p => Not (Membership.mem greedyPrimeClass p)) X).sum w <=
      (primeClassPrefix (fun p => Not (Membership.mem P p)) X).sum w := by
  by_cases hx : 2 <= X
  case pos =>
    have hxR : (2 : Real) <= X := by exact_mod_cast hx
    have hs := greedyPrimeClass_local_weight_dominance P (X : Real) hxR
      (fun t ht _ => hP t ht) w hw0 hw
    rw [Nat.floor_natCast] at hs
    have hS := primeClassPrefix_complement_weight_sum greedyPrimeClass w X
    have hT := primeClassPrefix_complement_weight_sum P w X
    linarith only [hs, hS, hT]
  case neg =>
    classical
    have hlt : X < 2 := Nat.lt_of_not_ge hx
    simp [primeClassPrefix, Finset.Icc_eq_empty_of_lt hlt]

theorem primeClassMissingWeight_nonneg (P : Set Nat) (w : Nat -> Real)
    (hw0 : forall p : Nat, Nat.Prime p -> 0 <= w p) (p : Nat) :
    0 <= primeClassMissingWeight P w p := by
  classical
  unfold primeClassMissingWeight
  split_ifs with h
  case pos => exact hw0 p h.1
  case neg => exact le_refl 0

theorem sum_primeClassMissingWeight_le_prefix (P : Set Nat) (w : Nat -> Real)
    (hw0 : forall p : Nat, Nat.Prime p -> 0 <= w p) (S : Finset Nat) :
    S.sum (primeClassMissingWeight P w) <=
      (primeClassPrefix (fun p => Not (Membership.mem P p)) (S.sup id)).sum w := by
  classical
  change S.sum (fun p => if And (Nat.Prime p) (Not (Membership.mem P p))
    then w p else 0) <= _
  rw [<- Finset.sum_filter]
  apply Finset.sum_le_sum_of_subset_of_nonneg
  case h =>
    intro p hp
    have hm := Finset.mem_filter.mp hp
    exact Finset.mem_filter.mpr (And.intro
      (Finset.mem_Icc.mpr (And.intro hm.2.1.two_le (Finset.le_sup (f := id) hm.1))) hm.2)
  case hf =>
    intro p hp _
    exact hw0 p (primeClassPrefix_prime _ _ p hp)

theorem primeClassMissingWeight_prefix_le_tsum (P : Set Nat) (w : Nat -> Real)
    (hw0 : forall p : Nat, Nat.Prime p -> 0 <= w p)
    (hsum : Summable (primeClassMissingWeight P w)) (X : Nat) :
    (primeClassPrefix (fun p => Not (Membership.mem P p)) X).sum w <=
      tsum (primeClassMissingWeight P w) := by
  classical
  have heq :
      (primeClassPrefix (fun p => Not (Membership.mem P p)) X).sum w =
      (primeClassPrefix (fun p => Not (Membership.mem P p)) X).sum
        (primeClassMissingWeight P w) := by
    apply Finset.sum_congr rfl
    intro p hp
    have hm := (Finset.mem_filter.mp hp).2
    have hm' : And (Nat.Prime p) (Not (Membership.mem P p)) := And.intro hm.1 hm.2
    rw [primeClassMissingWeight, ite_eq_left hm']
  rw [heq]
  exact hsum.sum_le_tsum _ (fun p _ => primeClassMissingWeight_nonneg P w hw0 p)

theorem greedyPrimeClass_missing_weight_summable (P : Set Nat)
    (hP : forall t : Real, 2 <= t -> primeClassThetaReal P t <= t)
    (w : Nat -> Real)
    (hw0 : forall p : Nat, Nat.Prime p -> 0 <= w p)
    (hw : forall p q : Nat, Nat.Prime p -> Nat.Prime q -> p <= q -> w q <= w p)
    (hsum : Summable (primeClassMissingWeight P w)) :
    And (Summable (primeClassMissingWeight greedyPrimeClass w))
      (tsum (primeClassMissingWeight greedyPrimeClass w) <=
        tsum (primeClassMissingWeight P w)) := by
  have hfinite : forall S : Finset Nat,
      S.sum (primeClassMissingWeight greedyPrimeClass w) <=
        tsum (primeClassMissingWeight P w) := by
    intro S
    exact (sum_primeClassMissingWeight_le_prefix greedyPrimeClass w hw0 S).trans
      ((greedyPrimeClass_missing_weight_prefix_le P hP w hw0 hw (S.sup id)).trans
        (primeClassMissingWeight_prefix_le_tsum P w hw0 hsum (S.sup id)))
  have hgreedy : Summable (primeClassMissingWeight greedyPrimeClass w) :=
    summable_of_sum_le (primeClassMissingWeight_nonneg greedyPrimeClass w hw0) hfinite
  exact And.intro hgreedy
    (le_of_tendsto hgreedy.hasSum (Filter.Eventually.of_forall hfinite))

noncomputable def primeEulerLogWeight (p : Nat) : Real :=
  -Real.log (1 - 1 / (p : Real))

theorem primeEulerLogWeight_nonneg (p : Nat) (hp : Nat.Prime p) :
    0 <= primeEulerLogWeight p := by
  have hp1 : (1 : Real) < p := by exact_mod_cast hp.one_lt
  have hp0 : (0 : Real) < p := lt_trans zero_lt_one hp1
  have hsmall : (1 : Real) / p < 1 := (div_lt_one hp0).mpr hp1
  have hb : 0 < 1 - 1 / (p : Real) := sub_pos.mpr hsmall
  exact neg_nonneg.mpr (Real.log_nonpos hb.le
    (sub_le_self 1 (one_div_nonneg.mpr hp0.le)))

theorem primeEulerLogWeight_antitone (p q : Nat) (hp : Nat.Prime p)
    (_hq : Nat.Prime q) (hpq : p <= q) :
    primeEulerLogWeight q <= primeEulerLogWeight p := by
  have hp1 : (1 : Real) < p := by exact_mod_cast hp.one_lt
  have hp0 : (0 : Real) < p := lt_trans zero_lt_one hp1
  have hsmall : (1 : Real) / p < 1 := (div_lt_one hp0).mpr hp1
  have hrecip : (1 : Real) / q <= 1 / p :=
    one_div_le_one_div_of_le hp0 (Nat.cast_le.mpr hpq)
  exact neg_le_neg (Real.log_le_log (sub_pos.mpr hsmall) (sub_le_sub_left hrecip 1))

theorem greedyPrimeClass_missing_logEulerCost (P : Set Nat)
    (hP : forall t : Real, 2 <= t -> primeClassThetaReal P t <= t)
    (hsum : Summable (primeClassMissingWeight P primeEulerLogWeight)) :
    And (Summable (primeClassMissingWeight greedyPrimeClass primeEulerLogWeight))
      (tsum (primeClassMissingWeight greedyPrimeClass primeEulerLogWeight) <=
        tsum (primeClassMissingWeight P primeEulerLogWeight)) :=
  greedyPrimeClass_missing_weight_summable P hP primeEulerLogWeight
    primeEulerLogWeight_nonneg primeEulerLogWeight_antitone hsum

end PrimeFactorOscillations.PrimeClassDeletion

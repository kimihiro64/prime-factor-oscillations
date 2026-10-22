/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.PrimeClassSamplingEuler
import PrimeFactorOscillations.Proof.PrimeClassDeletion.PrimePowerComponentUniformEuler

/-!
# The complete supported integer series of a thin prime class

Every finite integer subset is contained in one finite prime support.
The uniform geometric budget therefore proves summability of the full
class-supported series. Its reciprocal series defines a normalized law.
-/

set_option autoImplicit false
set_option Elab.async false

namespace PrimeFactorOscillations.PrimeClassSampling

def classPrimePowerSupported (P : Set Nat) (a : Nat) : Prop :=
  And (0 < a) (forall p : Nat,
    Membership.mem a.factorization.support p -> Membership.mem P p)

noncomputable def classPrimePowerWeight
    (P : Set Nat) (sigma : Real) (a : Nat) : Real := by
  classical
  exact if classPrimePowerSupported P a then (a : Real) ^ (-sigma) else 0

theorem classPrimePowerWeight_nonneg (P : Set Nat) (sigma : Real) (a : Nat) :
    0 <= classPrimePowerWeight P sigma a := by
  unfold classPrimePowerWeight
  split_ifs
  case pos => exact Real.rpow_nonneg (Nat.cast_nonneg _) _
  case neg => exact le_refl 0

theorem classPrimePowerWeight_one (P : Set Nat) (sigma : Real) :
    classPrimePowerWeight P sigma 1 = 1 := by
  classical
  have h : classPrimePowerSupported P 1 := by
    refine And.intro Nat.zero_lt_one ?_
    intro p hp
    simp at hp
  simp [classPrimePowerWeight, h]

theorem classPrimePowerWeight_finite_sum_le_uniform
    (P : Set Nat) (t : Finset Nat) (sigma : Real) (hs : 0 < sigma)
    (hsum : Summable (classPowerWeight P sigma)) :
    t.sum (classPrimePowerWeight P sigma) <=
      Real.exp ((2 / (1 - (2 : Real) ^ (-sigma))) *
        tsum (classPowerWeight P sigma)) := by
  classical
  let u := t.filter (classPrimePowerSupported P)
  let s := u.biUnion (fun a => a.factorization.support)
  have hpositive (a : Nat) (ha : Membership.mem u a) : 0 < a :=
    (Finset.mem_filter.mp ha).2.1
  have hsupport (a : Nat) (ha : Membership.mem u a) (p : Nat)
      (hp : Membership.mem a.factorization.support p) : Membership.mem s p :=
    Finset.mem_biUnion.mpr (Exists.intro a (And.intro ha hp))
  have hprime (p : Nat) (hp : Membership.mem s p) : Nat.Prime p := by
    have hd := Finset.mem_biUnion.mp hp
    have hm : Membership.mem (Exists.choose hd).factorization.support p :=
      (Exists.choose_spec hd).2
    rw [Nat.support_factorization] at hm
    exact (Nat.mem_primeFactors.mp hm).1
  have hP (p : Nat) (hp : Membership.mem s p) : Membership.mem P p := by
    have hd := Finset.mem_biUnion.mp hp
    have ha : Membership.mem u (Exists.choose hd) := (Exists.choose_spec hd).1
    exact (Finset.mem_filter.mp ha).2.2 p (Exists.choose_spec hd).2
  have heq : t.sum (classPrimePowerWeight P sigma) =
      u.sum (fun a => (a : Real) ^ (-sigma)) := by
    simp only [u, Finset.sum_filter]
    rfl
  rw [heq]
  exact (supported_primePower_finite_sum_le_euler
    s u hprime hpositive hsupport sigma hs).trans
      (primePowerGeometricBudget_uniform P s hprime hP sigma hs hsum)

theorem classPrimePowerWeight_summable
    (P : Set Nat) (sigma : Real) (hs : 0 < sigma)
    (hsum : Summable (classPowerWeight P sigma)) :
    Summable (classPrimePowerWeight P sigma) := by
  apply summable_of_sum_le
  case hf => exact classPrimePowerWeight_nonneg P sigma
  case h => exact fun t => classPrimePowerWeight_finite_sum_le_uniform P t sigma hs hsum

theorem classPrimePowerWeight_tsum_le_uniform
    (P : Set Nat) (sigma : Real) (hs : 0 < sigma)
    (hsum : Summable (classPowerWeight P sigma)) :
    tsum (classPrimePowerWeight P sigma) <=
      Real.exp ((2 / (1 - (2 : Real) ^ (-sigma))) *
        tsum (classPowerWeight P sigma)) := by
  apply Real.tsum_le_of_sum_le
  case hf => exact classPrimePowerWeight_nonneg P sigma
  case h => exact fun t => classPrimePowerWeight_finite_sum_le_uniform P t sigma hs hsum

theorem classPrimePowerWeight_tsum_pos
    (P : Set Nat) (sigma : Real) (hs : 0 < sigma)
    (hsum : Summable (classPowerWeight P sigma)) :
    0 < tsum (classPrimePowerWeight P sigma) := by
  have hsummable := classPrimePowerWeight_summable P sigma hs hsum
  have hone : (1 : Real) <= tsum (classPrimePowerWeight P sigma) := by
    calc
      1 = ({1} : Finset Nat).sum (classPrimePowerWeight P sigma) := by
        simp only [Finset.sum_singleton, classPrimePowerWeight_one]
      _ <= _ := Summable.sum_le_tsum {1}
        (fun a ha => classPrimePowerWeight_nonneg P sigma a) hsummable
  exact lt_of_lt_of_le zero_lt_one hone

noncomputable def classPrimePowerReference (P : Set Nat) (a : Nat) : Real :=
  classPrimePowerWeight P 1 a / tsum (classPrimePowerWeight P 1)

theorem classPrimePowerReference_nonneg (P : Set Nat)
    (hsum : Summable (classPowerWeight P 1)) (a : Nat) :
    0 <= classPrimePowerReference P a :=
  div_nonneg (classPrimePowerWeight_nonneg P 1 a)
    (classPrimePowerWeight_tsum_pos P 1 zero_lt_one hsum).le

theorem classPrimePowerReference_hasSum_one (P : Set Nat)
    (hsum : Summable (classPowerWeight P 1)) :
    HasSum (classPrimePowerReference P) 1 := by
  have hsummable := classPrimePowerWeight_summable P 1 zero_lt_one hsum
  have h := hsummable.hasSum.div_const (tsum (classPrimePowerWeight P 1))
  rw [div_self (ne_of_gt (classPrimePowerWeight_tsum_pos P 1 zero_lt_one hsum))] at h
  exact h

end PrimeFactorOscillations.PrimeClassSampling

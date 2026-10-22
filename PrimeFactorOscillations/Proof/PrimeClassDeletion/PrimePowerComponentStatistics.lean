/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Proof.PrimeClassDeletion.PrimePowerComponentClassLaw

/-!
# Uniform contraction under arbitrary component statistics

The statistic may take values in any type. Fiberwise summation preserves
mass and contracts the complete l1 error, so the original Euler constant
works for every statistic without an additional parameter.
-/

set_option autoImplicit false
set_option Elab.async false

namespace PrimeFactorOscillations.PrimeClassSampling

noncomputable def componentStatisticMass {B : Type*}
    (f : Nat -> B) (mass : Nat -> Real) (b : B) : Real :=
  tsum (fun a : {a : Nat // f a = b} => mass a.val)

theorem componentStatisticMass_nonneg {B : Type*}
    (f : Nat -> B) (mass : Nat -> Real) (hm : forall a, 0 <= mass a) (b : B) :
    0 <= componentStatisticMass f mass b :=
  tsum_nonneg (fun a => hm a.val)

theorem componentStatisticMass_hasSum {B : Type*}
    (f : Nat -> B) (mass : Nat -> Real) (M : Real) (hm : HasSum mass M) :
    HasSum (componentStatisticMass f mass) M :=
  hm.tsum_fiberwise f

theorem componentStatisticMass_l1_contraction {B : Type*}
    (f : Nat -> B) (u v : Nat -> Real)
    (hu : Summable u) (hv : Summable v)
    (habs : Summable (fun a => abs (u a - v a))) :
    And (Summable (fun b => abs
      (componentStatisticMass f u b - componentStatisticMass f v b)))
      (tsum (fun b => abs
        (componentStatisticMass f u b - componentStatisticMass f v b)) <=
          tsum (fun a => abs (u a - v a))) := by
  have hgroup := habs.hasSum.tsum_fiberwise f
  have hpoint (b : B) : abs
      (componentStatisticMass f u b - componentStatisticMass f v b) <=
        tsum (fun a : {a : Nat // f a = b} => abs (u a.val - v a.val)) := by
    have huf := hu.subtype (fun a => f a = b)
    have hvf := hv.subtype (fun a => f a = b)
    have haf := habs.subtype (fun a => f a = b)
    have hdf := huf.sub hvf
    have hsum : (tsum (fun a : {a : Nat // f a = b} => u a.val - v a.val)) =
        componentStatisticMass f u b - componentStatisticMass f v b := by
      simpa only [Function.comp_apply, componentStatisticMass] using huf.tsum_sub hvf
    rw [<- hsum]
    have hlo := Summable.tsum_le_tsum
      (fun a : {a : Nat // f a = b} => neg_abs_le (u a.val - v a.val)) haf.neg hdf
    have hhi := Summable.tsum_le_tsum
      (fun a : {a : Nat // f a = b} => le_abs_self (u a.val - v a.val)) hdf haf
    rw [tsum_neg] at hlo
    exact abs_le.mpr (And.intro hlo hhi)
  have hout : Summable (fun b => abs
      (componentStatisticMass f u b - componentStatisticMass f v b)) :=
    hgroup.summable.of_nonneg_of_le (fun b => abs_nonneg _) hpoint
  refine And.intro hout ?_
  exact (Summable.tsum_le_tsum hpoint hout hgroup.summable).trans_eq hgroup.tsum_eq

theorem classPrimePowerComponent_statistic_totalVariation_le {B : Type*}
    (f : Nat -> B) (P : Set Nat) (N : Nat) (hN : 0 < N)
    (sigma : Real) (hs : 0 < sigma) (hs1 : sigma <= 1)
    (hsum : Summable (classPowerWeight P sigma)) :
    tsum (fun b => abs
      (componentStatisticMass f (classPrimePowerComponentProbability P N) b -
        componentStatisticMass f (classPrimePowerReference P) b)) / 2 <=
      min 1 ((N : Real) ^ (sigma - 1) * classPrimePowerErrorConstant P sigma / 2) := by
  have hsum1 := classPowerWeight_one_summable P sigma hs1 hsum
  have hsample := classPrimePowerComponentProbability_hasSum_one P N hN
  have href := classPrimePowerReference_hasSum_one P hsum1
  have herror := classPrimePowerComponent_full_l1_error P N hN sigma hs hs1 hsum
  have hcontract := componentStatisticMass_l1_contraction f
    (classPrimePowerComponentProbability P N) (classPrimePowerReference P)
    hsample.summable href.summable herror.1
  exact (div_le_div_of_nonneg_right hcontract.2 (by norm_num)).trans
    (classPrimePowerComponent_totalVariation_le P N hN sigma hs hs1 hsum)

end PrimeFactorOscillations.PrimeClassSampling

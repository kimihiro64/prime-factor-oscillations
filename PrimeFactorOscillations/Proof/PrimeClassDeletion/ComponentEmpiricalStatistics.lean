/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Proof.PrimeClassDeletion.PrimePowerComponentStatistics

/-!
# Exact statistic fibers of a finite empirical law

Fiberwise summation of an arbitrary finite histogram equals the histogram
of the composed observation. This is an exact finite identity.
-/

set_option autoImplicit false
set_option Elab.async false

namespace PrimeFactorOscillations.PrimeClassSampling

private theorem fiber_dirac_hasSum {B : Type*}
    (f : Nat -> B) (m : Nat) (c : Real) (b : B) :
    HasSum (fun a : {a : Nat // f a = b} => if m = a.val then c else 0)
      (@ite Real (f m = b) (Classical.propDecidable _) c 0) := by
  classical
  by_cases hm : f m = b
  case pos =>
    rw [ite_eq_left hm]
    let a0 : {a : Nat // f a = b} := Subtype.mk m hm
    have hz (a : {a : Nat // f a = b})
        (ha : Not (Membership.mem ({a0} : Finset _) a)) :
        (if m = a.val then c else 0) = 0 := by
      apply ite_eq_right
      intro heq
      apply ha
      apply Finset.mem_singleton.mpr
      apply Subtype.ext
      exact heq.symm
    have h : HasSum
        (fun a : {a : Nat // f a = b} => if m = a.val then c else 0)
        (({a0} : Finset _).sum (fun a => if m = a.val then c else 0)) :=
      hasSum_sum_of_ne_finset_zero (s := ({a0} : Finset _)) hz
    rw [Finset.sum_singleton, ite_eq_left (rfl : m = a0.val)] at h
    exact h
  case neg =>
    rw [ite_eq_right hm]
    have hf : (fun a : {a : Nat // f a = b} => if m = a.val then c else 0) =
        (fun _ : {a : Nat // f a = b} => (0 : Real)) := by
      funext a
      apply ite_eq_right
      intro heq
      apply hm
      rw [heq]
      exact a.property
    rw [hf]
    exact hasSum_zero

private theorem finite_empirical_fiber_hasSum {B : Type*}
    (s : Finset Nat) (g : Nat -> Nat) (f : Nat -> B) (c : Real) (b : B) :
    HasSum
      (fun a : {a : Nat // f a = b} => s.sum (fun m => if g m = a.val then c else 0))
      (s.sum (fun m => @ite Real (f (g m) = b) (Classical.propDecidable _) c 0)) := by
  induction s using Finset.induction_on with
  | empty =>
      simpa only [Finset.sum_empty] using
        (hasSum_zero : HasSum (fun _ : {a : Nat // f a = b} => (0 : Real)) 0)
  | @insert m s hm ih =>
      simpa only [Finset.sum_insert hm] using (fiber_dirac_hasSum f (g m) c b).add ih

theorem componentStatisticMass_empirical {B : Type*}
    (s : Finset Nat) (g : Nat -> Nat) (f : Nat -> B) (c : Real) (b : B) :
    componentStatisticMass f (fun a => s.sum (fun m => if g m = a then c else 0)) b =
      s.sum (fun m => @ite Real (f (g m) = b) (Classical.propDecidable _) c 0) :=
  (finite_empirical_fiber_hasSum s g f c b).tsum_eq

theorem componentStatisticMass_id (mass : Nat -> Real) (b : Nat) :
    componentStatisticMass (fun a : Nat => a) mass b = mass b := by
  classical
  let a0 : {a : Nat // a = b} := Subtype.mk b rfl
  have hz (a : {a : Nat // a = b})
      (ha : Not (Membership.mem ({a0} : Finset _) a)) : mass a.val = 0 := by
    exact False.elim (ha (Finset.mem_singleton.mpr (Subtype.ext a.property)))
  have h : HasSum (fun a : {a : Nat // a = b} => mass a.val)
      (({a0} : Finset _).sum (fun a => mass a.val)) :=
    hasSum_sum_of_ne_finset_zero (s := ({a0} : Finset _)) hz
  have heq : ({a0} : Finset _).sum (fun a => mass a.val) = mass b := by
    rw [Finset.sum_singleton]
  exact h.tsum_eq.trans heq

theorem literalPrimePowerComponentProbability_eq_empirical
    (s : Finset Nat) (N a : Nat) :
    literalPrimePowerComponentProbability s N a =
      (Finset.Icc 1 N).sum (fun m =>
        if finitePrimePowerComponent s m = a then 1 / (N : Real) else 0) := by
  classical
  have hc : literalPrimePowerComponentCount s N a =
      (Finset.Icc 1 N).sum (fun m =>
        if finitePrimePowerComponent s m = a then (1 : Nat) else 0) := by
    simp [literalPrimePowerComponentCount]
  unfold literalPrimePowerComponentProbability
  rw [hc, Nat.cast_sum, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro m hm
  split_ifs <;> simp

end PrimeFactorOscillations.PrimeClassSampling

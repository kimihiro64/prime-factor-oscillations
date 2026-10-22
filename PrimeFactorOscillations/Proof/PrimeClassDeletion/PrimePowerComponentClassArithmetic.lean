/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Proof.PrimeClassDeletion.PrimePowerComponentErrorEuler

/-!
# Literal integer sampling for a whole prime class

No sampling limit is used in the cutoff identity. For every fixed sample
size N, all prime cutoffs Y at least N give exactly the same component
counts as the full prime class.
-/

set_option autoImplicit false
set_option Elab.async false

namespace PrimeFactorOscillations.PrimeClassSampling

open Filter

noncomputable def classPrimePowerComponent (P : Set Nat) (m : Nat) : Nat := by
  classical
  exact (m.factorization.filter (fun p => Membership.mem P p)).prod (fun p k => p ^ k)

theorem finitePrimePowerComponent_prefix_eq_class
    (P : Set Nat) (Y m : Nat) (hm : 0 < m) (hmY : m <= Y) :
    finitePrimePowerComponent (primeClassPrefix P Y) m =
      classPrimePowerComponent P m := by
  classical
  have hf : m.factorization.filter (fun p => Membership.mem (primeClassPrefix P Y) p) =
      m.factorization.filter (fun p => Membership.mem P p) := by
    apply Finsupp.ext
    intro p
    rw [Finsupp.filter_apply, Finsupp.filter_apply]
    by_cases hz : m.factorization p = 0
    case pos => simp only [hz, ite_self]
    case neg =>
      have hs : Membership.mem m.factorization.support p := Finsupp.mem_support_iff.mpr hz
      have hpf : Membership.mem m.primeFactors p := by
        rwa [Nat.support_factorization] at hs
      have hd := Nat.mem_primeFactors.mp hpf
      have hbound : p <= Y := (Nat.le_of_dvd hm hd.2.1).trans hmY
      by_cases hp : Membership.mem P p
      case pos =>
        have hprefix : Membership.mem (primeClassPrefix P Y) p :=
          Finset.mem_filter.mpr (And.intro
            (Finset.mem_Icc.mpr (And.intro hd.1.two_le hbound)) (And.intro hd.1 hp))
        simp only [ite_eq_left hp, ite_eq_left hprefix]
      case neg =>
        have hprefix : Not (Membership.mem (primeClassPrefix P Y) p) :=
          fun h => hp (Finset.mem_filter.mp h).2.2
        simp only [ite_eq_right hp, ite_eq_right hprefix]
  unfold finitePrimePowerComponent classPrimePowerComponent
  rw [hf]

noncomputable def classPrimePowerComponentCount (P : Set Nat) (N a : Nat) : Nat := by
  classical
  exact ((Finset.Icc 1 N).filter (fun m => classPrimePowerComponent P m = a)).card

noncomputable def classPrimePowerComponentProbability (P : Set Nat) (N a : Nat) : Real :=
  (classPrimePowerComponentCount P N a : Real) / (N : Real)

theorem classPrimePowerComponentCount_eq_finite_prefix
    (P : Set Nat) (N Y a : Nat) (hNY : N <= Y) :
    classPrimePowerComponentCount P N a =
      literalPrimePowerComponentCount (primeClassPrefix P Y) N a := by
  classical
  unfold classPrimePowerComponentCount literalPrimePowerComponentCount
  apply congrArg Finset.card
  apply Finset.filter_congr
  intro m hm
  have hdata := Finset.mem_Icc.mp hm
  rw [finitePrimePowerComponent_prefix_eq_class P Y m
    (Nat.lt_of_lt_of_le Nat.zero_lt_one hdata.1) (hdata.2.trans hNY)]

theorem classPrimePowerComponentProbability_eq_finite_prefix
    (P : Set Nat) (N Y a : Nat) (hNY : N <= Y) :
    classPrimePowerComponentProbability P N a =
      literalPrimePowerComponentProbability (primeClassPrefix P Y) N a := by
  unfold classPrimePowerComponentProbability literalPrimePowerComponentProbability
  rw [classPrimePowerComponentCount_eq_finite_prefix P N Y a hNY]

theorem classPrimePowerComponentProbability_nonneg (P : Set Nat) (N a : Nat) :
    0 <= classPrimePowerComponentProbability P N a :=
  div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)

theorem classPrimePowerComponentProbability_hasSum_one
    (P : Set Nat) (N : Nat) (hN : 0 < N) :
    HasSum (classPrimePowerComponentProbability P N) 1 := by
  have heq : classPrimePowerComponentProbability P N =
      literalPrimePowerComponentProbability (primeClassPrefix P N) N :=
    funext (fun a => classPrimePowerComponentProbability_eq_finite_prefix P N N a (le_refl N))
  rw [heq]
  exact literalPrimePowerComponentProbability_hasSum_one
    (primeClassPrefix P N) (primeClassPrefix_prime P N) N hN

theorem literalPrimePowerComponentProbability_prefix_tendsto
    (P : Set Nat) (N a : Nat) :
    Tendsto (fun Y : Nat =>
      literalPrimePowerComponentProbability (primeClassPrefix P Y) N a)
      atTop (nhds (classPrimePowerComponentProbability P N a)) := by
  apply tendsto_const_nhds.congr'
  filter_upwards [eventually_ge_atTop N] with Y hNY
  exact classPrimePowerComponentProbability_eq_finite_prefix P N Y a hNY

end PrimeFactorOscillations.PrimeClassSampling

/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import Mathlib.Analysis.Normed.Group.Tannery
import PrimeFactorOscillations.Proof.PrimeClassDeletion.PrimePowerComponentClassSeries

/-!
# The finite-prime cutoff limit of the complete component reference

Dominated convergence applies to the whole supported integer series.
The finite survival products therefore converge to the reciprocal of its
sum, identifying the normalized infinite reference with the Euler limit.
-/

set_option autoImplicit false
set_option Elab.async false

namespace PrimeFactorOscillations.PrimeClassSampling

open Filter

private theorem class_supported_of_prefix
    (P : Set Nat) (Y a : Nat)
    (ha : primePowerSupportedOn (primeClassPrefix P Y) a) :
    classPrimePowerSupported P a := by
  classical
  refine And.intro ha.1 ?_
  intro p hp
  exact (Finset.mem_filter.mp (ha.2 p hp)).2.2

private theorem prefix_supported_eventually
    (P : Set Nat) (a : Nat) (ha : classPrimePowerSupported P a) :
    Filter.Eventually (fun Y : Nat =>
      primePowerSupportedOn (primeClassPrefix P Y) a) atTop := by
  classical
  filter_upwards [eventually_ge_atTop (a.factorization.support.sup id)] with Y hY
  refine And.intro ha.1 ?_
  intro p hp
  have hpf : Membership.mem a.primeFactors p := by
    rwa [Nat.support_factorization] at hp
  have hprime := (Nat.mem_primeFactors.mp hpf).1
  have hbound : p <= a.factorization.support.sup id := Finset.le_sup (f := id) hp
  exact Finset.mem_filter.mpr (And.intro
    (Finset.mem_Icc.mpr (And.intro hprime.two_le (hbound.trans hY)))
    (And.intro hprime (ha.2 p hp)))

theorem supportedPrimePowerWeight_prefix_le
    (P : Set Nat) (sigma : Real) (Y a : Nat) :
    supportedPrimePowerWeight (primeClassPrefix P Y) sigma a <=
      classPrimePowerWeight P sigma a := by
  classical
  by_cases ha : primePowerSupportedOn (primeClassPrefix P Y) a
  case pos =>
    have hc := class_supported_of_prefix P Y a ha
    simp only [supportedPrimePowerWeight, classPrimePowerWeight,
      ite_eq_left ha, ite_eq_left hc, le_refl]
  case neg =>
    rw [supportedPrimePowerWeight, ite_eq_right ha]
    exact classPrimePowerWeight_nonneg P sigma a

theorem supportedPrimePowerWeight_prefix_eventually_eq
    (P : Set Nat) (sigma : Real) (a : Nat) :
    Filter.Eventually (fun Y : Nat =>
      supportedPrimePowerWeight (primeClassPrefix P Y) sigma a =
        classPrimePowerWeight P sigma a) atTop := by
  classical
  by_cases ha : classPrimePowerSupported P a
  case pos =>
    filter_upwards [prefix_supported_eventually P a ha] with Y hY
    simp only [supportedPrimePowerWeight, classPrimePowerWeight,
      ite_eq_left hY, ite_eq_left ha]
  case neg =>
    apply Filter.Eventually.of_forall
    intro Y
    have hn : Not (primePowerSupportedOn (primeClassPrefix P Y) a) :=
      fun h => ha (class_supported_of_prefix P Y a h)
    simp only [supportedPrimePowerWeight, classPrimePowerWeight,
      ite_eq_right hn, ite_eq_right ha]

theorem supportedPrimePowerWeight_prefix_tendsto
    (P : Set Nat) (sigma : Real) (a : Nat) :
    Tendsto (fun Y : Nat =>
      supportedPrimePowerWeight (primeClassPrefix P Y) sigma a)
      atTop (nhds (classPrimePowerWeight P sigma a)) :=
  tendsto_const_nhds.congr'
    ((supportedPrimePowerWeight_prefix_eventually_eq P sigma a).mono
      (fun _Y h => h.symm))

theorem supportedPrimePowerWeight_prefix_tsum_tendsto
    (P : Set Nat) (sigma : Real) (hs : 0 < sigma)
    (hsum : Summable (classPowerWeight P sigma)) :
    Tendsto (fun Y : Nat => tsum
      (supportedPrimePowerWeight (primeClassPrefix P Y) sigma))
      atTop (nhds (tsum (classPrimePowerWeight P sigma))) := by
  refine tendsto_tsum_of_dominated_convergence
    (bound := classPrimePowerWeight P sigma)
    (classPrimePowerWeight_summable P sigma hs hsum) ?_ ?_
  . intro a
    exact supportedPrimePowerWeight_prefix_tendsto P sigma a
  . apply Filter.Eventually.of_forall
    intro Y a
    have hn : 0 <= supportedPrimePowerWeight (primeClassPrefix P Y) sigma a := by
      unfold supportedPrimePowerWeight
      split_ifs
      case pos => exact Real.rpow_nonneg (Nat.cast_nonneg _) _
      case neg => exact le_refl 0
    simpa only [Real.norm_eq_abs, abs_of_nonneg hn] using
      supportedPrimePowerWeight_prefix_le P sigma Y a

private theorem finite_reference_eq_survival_weight (s : Finset Nat) (a : Nat) :
    finitePrimePowerReference s a =
      finitePrimeComponentSurvival s * supportedPrimePowerWeight s 1 a := by
  classical
  by_cases ha : primePowerSupportedOn s a <;>
    simp [finitePrimePowerReference, supportedPrimePowerWeight,
      ha, Real.rpow_neg_one, div_eq_mul_inv]

theorem finitePrimeComponentSurvival_eq_reciprocal
    (s : Finset Nat)
    (hprime : forall p : Nat, Membership.mem s p -> Nat.Prime p) :
    finitePrimeComponentSurvival s =
      1 / tsum (supportedPrimePowerWeight s 1) := by
  have hs := supportedPrimePowerWeight_summable s hprime 1 zero_lt_one
  have h := hs.hasSum.mul_left (finitePrimeComponentSurvival s)
  have heq : (fun a => finitePrimeComponentSurvival s * supportedPrimePowerWeight s 1 a) =
      finitePrimePowerReference s :=
    funext (fun a => (finite_reference_eq_survival_weight s a).symm)
  rw [heq] at h
  have hmass : finitePrimeComponentSurvival s *
      tsum (supportedPrimePowerWeight s 1) = 1 :=
    h.unique (finitePrimePowerReference_hasSum_one s hprime)
  have hn : Not (tsum (supportedPrimePowerWeight s 1) = 0) := by
    intro hz
    rw [hz, mul_zero] at hmass
    norm_num at hmass
  exact (eq_div_iff hn).mpr hmass

theorem finitePrimeComponentSurvival_prefix_tendsto
    (P : Set Nat) (hsum : Summable (classPowerWeight P 1)) :
    Tendsto (fun Y : Nat => finitePrimeComponentSurvival (primeClassPrefix P Y))
      atTop (nhds (1 / tsum (classPrimePowerWeight P 1))) := by
  have hf : (fun Y : Nat => finitePrimeComponentSurvival (primeClassPrefix P Y)) =
      (fun Y : Nat => 1 / tsum (supportedPrimePowerWeight (primeClassPrefix P Y) 1)) :=
    funext (fun Y => finitePrimeComponentSurvival_eq_reciprocal
      (primeClassPrefix P Y) (primeClassPrefix_prime P Y))
  rw [hf]
  exact tendsto_const_nhds.div
    (supportedPrimePowerWeight_prefix_tsum_tendsto P 1 zero_lt_one hsum)
    (ne_of_gt (classPrimePowerWeight_tsum_pos P 1 zero_lt_one hsum))

theorem finitePrimePowerReference_prefix_tendsto
    (P : Set Nat) (hsum : Summable (classPowerWeight P 1)) (a : Nat) :
    Tendsto (fun Y : Nat => finitePrimePowerReference (primeClassPrefix P Y) a)
      atTop (nhds (classPrimePowerReference P a)) := by
  have hf : (fun Y : Nat => finitePrimePowerReference (primeClassPrefix P Y) a) =
      (fun Y : Nat => finitePrimeComponentSurvival (primeClassPrefix P Y) *
        supportedPrimePowerWeight (primeClassPrefix P Y) 1 a) :=
    funext (fun Y => finite_reference_eq_survival_weight (primeClassPrefix P Y) a)
  rw [hf]
  simpa only [classPrimePowerReference, div_eq_mul_inv, mul_comm, one_mul] using
    (finitePrimeComponentSurvival_prefix_tendsto P hsum).mul
      (supportedPrimePowerWeight_prefix_tendsto P 1 a)

end PrimeFactorOscillations.PrimeClassSampling

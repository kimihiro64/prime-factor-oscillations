/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Proof.PrimeClassDeletion.PrimePowerComponentDistance

/-!
# Exact finite-prime truncation distance

The full reference law is compared with the actual finite-prime reference,
including empty supports, the prime two and every finite cutoff.
Only reciprocal summability is needed for convergence in total variation.
-/

set_option autoImplicit false
set_option Elab.async false

namespace PrimeFactorOscillations.PrimeClassSampling

open Filter

theorem classPowerWeight_finset_summable (s : Finset Nat) :
    Summable (classPowerWeight (s : Set Nat) 1) := by
  classical
  have h : HasSum (classPowerWeight (s : Set Nat) 1)
      (s.sum (classPowerWeight (s : Set Nat) 1)) :=
    hasSum_sum_of_ne_finset_zero (s := s) (by
      intro p hp
      simp [classPowerWeight, hp])
  exact h.summable

theorem classPrimePowerWeight_finset (s : Finset Nat) (sigma : Real) :
    classPrimePowerWeight (s : Set Nat) sigma = supportedPrimePowerWeight s sigma := by
  rfl

theorem classPrimePowerNormalizer_finset
    (s : Finset Nat)
    (hprime : forall p : Nat, Membership.mem s p -> Nat.Prime p) :
    classPrimePowerNormalizer (s : Set Nat) = 1 / finitePrimeComponentSurvival s := by
  unfold classPrimePowerNormalizer
  rw [classPrimePowerWeight_finset,
    finitePrimeComponentSurvival_eq_reciprocal s hprime, one_div_one_div]

theorem classPrimePowerReference_finset
    (s : Finset Nat)
    (hprime : forall p : Nat, Membership.mem s p -> Nat.Prime p) (a : Nat) :
    classPrimePowerReference (s : Set Nat) a = finitePrimePowerReference s a := by
  classical
  unfold classPrimePowerReference
  rw [classPrimePowerWeight_finset]
  unfold finitePrimePowerReference
  by_cases ha : primePowerSupportedOn s a
  case pos =>
    rw [ite_eq_left ha]
    have hw : supportedPrimePowerWeight s 1 a = (a : Real) ^ (-(1 : Real)) := by
      simp only [supportedPrimePowerWeight, ite_eq_left ha]
    rw [hw, Real.rpow_neg_one, finitePrimeComponentSurvival_eq_reciprocal s hprime]
    simp only [div_eq_mul_inv, one_mul]
    exact mul_comm _ _
  case neg =>
    rw [ite_eq_right ha]
    have hz : supportedPrimePowerWeight s 1 a = 0 := by
      simp only [supportedPrimePowerWeight, ite_eq_right ha]
    rw [hz, zero_div]

theorem classPrimePowerReference_finite_totalVariation_eq
    (P : Set Nat) (hsum : Summable (classPowerWeight P 1))
    (s : Finset Nat)
    (hprime : forall p : Nat, Membership.mem s p -> Nat.Prime p)
    (hP : forall p : Nat, Membership.mem s p -> Membership.mem P p) :
    tsum (fun a => abs (classPrimePowerReference P a - finitePrimePowerReference s a)) / 2 =
      1 - (1 / classPrimePowerNormalizer P) / finitePrimeComponentSurvival s := by
  have h := classPrimePowerReference_subset_totalVariation_eq (s : Set Nat) P hP
    (classPowerWeight_finset_summable s) hsum
  have hf : (fun a => abs
      (classPrimePowerReference (s : Set Nat) a - classPrimePowerReference P a)) =
      (fun a => abs (classPrimePowerReference P a - finitePrimePowerReference s a)) := by
    funext a
    rw [classPrimePowerReference_finset s hprime a, abs_sub_comm]
  rw [hf, classPrimePowerNormalizer_finset s hprime] at h
  calc
    _ = 1 - (1 / finitePrimeComponentSurvival s) / classPrimePowerNormalizer P := h
    _ = _ := by ring

theorem classPrimePowerReference_prefix_totalVariation_eq
    (P : Set Nat) (hsum : Summable (classPowerWeight P 1)) (Y : Nat) :
    tsum (fun a => abs (classPrimePowerReference P a -
      finitePrimePowerReference (primeClassPrefix P Y) a)) / 2 =
      1 - (1 / classPrimePowerNormalizer P) /
        finitePrimeComponentSurvival (primeClassPrefix P Y) := by
  classical
  exact classPrimePowerReference_finite_totalVariation_eq P hsum (primeClassPrefix P Y)
    (primeClassPrefix_prime P Y) (fun p hp => (Finset.mem_filter.mp hp).2.2)

theorem classPrimePowerReference_prefix_totalVariation_tendsto_zero
    (P : Set Nat) (hsum : Summable (classPowerWeight P 1)) :
    Tendsto (fun Y : Nat => tsum (fun a => abs (classPrimePowerReference P a -
      finitePrimePowerReference (primeClassPrefix P Y) a)) / 2) atTop (nhds 0) := by
  have hZ : 0 < classPrimePowerNormalizer P :=
    classPrimePowerWeight_tsum_pos P 1 zero_lt_one hsum
  have hn : Not (1 / classPrimePowerNormalizer P = 0) := ne_of_gt (one_div_pos.mpr hZ)
  have hc : Tendsto
      (fun Y : Nat => finitePrimeComponentSurvival (primeClassPrefix P Y))
      atTop (nhds (1 / classPrimePowerNormalizer P)) :=
    finitePrimeComponentSurvival_prefix_tendsto P hsum
  have hd : Tendsto
      (fun Y : Nat => (1 / classPrimePowerNormalizer P) /
        finitePrimeComponentSurvival (primeClassPrefix P Y))
      atTop (nhds ((1 / classPrimePowerNormalizer P) / (1 / classPrimePowerNormalizer P))) :=
    tendsto_const_nhds.div hc hn
  have h : Tendsto
      (fun Y : Nat => 1 - (1 / classPrimePowerNormalizer P) /
        finitePrimeComponentSurvival (primeClassPrefix P Y)) atTop (nhds 0) := by
    simpa only [div_self hn, sub_self] using
      ((tendsto_const_nhds : Tendsto (fun _ : Nat => (1 : Real)) atTop (nhds 1)).sub hd)
  apply h.congr'
  exact Filter.Eventually.of_forall
    (fun Y => (classPrimePowerReference_prefix_totalVariation_eq P hsum Y).symm)

end PrimeFactorOscillations.PrimeClassSampling

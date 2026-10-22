/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Proof.PrimeClassDeletion.PrimeComponentCarrierEuler
import PrimeFactorOscillations.Proof.PrimeClassDeletion.PrimePowerComponentErrorEuler

/-!
# Exact absolute norm of the prime-component inverse

The full infinite Mobius inverse has norm equal to the complete sampling
Euler budget. This identifies the constant exactly, without discarding the
geometric denominators or replacing it by a larger exponential estimate.
-/

set_option autoImplicit false
set_option Elab.async false

namespace PrimeFactorOscillations.PrimeClassSampling

open Filter

private theorem succ_tendsto : Tendsto (fun Y : Nat => Y + 1) atTop atTop := by
  apply tendsto_atTop.mpr
  intro b
  filter_upwards [eventually_ge_atTop b] with Y hY
  exact hY.trans (Nat.le_succ Y)

theorem classPrimeComponentWeightEulerPrefix_tendsto
    (P : Set Nat) (sigma : Real) (hs : 0 < sigma)
    (hsum : Summable (classPowerWeight P sigma)) :
    Tendsto (fun Y : Nat => (Y + 1).primesBelow.prod
      (fun p => 1 / (1 - classPrimePowerWeight P sigma p)))
      atTop (nhds (classPrimePowerPartition P sigma)) := by
  have hnorm : Summable (fun n : Nat =>
      norm (classPrimeComponentWeightArithmetic P sigma n)) := by
    apply (classPrimePowerWeight_summable P sigma hs hsum).congr
    intro n
    rw [classPrimeComponentWeightArithmetic_apply, Real.norm_eq_abs,
      abs_of_nonneg (classPrimePowerWeight_nonneg P sigma n)]
  have heuler := (classPrimeComponentWeightArithmetic_isMultiplicative P sigma).eulerProduct hnorm
  simp only [classPrimeComponentWeightArithmetic_apply] at heuler
  apply (heuler.comp succ_tendsto).congr'
  apply Filter.Eventually.of_forall
  intro Y
  apply Finset.prod_congr rfl
  intro p hp
  exact classPrimePowerWeight_primePower_tsum P sigma hs p (Nat.mem_primesBelow.mp hp).2

theorem classPrimeComponentAbsMobiusEulerPrefix_tendsto
    (P : Set Nat) (sigma : Real) (hs : 0 < sigma)
    (hsum : Summable (classPowerWeight P sigma)) :
    Tendsto (fun Y : Nat => (Y + 1).primesBelow.prod
      (fun p => 1 + classPrimePowerWeight P sigma p))
      atTop (nhds (tsum (classPrimeComponentAbsMobiusArithmetic P sigma))) := by
  have hnorm : Summable (fun n : Nat =>
      norm (classPrimeComponentAbsMobiusArithmetic P sigma n)) := by
    apply (classPrimeComponentAbsMobiusArithmetic_summable P sigma hs hsum).congr
    intro n
    rw [Real.norm_eq_abs,
      abs_of_nonneg (classPrimeComponentAbsMobiusArithmetic_nonneg P sigma n)]
  have heuler :=
    (classPrimeComponentAbsMobiusArithmetic_isMultiplicative P sigma).eulerProduct hnorm
  apply (heuler.comp succ_tendsto).congr'
  apply Filter.Eventually.of_forall
  intro Y
  apply Finset.prod_congr rfl
  intro p hp
  exact classPrimeComponentAbsMobiusArithmetic_primePower_tsum P sigma p
    (Nat.mem_primesBelow.mp hp).2

theorem classPrimeComponentEulerRatioPrefix
    (P : Set Nat) (sigma : Real) (Y : Nat) :
    ((Y + 1).primesBelow.prod (fun p => 1 / (1 - classPrimePowerWeight P sigma p))) *
      ((Y + 1).primesBelow.prod (fun p => 1 + classPrimePowerWeight P sigma p)) =
        (primeClassPrefix P Y).prod (fun p =>
          (1 + (p : Real) ^ (-sigma)) / (1 - (p : Real) ^ (-sigma))) := by
  classical
  rw [<- Finset.prod_mul_distrib]
  have hlocal : (Y + 1).primesBelow.prod
      (fun p => (1 / (1 - classPrimePowerWeight P sigma p)) *
        (1 + classPrimePowerWeight P sigma p)) =
      (Y + 1).primesBelow.prod (fun p => if Membership.mem P p then
        (1 + (p : Real) ^ (-sigma)) / (1 - (p : Real) ^ (-sigma)) else 1) := by
    apply Finset.prod_congr rfl
    intro p hp
    have hprime := (Nat.mem_primesBelow.mp hp).2
    rw [classPrimePowerWeight_prime P sigma p hprime]
    by_cases hP : Membership.mem P p
    . simp only [classPowerWeight, ite_eq_left (And.intro hprime hP), ite_eq_left hP]
      ring
    . have hn : Not (And (Nat.Prime p) (Membership.mem P p)) := fun h => hP h.2
      simp only [classPowerWeight, ite_eq_right hn, ite_eq_right hP]
      norm_num
  rw [hlocal, <- Finset.prod_filter]
  have hsets : (Y + 1).primesBelow.filter (fun p => Membership.mem P p) =
      primeClassPrefix P Y := by
    ext p
    constructor
    . intro hp
      have h := Finset.mem_filter.mp hp
      have hprime := Nat.mem_primesBelow.mp h.1
      exact Finset.mem_filter.mpr (And.intro
        (Finset.mem_Icc.mpr (And.intro hprime.2.two_le (Nat.le_of_lt_succ hprime.1)))
        (And.intro hprime.2 h.2))
    . intro hp
      have h := Finset.mem_filter.mp hp
      have hb := Finset.mem_Icc.mp h.1
      exact Finset.mem_filter.mpr (And.intro
        (Nat.mem_primesBelow.mpr (And.intro (Nat.lt_succ_of_le hb.2) h.2.1)) h.2.2)
  rw [hsets]

theorem classPrimeComponentInverseArithmetic_norm
    (P : Set Nat) (sigma : Real) (hs : 0 < sigma)
    (hsum : Summable (classPowerWeight P sigma)) (n : Nat) :
    norm (classPrimeComponentInverseArithmetic P sigma n) =
      classPrimePowerPartition P sigma * classPrimeComponentAbsMobiusArithmetic P sigma n := by
  have hZ : 0 <= classPrimePowerPartition P sigma :=
    (classPrimePowerWeight_tsum_pos P sigma hs hsum).le
  rw [Real.norm_eq_abs, classPrimeComponentInverseArithmetic_apply,
    abs_mul, abs_mul, abs_of_nonneg hZ,
    abs_of_nonneg (classPrimePowerWeight_nonneg P sigma n),
    classPrimeComponentAbsMobiusArithmetic_apply]
  ring

theorem classPrimeComponentInverseArithmetic_norm_summable
    (P : Set Nat) (sigma : Real) (hs : 0 < sigma)
    (hsum : Summable (classPowerWeight P sigma)) :
    Summable (fun n : Nat => norm (classPrimeComponentInverseArithmetic P sigma n)) := by
  apply ((classPrimeComponentAbsMobiusArithmetic_summable P sigma hs hsum).mul_left
    (classPrimePowerPartition P sigma)).congr
  intro n
  exact (classPrimeComponentInverseArithmetic_norm P sigma hs hsum n).symm

theorem classPrimeComponentInverseArithmetic_tsum_norm
    (P : Set Nat) (sigma : Real) (hs : 0 < sigma)
    (hsum : Summable (classPowerWeight P sigma)) :
    tsum (fun n : Nat => norm (classPrimeComponentInverseArithmetic P sigma n)) =
      classPrimePowerErrorConstant P sigma := by
  have hlim := (classPrimeComponentWeightEulerPrefix_tendsto P sigma hs hsum).mul
    (classPrimeComponentAbsMobiusEulerPrefix_tendsto P sigma hs hsum)
  have heq : (fun Y : Nat =>
      ((Y + 1).primesBelow.prod (fun p => 1 / (1 - classPrimePowerWeight P sigma p))) *
      ((Y + 1).primesBelow.prod (fun p => 1 + classPrimePowerWeight P sigma p))) =
      (fun Y : Nat => (primeClassPrefix P Y).prod (fun p =>
        (1 + (p : Real) ^ (-sigma)) / (1 - (p : Real) ^ (-sigma)))) :=
    funext (classPrimeComponentEulerRatioPrefix P sigma)
  rw [heq] at hlim
  have hmass := tendsto_nhds_unique hlim (primePowerErrorEulerPrefix_tendsto P sigma hs hsum)
  simp_rw [classPrimeComponentInverseArithmetic_norm P sigma hs hsum]
  rw [tsum_mul_left]
  exact hmass

theorem classPrimeComponentCarrier_inverse_norm_certificate
    (P : Set Nat) (sigma : Real) (hs : 0 < sigma)
    (hsum : Summable (classPowerWeight P sigma)) :
    And (forall n : Nat, 0 <= classPrimeComponentNoiseArithmetic P sigma n)
      (And (HasSum (classPrimeComponentNoiseArithmetic P sigma) 1)
        (And (classPrimeComponentInverseArithmetic P sigma *
          classPrimeComponentNoiseArithmetic P sigma = 1)
          (And (Summable (fun n : Nat =>
            norm (classPrimeComponentInverseArithmetic P sigma n)))
            (tsum (fun n : Nat => norm (classPrimeComponentInverseArithmetic P sigma n)) =
              classPrimePowerErrorConstant P sigma)))) := by
  refine And.intro ?_ (And.intro
    (classPrimeComponentNoise_hasSum_one P sigma hs hsum)
    (And.intro (classPrimeComponentInverse_mul_noise P sigma hs hsum)
      (And.intro (classPrimeComponentInverseArithmetic_norm_summable P sigma hs hsum)
        (classPrimeComponentInverseArithmetic_tsum_norm P sigma hs hsum))))
  intro n
  rw [classPrimeComponentNoiseArithmetic_apply]
  exact div_nonneg (classPrimePowerWeight_nonneg P sigma n)
    (classPrimePowerWeight_tsum_pos P sigma hs hsum).le

end PrimeFactorOscillations.PrimeClassSampling

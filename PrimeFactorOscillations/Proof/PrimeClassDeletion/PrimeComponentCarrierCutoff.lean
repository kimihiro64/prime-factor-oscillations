/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Proof.PrimeClassDeletion.PrimeComponentCarrierDistance
import PrimeFactorOscillations.Proof.PrimeClassDeletion.PrimeComponentCarrierSharpness
import PrimeFactorOscillations.Proof.PrimeClassDeletion.PrimePowerComponentCutoffDistance

/-!
# Exact finite-prime reconstruction error

The full inverse is approximated in absolute coefficient norm by its actual
prime-prefix inverses. The error is exactly the missing Euler budget, and
this is the best uniform convolution-operator constant.
-/

set_option autoImplicit false
set_option Elab.async false

namespace PrimeFactorOscillations.PrimeClassSampling

open Filter

theorem classPrimeComponentPrefix_powerWeight_summable
    (P : Set Nat) (sigma : Real)
    (hP : Summable (classPowerWeight P sigma)) (Y : Nat) :
    Summable (classPowerWeight (primeClassPrefix P Y : Set Nat) sigma) := by
  classical
  exact classPowerWeight_summable_subset (primeClassPrefix P Y : Set Nat) P
    (fun p hp => (Finset.mem_filter.mp hp).2.2) sigma hP

theorem classPrimeComponentPrefix_partition_tendsto
    (P : Set Nat) (sigma : Real) (hs : 0 < sigma)
    (hP : Summable (classPowerWeight P sigma)) :
    Tendsto (fun Y : Nat => classPrimePowerPartition
      (primeClassPrefix P Y : Set Nat) sigma) atTop
        (nhds (classPrimePowerPartition P sigma)) := by
  simpa only [classPrimePowerPartition, classPrimePowerWeight_finset] using
    supportedPrimePowerWeight_prefix_tsum_tendsto P sigma hs hP

theorem classPrimeComponentPrefix_absMobius_tsum_tendsto
    (P : Set Nat) (sigma : Real) (hs : 0 < sigma)
    (hP : Summable (classPowerWeight P sigma)) :
    Tendsto (fun Y : Nat => tsum (classPrimeComponentAbsMobiusArithmetic
      (primeClassPrefix P Y : Set Nat) sigma)) atTop
        (nhds (tsum (classPrimeComponentAbsMobiusArithmetic P sigma))) := by
  refine tendsto_tsum_of_dominated_convergence
    (bound := classPrimeComponentAbsMobiusArithmetic P sigma)
    (classPrimeComponentAbsMobiusArithmetic_summable P sigma hs hP) ?_ ?_
  . intro n
    have hw : Tendsto (fun Y : Nat => classPrimePowerWeight
        (primeClassPrefix P Y : Set Nat) sigma n) atTop
          (nhds (classPrimePowerWeight P sigma n)) := by
      simpa only [classPrimePowerWeight_finset] using
        supportedPrimePowerWeight_prefix_tendsto P sigma n
    simpa only [classPrimeComponentAbsMobiusArithmetic_apply] using
      (tendsto_const_nhds.mul hw :
        Tendsto (fun Y : Nat => abs (ArithmeticFunction.moebius n : Real) *
          classPrimePowerWeight (primeClassPrefix P Y : Set Nat) sigma n)
          atTop (nhds (abs (ArithmeticFunction.moebius n : Real) *
            classPrimePowerWeight P sigma n)))
  . apply Filter.Eventually.of_forall
    intro Y n
    rw [Real.norm_eq_abs,
      abs_of_nonneg (classPrimeComponentAbsMobiusArithmetic_nonneg
        (primeClassPrefix P Y : Set Nat) sigma n),
      classPrimeComponentAbsMobiusArithmetic_apply,
      classPrimeComponentAbsMobiusArithmetic_apply,
      classPrimePowerWeight_finset]
    exact mul_le_mul_of_nonneg_left (supportedPrimePowerWeight_prefix_le P sigma Y n)
      (abs_nonneg _)

theorem classPrimePowerErrorConstant_eq_partition_mul_absMobius
    (P : Set Nat) (sigma : Real) (hs : 0 < sigma)
    (hP : Summable (classPowerWeight P sigma)) :
    classPrimePowerErrorConstant P sigma = classPrimePowerPartition P sigma *
      tsum (classPrimeComponentAbsMobiusArithmetic P sigma) := by
  have h := classPrimeComponentInverseArithmetic_tsum_norm P sigma hs hP
  simp_rw [classPrimeComponentInverseArithmetic_norm P sigma hs hP] at h
  rw [tsum_mul_left] at h
  exact h.symm

theorem classPrimeComponentPrefix_budget_tendsto
    (P : Set Nat) (sigma : Real) (hs : 0 < sigma)
    (hP : Summable (classPowerWeight P sigma)) :
    Tendsto (fun Y : Nat => classPrimePowerErrorConstant
      (primeClassPrefix P Y : Set Nat) sigma) atTop
        (nhds (classPrimePowerErrorConstant P sigma)) := by
  have h := (classPrimeComponentPrefix_partition_tendsto P sigma hs hP).mul
    (classPrimeComponentPrefix_absMobius_tsum_tendsto P sigma hs hP)
  rw [<- classPrimePowerErrorConstant_eq_partition_mul_absMobius P sigma hs hP] at h
  apply h.congr'
  exact Filter.Eventually.of_forall (fun Y =>
    (classPrimePowerErrorConstant_eq_partition_mul_absMobius
      (primeClassPrefix P Y : Set Nat) sigma hs
      (classPrimeComponentPrefix_powerWeight_summable P sigma hP Y)).symm)

theorem classPrimeComponentInverse_prefix_l1_error
    (P : Set Nat) (sigma : Real) (hs : 0 < sigma)
    (hP : Summable (classPowerWeight P sigma)) (Y : Nat) :
    tsum (fun n : Nat => norm (classPrimeComponentInverseArithmetic P sigma n -
      classPrimeComponentInverseArithmetic (primeClassPrefix P Y : Set Nat) sigma n)) =
        classPrimePowerErrorConstant P sigma -
          classPrimePowerErrorConstant (primeClassPrefix P Y : Set Nat) sigma := by
  classical
  have h := classPrimeComponentInverse_l1_distance_of_subset
    (primeClassPrefix P Y : Set Nat) P
    (fun p hp => (Finset.mem_filter.mp hp).2.2) sigma hs
    (classPrimeComponentPrefix_powerWeight_summable P sigma hP Y) hP
  have heq : (fun n : Nat => norm (classPrimeComponentInverseArithmetic P sigma n -
      classPrimeComponentInverseArithmetic (primeClassPrefix P Y : Set Nat) sigma n)) =
      (fun n : Nat => norm
        (classPrimeComponentInverseArithmetic (primeClassPrefix P Y : Set Nat) sigma n -
          classPrimeComponentInverseArithmetic P sigma n)) := by
    funext n
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_sub_comm]
  rw [heq]
  exact h

theorem classPrimeComponentInverse_prefix_l1_tendsto_zero
    (P : Set Nat) (sigma : Real) (hs : 0 < sigma)
    (hP : Summable (classPowerWeight P sigma)) :
    Tendsto (fun Y : Nat => tsum (fun n : Nat => norm
      (classPrimeComponentInverseArithmetic P sigma n -
        classPrimeComponentInverseArithmetic (primeClassPrefix P Y : Set Nat) sigma n)))
      atTop (nhds 0) := by
  have h : Tendsto (fun Y : Nat => classPrimePowerErrorConstant P sigma -
      classPrimePowerErrorConstant (primeClassPrefix P Y : Set Nat) sigma)
      atTop (nhds 0) := by
    simpa only [sub_self] using
      ((tendsto_const_nhds : Tendsto
        (fun _ : Nat => classPrimePowerErrorConstant P sigma) atTop
          (nhds (classPrimePowerErrorConstant P sigma))).sub
        (classPrimeComponentPrefix_budget_tendsto P sigma hs hP))
  apply h.congr'
  exact Filter.Eventually.of_forall (fun Y =>
    (classPrimeComponentInverse_prefix_l1_error P sigma hs hP Y).symm)

theorem classPrimeComponentInverse_prefix_convolution_error
    (P : Set Nat) (sigma : Real) (hs : 0 < sigma)
    (hP : Summable (classPowerWeight P sigma)) (Y : Nat)
    (f : ArithmeticFunction Real) (hf : Summable (fun n : Nat => norm (f n))) :
    tsum (fun n : Nat => norm
      (((classPrimeComponentInverseArithmetic P sigma -
        classPrimeComponentInverseArithmetic (primeClassPrefix P Y : Set Nat) sigma) * f) n)) <=
        (classPrimePowerErrorConstant P sigma -
          classPrimePowerErrorConstant (primeClassPrefix P Y : Set Nat) sigma) *
            tsum (fun n : Nat => norm (f n)) := by
  have hPrefix := classPrimeComponentPrefix_powerWeight_summable P sigma hP Y
  have hdiff : Summable (fun n : Nat => norm
      ((classPrimeComponentInverseArithmetic P sigma -
        classPrimeComponentInverseArithmetic (primeClassPrefix P Y : Set Nat) sigma) n)) := by
    exact (classPrimeComponentInverse_distance_hasSum P
      (primeClassPrefix P Y : Set Nat) sigma hs hP hPrefix).summable
  have h := ArithmeticFunctionL1.tsum_norm_convolution_le
    (classPrimeComponentInverseArithmetic P sigma -
      classPrimeComponentInverseArithmetic (primeClassPrefix P Y : Set Nat) sigma) f hdiff hf
  have heq : tsum (fun n : Nat => norm
      ((classPrimeComponentInverseArithmetic P sigma -
        classPrimeComponentInverseArithmetic (primeClassPrefix P Y : Set Nat) sigma) n)) =
      classPrimePowerErrorConstant P sigma -
        classPrimePowerErrorConstant (primeClassPrefix P Y : Set Nat) sigma :=
    classPrimeComponentInverse_prefix_l1_error P sigma hs hP Y
  rw [heq] at h
  exact h

theorem classPrimeComponentInverse_prefix_convolution_constant_optimal
    (P : Set Nat) (sigma : Real) (hs : 0 < sigma)
    (hP : Summable (classPowerWeight P sigma)) (Y : Nat) (C : Real)
    (hC : forall f : ArithmeticFunction Real,
      Summable (fun n : Nat => norm (f n)) ->
        tsum (fun n : Nat => norm
          (((classPrimeComponentInverseArithmetic P sigma -
            classPrimeComponentInverseArithmetic (primeClassPrefix P Y : Set Nat) sigma) * f) n)) <=
              C * tsum (fun n : Nat => norm (f n))) :
    classPrimePowerErrorConstant P sigma -
      classPrimePowerErrorConstant (primeClassPrefix P Y : Set Nat) sigma <= C := by
  have hunit : HasSum (fun n : Nat => norm ((1 : ArithmeticFunction Real) n)) 1 := by
    have heq : (fun n : Nat => norm ((1 : ArithmeticFunction Real) n)) =
        (fun n : Nat => if n = 1 then (1 : Real) else 0) := by
      funext n
      by_cases hn : n = 1 <;> simp [hn]
    rw [heq]
    exact hasSum_ite_eq 1 1
  have h := hC 1 hunit.summable
  simp only [mul_one, hunit.tsum_eq] at h
  rw [<- classPrimeComponentInverse_prefix_l1_error P sigma hs hP Y]
  exact h

end PrimeFactorOscillations.PrimeClassSampling

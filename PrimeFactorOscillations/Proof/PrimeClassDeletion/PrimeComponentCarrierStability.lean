/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.ArithmeticFunctionDirichletL1
import PrimeFactorOscillations.Proof.PrimeClassDeletion.PrimeComponentCarrierNorm

/-!
# Stable inversion of multiplicative prime-component noise

The exact infinite inverse norm controls every summable signed input.
Probability differences obey the same inverse bound and the forward
contraction bound. Optimality on zero-mass differences is a separate claim.
-/

set_option autoImplicit false
set_option Elab.async false

namespace PrimeFactorOscillations.PrimeClassSampling

open PrimeFactorOscillations.ArithmeticFunctionL1

theorem classPrimeComponentNoise_norm_hasSum_one
    (P : Set Nat) (sigma : Real) (hs : 0 < sigma)
    (hsum : Summable (classPowerWeight P sigma)) :
    HasSum (fun n : Nat => norm (classPrimeComponentNoiseArithmetic P sigma n)) 1 := by
  have hc := classPrimeComponentCarrier_inverse_norm_certificate P sigma hs hsum
  have heq : (fun n : Nat => norm (classPrimeComponentNoiseArithmetic P sigma n)) =
      (fun n : Nat => classPrimeComponentNoiseArithmetic P sigma n) := by
    funext n
    rw [Real.norm_eq_abs, abs_of_nonneg (hc.1 n)]
  rw [heq]
  exact hc.2.1

theorem classPrimeComponentCarrier_l1_contraction
    (P : Set Nat) (sigma : Real) (hs : 0 < sigma)
    (hsum : Summable (classPowerWeight P sigma)) (f : ArithmeticFunction Real)
    (hf : Summable (fun n : Nat => norm (f n))) :
    tsum (fun n : Nat => norm ((classPrimeComponentNoiseArithmetic P sigma * f) n)) <=
      tsum (fun n : Nat => norm (f n)) := by
  have heta := classPrimeComponentNoise_norm_hasSum_one P sigma hs hsum
  have h := tsum_norm_convolution_le (classPrimeComponentNoiseArithmetic P sigma) f
    heta.summable hf
  rw [heta.tsum_eq, one_mul] at h
  exact h

theorem classPrimeComponentCarrier_l1_recovery
    (P : Set Nat) (sigma : Real) (hs : 0 < sigma)
    (hsum : Summable (classPowerWeight P sigma)) (f : ArithmeticFunction Real)
    (hf : Summable (fun n : Nat => norm (f n))) :
    tsum (fun n : Nat => norm (f n)) <= classPrimePowerErrorConstant P sigma *
      tsum (fun n : Nat => norm ((classPrimeComponentNoiseArithmetic P sigma * f) n)) := by
  have heta := classPrimeComponentNoise_norm_hasSum_one P sigma hs hsum
  have hout := norm_convolution_summable
    (classPrimeComponentNoiseArithmetic P sigma) f heta.summable hf
  have h := tsum_norm_convolution_le (classPrimeComponentInverseArithmetic P sigma)
    (classPrimeComponentNoiseArithmetic P sigma * f)
    (classPrimeComponentInverseArithmetic_norm_summable P sigma hs hsum) hout
  rw [<- mul_assoc, classPrimeComponentInverse_mul_noise P sigma hs hsum, one_mul,
    classPrimeComponentInverseArithmetic_tsum_norm P sigma hs hsum] at h
  exact h

theorem classPrimeComponentCarrier_totalVariation_bounds
    (P : Set Nat) (sigma : Real) (hs : 0 < sigma)
    (hsum : Summable (classPowerWeight P sigma)) (f g : ArithmeticFunction Real)
    (hf : Summable (fun n : Nat => norm (f n)))
    (hg : Summable (fun n : Nat => norm (g n))) :
    And
      (tsum (fun n : Nat => norm (f n - g n)) / 2 <=
        classPrimePowerErrorConstant P sigma *
          (tsum (fun n : Nat => norm
            ((classPrimeComponentNoiseArithmetic P sigma * f) n -
              (classPrimeComponentNoiseArithmetic P sigma * g) n)) / 2))
      (tsum (fun n : Nat => norm
        ((classPrimeComponentNoiseArithmetic P sigma * f) n -
          (classPrimeComponentNoiseArithmetic P sigma * g) n)) / 2 <=
        tsum (fun n : Nat => norm (f n - g n)) / 2) := by
  have hdiff : Summable (fun n : Nat => norm ((f - g) n)) := by
    apply (hf.add hg).of_nonneg_of_le (fun n => norm_nonneg _) 
    intro n
    exact norm_sub_le (f n) (g n)
  have hrec := classPrimeComponentCarrier_l1_recovery P sigma hs hsum (f - g) hdiff
  have hcon := classPrimeComponentCarrier_l1_contraction P sigma hs hsum (f - g) hdiff
  change And
    (tsum (fun n : Nat => norm ((f - g) n)) / 2 <= classPrimePowerErrorConstant P sigma *
      (tsum (fun n : Nat => norm
        ((classPrimeComponentNoiseArithmetic P sigma * f -
          classPrimeComponentNoiseArithmetic P sigma * g) n)) / 2))
    (tsum (fun n : Nat => norm
      ((classPrimeComponentNoiseArithmetic P sigma * f -
        classPrimeComponentNoiseArithmetic P sigma * g) n)) / 2 <=
      tsum (fun n : Nat => norm ((f - g) n)) / 2)
  rw [<- mul_sub]
  constructor
  . calc
      _ <= (classPrimePowerErrorConstant P sigma *
          tsum (fun n : Nat => norm
            ((classPrimeComponentNoiseArithmetic P sigma * (f - g)) n))) / 2 :=
        div_le_div_of_nonneg_right hrec (by norm_num)
      _ = _ := by ring
  . exact div_le_div_of_nonneg_right hcon (by norm_num)

theorem classPrimeComponentCarrier_probability_totalVariation_bounds
    (P : Set Nat) (sigma : Real) (hs : 0 < sigma)
    (hsum : Summable (classPowerWeight P sigma)) (f g : ArithmeticFunction Real)
    (hfpos : forall n : Nat, 0 <= f n) (hgpos : forall n : Nat, 0 <= g n)
    (hf : HasSum (fun n : Nat => f n) 1) (hg : HasSum (fun n : Nat => g n) 1) :
    And
      (tsum (fun n : Nat => norm (f n - g n)) / 2 <=
        classPrimePowerErrorConstant P sigma *
          (tsum (fun n : Nat => norm
            ((classPrimeComponentNoiseArithmetic P sigma * f) n -
              (classPrimeComponentNoiseArithmetic P sigma * g) n)) / 2))
      (tsum (fun n : Nat => norm
        ((classPrimeComponentNoiseArithmetic P sigma * f) n -
          (classPrimeComponentNoiseArithmetic P sigma * g) n)) / 2 <=
        tsum (fun n : Nat => norm (f n - g n)) / 2) := by
  apply classPrimeComponentCarrier_totalVariation_bounds P sigma hs hsum f g
  . apply hf.summable.congr
    intro n
    exact (by rw [Real.norm_eq_abs, abs_of_nonneg (hfpos n)] :
      norm (f n) = f n).symm
  . apply hg.summable.congr
    intro n
    exact (by rw [Real.norm_eq_abs, abs_of_nonneg (hgpos n)] :
      norm (g n) = g n).symm

theorem classPrimeComponentCarrier_l1_recovery_constant_optimal
    (P : Set Nat) (sigma : Real) (hs : 0 < sigma)
    (hsum : Summable (classPowerWeight P sigma)) (C : Real)
    (hC : forall f : ArithmeticFunction Real,
      Summable (fun n : Nat => norm (f n)) ->
        tsum (fun n : Nat => norm (f n)) <= C *
          tsum (fun n : Nat => norm ((classPrimeComponentNoiseArithmetic P sigma * f) n))) :
    classPrimePowerErrorConstant P sigma <= C := by
  have h := hC (classPrimeComponentInverseArithmetic P sigma)
    (classPrimeComponentInverseArithmetic_norm_summable P sigma hs hsum)
  have hinv : classPrimeComponentNoiseArithmetic P sigma *
      classPrimeComponentInverseArithmetic P sigma = 1 := by
    rw [mul_comm]
    exact classPrimeComponentInverse_mul_noise P sigma hs hsum
  have hone : tsum (fun n : Nat => norm ((1 : ArithmeticFunction Real) n)) = 1 := by
    have heq : (fun n : Nat => norm ((1 : ArithmeticFunction Real) n)) =
        (fun n : Nat => if n = 1 then (1 : Real) else 0) := by
      funext n
      by_cases hn : n = 1 <;> simp [hn]
    rw [heq]
    simp
  rw [classPrimeComponentInverseArithmetic_tsum_norm P sigma hs hsum,
    hinv, hone, mul_one] at h
  exact h

theorem classPrimeComponentCarrier_probability_output
    (P : Set Nat) (sigma : Real) (hs : 0 < sigma)
    (hsum : Summable (classPowerWeight P sigma)) (f : ArithmeticFunction Real)
    (hfpos : forall n : Nat, 0 <= f n) (hf : HasSum (fun n : Nat => f n) 1) :
    And (forall n : Nat, 0 <= (classPrimeComponentNoiseArithmetic P sigma * f) n)
      (HasSum (fun n : Nat => (classPrimeComponentNoiseArithmetic P sigma * f) n) 1) := by
  have hc := classPrimeComponentCarrier_inverse_norm_certificate P sigma hs hsum
  have hf' : Summable (fun n : Nat => norm (f n)) := by
    apply hf.summable.congr
    intro n
    exact (by rw [Real.norm_eq_abs, abs_of_nonneg (hfpos n)] : norm (f n) = f n).symm
  have hmass := convolution_hasSum (classPrimeComponentNoiseArithmetic P sigma) f
    (classPrimeComponentNoise_norm_hasSum_one P sigma hs hsum).summable hf'
  rw [hc.2.1.tsum_eq, hf.tsum_eq, one_mul] at hmass
  refine And.intro ?_ hmass
  intro n
  rw [ArithmeticFunction.mul_apply]
  apply Finset.sum_nonneg
  intro x hx
  exact mul_nonneg (hc.1 x.1) (hfpos x.2)

end PrimeFactorOscillations.PrimeClassSampling

/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Proof.PrimeClassDeletion.PrimeComponentCarrierSeparation
import PrimeFactorOscillations.Proof.PrimeClassDeletion.PrimeComponentCarrierStability

/-!
# Attained sharpness of the probability-channel inverse bound

The positive and negative parts of the separated inverse give probability
laws at distance one whose noisy images have distance exactly one over B.
These laws may use integers outside the original supported prime class.
-/

set_option autoImplicit false
set_option Elab.async false

namespace PrimeFactorOscillations.PrimeClassSampling

noncomputable def classPrimeComponentExtremizerPositive
    (P : Set Nat) (sigma : Real) : ArithmeticFunction Real where
  toFun n := (norm (classPrimeComponentSeparatedInverse P sigma n) +
    classPrimeComponentSeparatedInverse P sigma n) / (2 * classPrimePowerErrorConstant P sigma)
  map_zero' := by simp

noncomputable def classPrimeComponentExtremizerNegative
    (P : Set Nat) (sigma : Real) : ArithmeticFunction Real where
  toFun n := (norm (classPrimeComponentSeparatedInverse P sigma n) -
    classPrimeComponentSeparatedInverse P sigma n) / (2 * classPrimePowerErrorConstant P sigma)
  map_zero' := by simp

private theorem norm_inverse_scale (B x : Real) (hB : 0 < B) :
    norm ((1 / B) * x) = norm x / B := by
  rw [norm_mul, Real.norm_eq_abs, abs_of_pos (one_div_pos.mpr hB)]
  ring

theorem classPrimeComponentExtremizer_difference (P : Set Nat) (sigma : Real) :
    classPrimeComponentExtremizerPositive P sigma -
      classPrimeComponentExtremizerNegative P sigma =
        SMul.smul (1 / classPrimePowerErrorConstant P sigma)
          (classPrimeComponentSeparatedInverse P sigma) := by
  have hB := ne_of_gt (classPrimePowerErrorConstant_pos P sigma)
  ext n
  change (norm (classPrimeComponentSeparatedInverse P sigma n) +
      classPrimeComponentSeparatedInverse P sigma n) / (2 * classPrimePowerErrorConstant P sigma) -
    (norm (classPrimeComponentSeparatedInverse P sigma n) -
      classPrimeComponentSeparatedInverse P sigma n) / (2 * classPrimePowerErrorConstant P sigma) =
        (1 / classPrimePowerErrorConstant P sigma) * classPrimeComponentSeparatedInverse P sigma n
  field_simp [hB]
  ring

theorem classPrimeComponentExtremizer_probability_laws
    (P : Set Nat) (sigma : Real) (hs : 0 < sigma)
    (hsum : Summable (classPowerWeight P sigma)) :
    And (forall n : Nat, 0 <= classPrimeComponentExtremizerPositive P sigma n)
      (And (forall n : Nat, 0 <= classPrimeComponentExtremizerNegative P sigma n)
        (And (HasSum (fun n : Nat => classPrimeComponentExtremizerPositive P sigma n) 1)
          (HasSum (fun n : Nat => classPrimeComponentExtremizerNegative P sigma n) 1))) := by
  have hB := classPrimePowerErrorConstant_pos P sigma
  have hden : 0 < 2 * classPrimePowerErrorConstant P sigma := mul_pos (by norm_num) hB
  have hn := classPrimeComponentSeparatedInverse_norm_hasSum P sigma hs hsum
  have hm := classPrimeComponentSeparatedInverse_hasSum_zero P sigma hs hsum
  have hp := (hn.add hm).div_const (2 * classPrimePowerErrorConstant P sigma)
  have hq := (hn.sub hm).div_const (2 * classPrimePowerErrorConstant P sigma)
  have hp' : HasSum (fun n : Nat => classPrimeComponentExtremizerPositive P sigma n) 1 := by
    change HasSum (fun n : Nat =>
      (norm (classPrimeComponentSeparatedInverse P sigma n) +
        classPrimeComponentSeparatedInverse P sigma n) /
          (2 * classPrimePowerErrorConstant P sigma)) 1
    simpa only [add_zero, div_self (ne_of_gt hden)] using hp
  have hq' : HasSum (fun n : Nat => classPrimeComponentExtremizerNegative P sigma n) 1 := by
    change HasSum (fun n : Nat =>
      (norm (classPrimeComponentSeparatedInverse P sigma n) -
        classPrimeComponentSeparatedInverse P sigma n) /
          (2 * classPrimePowerErrorConstant P sigma)) 1
    simpa only [sub_zero, div_self (ne_of_gt hden)] using hq
  refine And.intro ?_ (And.intro ?_ (And.intro hp' hq'))
  . intro n
    change 0 <= (norm (classPrimeComponentSeparatedInverse P sigma n) +
      classPrimeComponentSeparatedInverse P sigma n) / (2 * classPrimePowerErrorConstant P sigma)
    have ha : -norm (classPrimeComponentSeparatedInverse P sigma n) <=
        classPrimeComponentSeparatedInverse P sigma n := by
      rw [Real.norm_eq_abs]
      exact neg_abs_le _
    exact div_nonneg (by linarith) hden.le
  . intro n
    change 0 <= (norm (classPrimeComponentSeparatedInverse P sigma n) -
      classPrimeComponentSeparatedInverse P sigma n) / (2 * classPrimePowerErrorConstant P sigma)
    have ha : classPrimeComponentSeparatedInverse P sigma n <=
        norm (classPrimeComponentSeparatedInverse P sigma n) := by
      rw [Real.norm_eq_abs]
      exact le_abs_self _
    exact div_nonneg (sub_nonneg.mpr ha) hden.le

theorem classPrimeComponentExtremizer_input_distance
    (P : Set Nat) (sigma : Real) (hs : 0 < sigma)
    (hsum : Summable (classPowerWeight P sigma)) :
    tsum (fun n : Nat => norm (classPrimeComponentExtremizerPositive P sigma n -
      classPrimeComponentExtremizerNegative P sigma n)) / 2 = 1 := by
  have hB := classPrimePowerErrorConstant_pos P sigma
  have h := (classPrimeComponentSeparatedInverse_norm_hasSum P sigma hs hsum).div_const
    (classPrimePowerErrorConstant P sigma)
  have heq : (fun n : Nat => norm (classPrimeComponentExtremizerPositive P sigma n -
      classPrimeComponentExtremizerNegative P sigma n)) =
      (fun n : Nat => norm (classPrimeComponentSeparatedInverse P sigma n) /
        classPrimePowerErrorConstant P sigma) := by
    funext n
    change norm ((classPrimeComponentExtremizerPositive P sigma -
      classPrimeComponentExtremizerNegative P sigma) n) = _
    rw [classPrimeComponentExtremizer_difference]
    exact norm_inverse_scale _ _ hB
  rw [<- heq] at h
  rw [h.tsum_eq]
  field_simp [ne_of_gt hB]

theorem classPrimeComponentExtremizer_output_distance
    (P : Set Nat) (sigma : Real) (hs : 0 < sigma)
    (hsum : Summable (classPowerWeight P sigma)) :
    tsum (fun n : Nat => norm
      ((classPrimeComponentNoiseArithmetic P sigma *
        classPrimeComponentExtremizerPositive P sigma) n -
      (classPrimeComponentNoiseArithmetic P sigma *
        classPrimeComponentExtremizerNegative P sigma) n)) / 2 =
          1 / classPrimePowerErrorConstant P sigma := by
  have hB := classPrimePowerErrorConstant_pos P sigma
  have hout : classPrimeComponentNoiseArithmetic P sigma *
      classPrimeComponentExtremizerPositive P sigma -
      classPrimeComponentNoiseArithmetic P sigma *
        classPrimeComponentExtremizerNegative P sigma =
      SMul.smul (1 / classPrimePowerErrorConstant P sigma)
        (classPrimeComponentNoiseArithmetic P sigma *
          classPrimeComponentSeparatedInverse P sigma) := by
    rw [<- mul_sub, classPrimeComponentExtremizer_difference]
    ext n
    rw [ArithmeticFunction.mul_apply]
    change n.divisorsAntidiagonal.sum (fun x =>
      classPrimeComponentNoiseArithmetic P sigma x.1 *
        ((1 / classPrimePowerErrorConstant P sigma) *
          classPrimeComponentSeparatedInverse P sigma x.2)) =
      (1 / classPrimePowerErrorConstant P sigma) *
        (classPrimeComponentNoiseArithmetic P sigma *
          classPrimeComponentSeparatedInverse P sigma) n
    rw [ArithmeticFunction.mul_apply, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro x hx
    ring
  have heq : (fun n : Nat => norm
      ((classPrimeComponentNoiseArithmetic P sigma * classPrimeComponentExtremizerPositive P sigma) n -
      (classPrimeComponentNoiseArithmetic P sigma * classPrimeComponentExtremizerNegative P sigma) n)) =
      (fun n : Nat => norm
        ((classPrimeComponentNoiseArithmetic P sigma * classPrimeComponentSeparatedInverse P sigma) n) /
          classPrimePowerErrorConstant P sigma) := by
    funext n
    change norm ((classPrimeComponentNoiseArithmetic P sigma *
      classPrimeComponentExtremizerPositive P sigma -
      classPrimeComponentNoiseArithmetic P sigma *
        classPrimeComponentExtremizerNegative P sigma) n) = _
    rw [hout]
    exact norm_inverse_scale _ _ hB
  have h := (classPrimeComponentNoise_separatedInverse_norm_hasSum P sigma hs hsum).div_const
    (classPrimePowerErrorConstant P sigma)
  rw [<- heq] at h
  rw [h.tsum_eq]
  ring

theorem classPrimeComponentCarrier_probability_extremizers
    (P : Set Nat) (sigma : Real) (hs : 0 < sigma)
    (hsum : Summable (classPowerWeight P sigma)) :
    exists f g : ArithmeticFunction Real,
      And (forall n : Nat, 0 <= f n) (And (forall n : Nat, 0 <= g n)
        (And (HasSum (fun n : Nat => f n) 1) (And (HasSum (fun n : Nat => g n) 1)
          (And (tsum (fun n : Nat => norm (f n - g n)) / 2 = 1)
            (tsum (fun n : Nat => norm
              ((classPrimeComponentNoiseArithmetic P sigma * f) n -
                (classPrimeComponentNoiseArithmetic P sigma * g) n)) / 2 =
                  1 / classPrimePowerErrorConstant P sigma))))) := by
  have hp := classPrimeComponentExtremizer_probability_laws P sigma hs hsum
  refine Exists.intro (classPrimeComponentExtremizerPositive P sigma)
    (Exists.intro (classPrimeComponentExtremizerNegative P sigma)
      (And.intro hp.1 (And.intro hp.2.1
        (And.intro hp.2.2.1 (And.intro hp.2.2.2 (And.intro ?_ ?_))))))
  . exact classPrimeComponentExtremizer_input_distance P sigma hs hsum
  . exact classPrimeComponentExtremizer_output_distance P sigma hs hsum

theorem classPrimeComponentCarrier_probability_recovery_constant_optimal
    (P : Set Nat) (sigma : Real) (hs : 0 < sigma)
    (hsum : Summable (classPowerWeight P sigma)) (C : Real)
    (hC : forall f g : ArithmeticFunction Real,
      (forall n : Nat, 0 <= f n) -> (forall n : Nat, 0 <= g n) ->
      HasSum (fun n : Nat => f n) 1 -> HasSum (fun n : Nat => g n) 1 ->
      tsum (fun n : Nat => norm (f n - g n)) / 2 <= C *
        (tsum (fun n : Nat => norm
          ((classPrimeComponentNoiseArithmetic P sigma * f) n -
            (classPrimeComponentNoiseArithmetic P sigma * g) n)) / 2)) :
    classPrimePowerErrorConstant P sigma <= C := by
  have hp := classPrimeComponentExtremizer_probability_laws P sigma hs hsum
  have h := hC (classPrimeComponentExtremizerPositive P sigma)
    (classPrimeComponentExtremizerNegative P sigma) hp.1 hp.2.1 hp.2.2.1 hp.2.2.2
  rw [classPrimeComponentExtremizer_input_distance P sigma hs hsum,
    classPrimeComponentExtremizer_output_distance P sigma hs hsum] at h
  have hB := classPrimePowerErrorConstant_pos P sigma
  have h' := mul_le_mul_of_nonneg_right h hB.le
  simpa only [one_mul, mul_assoc, one_div_mul_cancel (ne_of_gt hB), mul_one] using h'

end PrimeFactorOscillations.PrimeClassSampling

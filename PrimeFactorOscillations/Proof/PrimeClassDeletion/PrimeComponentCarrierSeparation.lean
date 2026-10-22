/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.ArithmeticFunctionFourDilation
import PrimeFactorOscillations.Proof.PrimeClassDeletion.PrimeComponentCarrierNorm

/-!
# A mass-zero inverse probe with disjoint supports

Subtracting the dilation by four from the inverse doubles its absolute
mass while giving total signed mass zero. The noisy probe is exactly the
difference of point masses at one and four.
-/

set_option autoImplicit false
set_option Elab.async false

namespace PrimeFactorOscillations.PrimeClassSampling

open PrimeFactorOscillations.ArithmeticFunctionL1

noncomputable def classPrimeComponentSeparatedInverse
    (P : Set Nat) (sigma : Real) : ArithmeticFunction Real :=
  classPrimeComponentInverseArithmetic P sigma -
    fourAtom * classPrimeComponentInverseArithmetic P sigma

theorem classPrimeComponentInverse_zero_of_four_dvd
    (P : Set Nat) (sigma : Real) (n : Nat) (hfour : Dvd.dvd 4 n) :
    classPrimeComponentInverseArithmetic P sigma n = 0 := by
  apply classPrimeComponentInverse_zero_of_not_squarefree P sigma n
  intro hn
  have htwo : IsUnit (2 : Nat) := hn 2 (by simpa only [Nat.reduceMul] using hfour)
  norm_num at htwo

theorem classPrimeComponentSeparatedInverse_norm_apply
    (P : Set Nat) (sigma : Real) (n : Nat) :
    norm (classPrimeComponentSeparatedInverse P sigma n) =
      norm (classPrimeComponentInverseArithmetic P sigma n) +
        norm ((fourAtom * classPrimeComponentInverseArithmetic P sigma) n) := by
  change norm (classPrimeComponentInverseArithmetic P sigma n -
    (fourAtom * classPrimeComponentInverseArithmetic P sigma) n) = _
  by_cases hd : Dvd.dvd 4 n
  . rw [classPrimeComponentInverse_zero_of_four_dvd P sigma n hd]
    simp
  . rw [fourAtom_mul_apply, ite_eq_right hd]
    simp

theorem classPrimeComponentSeparatedInverse_norm_hasSum
    (P : Set Nat) (sigma : Real) (hs : 0 < sigma)
    (hsum : Summable (classPowerWeight P sigma)) :
    HasSum (fun n : Nat => norm (classPrimeComponentSeparatedInverse P sigma n))
      (2 * classPrimePowerErrorConstant P sigma) := by
  have hr : HasSum (fun n : Nat => norm (classPrimeComponentInverseArithmetic P sigma n))
      (classPrimePowerErrorConstant P sigma) := by
    rw [<- classPrimeComponentInverseArithmetic_tsum_norm P sigma hs hsum]
    exact (classPrimeComponentInverseArithmetic_norm_summable P sigma hs hsum).hasSum
  have hd := fourAtom_norm_mul_hasSum (classPrimeComponentInverseArithmetic P sigma)
    (classPrimeComponentInverseArithmetic_norm_summable P sigma hs hsum)
  rw [classPrimeComponentInverseArithmetic_tsum_norm P sigma hs hsum] at hd
  have h := hr.add hd
  have heq : (fun n : Nat => norm (classPrimeComponentSeparatedInverse P sigma n)) =
      (fun n : Nat => norm (classPrimeComponentInverseArithmetic P sigma n) +
        norm ((fourAtom * classPrimeComponentInverseArithmetic P sigma) n)) :=
    funext (classPrimeComponentSeparatedInverse_norm_apply P sigma)
  rw [<- heq] at h
  simpa only [two_mul] using h

theorem classPrimeComponentSeparatedInverse_hasSum_zero
    (P : Set Nat) (sigma : Real) (hs : 0 < sigma)
    (hsum : Summable (classPowerWeight P sigma)) :
    HasSum (fun n : Nat => classPrimeComponentSeparatedInverse P sigma n) 0 := by
  have hr := (classPrimeComponentInverseArithmetic_norm_summable P sigma hs hsum).of_norm.hasSum
  have hd := fourAtom_mul_hasSum (classPrimeComponentInverseArithmetic P sigma)
    (classPrimeComponentInverseArithmetic_norm_summable P sigma hs hsum)
  have h := hr.sub hd
  rw [sub_self] at h
  exact h

theorem classPrimeComponentNoise_mul_separatedInverse
    (P : Set Nat) (sigma : Real) (hs : 0 < sigma)
    (hsum : Summable (classPowerWeight P sigma)) :
    classPrimeComponentNoiseArithmetic P sigma * classPrimeComponentSeparatedInverse P sigma =
      1 - fourAtom := by
  have hinv : classPrimeComponentNoiseArithmetic P sigma *
      classPrimeComponentInverseArithmetic P sigma = 1 := by
    rw [mul_comm]
    exact classPrimeComponentInverse_mul_noise P sigma hs hsum
  unfold classPrimeComponentSeparatedInverse
  rw [mul_sub, hinv, mul_left_comm (classPrimeComponentNoiseArithmetic P sigma) fourAtom,
    hinv, mul_one]

theorem classPrimeComponentNoise_separatedInverse_norm_hasSum
    (P : Set Nat) (sigma : Real) (hs : 0 < sigma)
    (hsum : Summable (classPowerWeight P sigma)) :
    HasSum (fun n : Nat => norm
      ((classPrimeComponentNoiseArithmetic P sigma * classPrimeComponentSeparatedInverse P sigma) n)) 2 := by
  rw [classPrimeComponentNoise_mul_separatedInverse P sigma hs hsum]
  have hone : HasSum (fun n : Nat => (1 : ArithmeticFunction Real) n) 1 :=
    hasSum_ite_eq 1 1
  have h := hone.add fourAtom_hasSum_one
  have heq : (fun n : Nat => norm ((1 - fourAtom : ArithmeticFunction Real) n)) =
      (fun n : Nat => (1 : ArithmeticFunction Real) n + fourAtom n) := by
    funext n
    change norm ((1 : ArithmeticFunction Real) n - fourAtom n) =
      (1 : ArithmeticFunction Real) n + fourAtom n
    by_cases hn1 : n = 1
    . subst n
      norm_num [fourAtom]
    . by_cases hn4 : n = 4
      . subst n
        norm_num [fourAtom]
      . simp [fourAtom, hn1, hn4]
  rw [heq]
  simpa only [one_add_one_eq_two] using h

end PrimeFactorOscillations.PrimeClassSampling

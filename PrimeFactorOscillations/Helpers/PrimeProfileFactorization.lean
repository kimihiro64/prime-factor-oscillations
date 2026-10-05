/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.PrimeProfile

/-!
# Exact finite prime-profile factorization

Restoring the finite logarithmic clock cancels the normalization factors.
The clock is positive once the prefix contains the prime two.
-/

set_option autoImplicit false
set_option Elab.async false

namespace PrimeFactorOscillations

theorem primePrefixProfile_mul_exp_logSum (N : Nat) (z : Complex) :
    primePrefixProfile N z *
      Complex.exp ((((primeProfilePrefixSet N).sum
        (fun p => Real.log (1 + primeProfileWeight (p : Nat))) : Real) : Complex) * z) =
      (primeProfilePrefixSet N).prod
        (fun p => 1 + (primeProfileWeight (p : Nat) : Complex) * z) := by
  unfold primePrefixProfile Complex.normalizedLinearFactor
  rw [Finset.prod_mul_distrib, <- Complex.exp_sum, mul_assoc, <- Complex.exp_add]
  have hsum : (primeProfilePrefixSet N).sum
      (fun p => -(Real.log (1 + primeProfileWeight (p : Nat)) : Complex) * z) =
      -((((primeProfilePrefixSet N).sum
        (fun p => Real.log (1 + primeProfileWeight (p : Nat))) : Real) : Complex)) * z := by
    rw [<- Finset.sum_mul, Finset.sum_neg_distrib]
    congr 2
    simp
  rw [hsum]
  simp

theorem primePrefixProfile_logSum_pos (N : Nat) (hN : 2 <= N) :
    0 < (primeProfilePrefixSet N).sum
      (fun p => Real.log (1 + primeProfileWeight (p : Nat))) := by
  let two : Nat.Primes := Subtype.mk 2 Nat.prime_two
  have htwo : Membership.mem (primeProfilePrefixSet N) two := by
    apply (mem_primeProfilePrefixSet two N).mpr
    exact hN
  have hnonneg : forall p, Membership.mem (primeProfilePrefixSet N) p ->
      0 <= Real.log (1 + primeProfileWeight (p : Nat)) := by
    intro p _
    apply Real.log_nonneg
    linarith [primeProfileWeight_nonneg (p : Nat)]
  have htwoValue : Real.log (1 + primeProfileWeight (two : Nat)) = Real.log 2 := by
    norm_num [two, primeProfileWeight]
  have hle := Finset.single_le_sum hnonneg htwo
  rw [htwoValue] at hle
  exact (Real.log_pos (by norm_num : (1 : Real) < 2)).trans_le hle

end PrimeFactorOscillations


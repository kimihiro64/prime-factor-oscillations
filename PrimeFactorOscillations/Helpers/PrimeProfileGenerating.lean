/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import BombieriVinogradov.Helpers.ComplexAnalysis.CauchyTaylor
import PrimeFactorOscillations.Helpers.PrimeProfileFactorization
import PrimeFactorOscillations.Mathlib.Analysis.Analytic.ExponentialConvolution
import PrimeFactorOscillations.Mathlib.Analysis.Analytic.FactorialPolynomial

/-!
# Exact generating coefficient at the finite prime clock

The restored finite product and normalized exponential convolution identify
the actual real factorial convolution with the finite product coefficient.
-/

set_option autoImplicit false
set_option Elab.async false

namespace PrimeFactorOscillations

open BombieriVinogradov.ComplexAnalysis

theorem primePrefixProfile_factorialConvolution_eq_product_coefficient (N r : Nat) :
    Nat.factorialConvolution
      (fun j => (taylorCoefficient (primePrefixProfile N) 0 j).re) r
      ((primeProfilePrefixSet N).sum
        (fun p => Real.log (1 + primeProfileWeight (p : Nat)))) =
      (taylorCoefficient (fun z : Complex =>
        (primeProfilePrefixSet N).prod
          (fun p => 1 + (primeProfileWeight (p : Nat) : Complex) * z)) 0 r).re := by
  let B : Real := (primeProfilePrefixSet N).sum
    (fun p => Real.log (1 + primeProfileWeight (p : Nat)))
  have heq : (fun z : Complex => primePrefixProfile N z * Complex.exp ((B : Complex) * z)) =
      (fun z : Complex => (primeProfilePrefixSet N).prod
        (fun p => 1 + (primeProfileWeight (p : Nat) : Complex) * z)) := by
    funext z
    exact primePrefixProfile_mul_exp_logSum N z
  have hconv := Complex.normalized_iteratedDeriv_mul_exp_zero
    (primePrefixProfile N) (differentiable_primePrefixProfile N) (B : Complex) r
  rw [heq] at hconv
  unfold taylorCoefficient
  rw [hconv]
  change _ = Complex.reAddGroupHom _
  rw [map_sum]
  simp only [Complex.coe_reAddGroupHom]
  unfold Nat.factorialConvolution
  apply Finset.sum_congr rfl
  intro j _
  have hcast : (B : Complex) ^ (r - j) / ((r - j).factorial : Complex) =
      Complex.ofReal (B ^ (r - j) / ((r - j).factorial : Real)) := by
    push_cast
    rfl
  simp_rw [mul_div_assoc]
  rw [hcast]
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]
  dsimp [B]

end PrimeFactorOscillations


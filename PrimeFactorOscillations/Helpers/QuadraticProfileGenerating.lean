/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.NicolasCanonicalSign
import PrimeFactorOscillations.Helpers.PrimeProfileThetaClock
import PrimeFactorOscillations.Helpers.QuadraticProfileCoefficients
import PrimeFactorOscillations.Mathlib.Analysis.Analytic.ExponentialConvolution
import PrimeFactorOscillations.Mathlib.Analysis.Analytic.FactorialPolynomial
import PrimeFactorOscillations.Mathlib.Analysis.Calculus.IteratedDeriv.LinearProduct

/-!
# Actual family symmetric coefficients and their two clocks

The entire profile restores the exact finite generating product at the
arithmetic clock. Its coefficients are the actual elementary symmetric
polynomials of the local odds, including zero exceptional coordinates.
-/

set_option autoImplicit false
set_option Elab.async false

namespace PrimeFactorOscillations.QuadraticPrimeLaw

open Filter BombieriVinogradov.ComplexAnalysis Robin1984

noncomputable def arithmeticClock (law : QuadraticPrimeLaw) (N : Nat) : Real :=
  law.nu * (primeProfilePrefixSet N).sum
    (fun p => Real.log (1 + primeProfileWeight (p : Nat)))

noncomputable def referenceClock (law : QuadraticPrimeLaw) (N : Nat) : Real :=
  law.nu * (Real.eulerMascheroniConstant +
    Real.log (Real.log (Chebyshev.theta (N : Real))))

noncomputable def prefixEsymm (law : QuadraticPrimeLaw) (N r : Nat) : Real :=
  ((primeProfilePrefixSet N).val.map law.weight).esymm r

noncomputable def densityRatio (law : QuadraticPrimeLaw) (N r : Nat) : Real :=
  law.prefixEsymm N (r - 1) / law.prefixEsymm N r

noncomputable def referenceRatio (law : QuadraticPrimeLaw) (r : Nat) (u : Real) : Real :=
  Nat.factorialConvolution law.realCoefficient (r - 1) u /
    Nat.factorialConvolution law.realCoefficient r u

theorem complexPrefix_mul_exp_clock (law : QuadraticPrimeLaw) (N : Nat) (z : Complex) :
    law.complexPrefix N z * Complex.exp ((law.arithmeticClock N : Complex) * z) =
      (primeProfilePrefixSet N).prod (fun p => 1 + (law.weight p : Complex) * z) := by
  unfold complexPrefix complexFactor
  rw [Finset.prod_mul_distrib, <- Complex.exp_sum, mul_assoc, <- Complex.exp_add]
  have hsum : (primeProfilePrefixSet N).sum
      (fun p => -((law.nu * Real.log (1 + primeProfileWeight (p : Nat)) : Real) : Complex) * z) =
      -(law.arithmeticClock N : Complex) * z := by
    rw [<- Finset.sum_mul, Finset.sum_neg_distrib]
    congr 2
    unfold arithmeticClock
    simp only [Complex.ofReal_mul, Complex.ofReal_sum, Finset.mul_sum]
  rw [hsum]
  simp

theorem prefix_factorialConvolution_eq_product_coefficient
    (law : QuadraticPrimeLaw) (N r : Nat) :
    Nat.factorialConvolution
      (fun j => (taylorCoefficient (law.complexPrefix N) 0 j).re) r (law.arithmeticClock N) =
      (taylorCoefficient (fun z : Complex =>
        (primeProfilePrefixSet N).prod (fun p => 1 + (law.weight p : Complex) * z)) 0 r).re := by
  let B := law.arithmeticClock N
  have heq : (fun z : Complex => law.complexPrefix N z * Complex.exp ((B : Complex) * z)) =
      (fun z : Complex => (primeProfilePrefixSet N).prod
        (fun p => 1 + (law.weight p : Complex) * z)) := by
    funext z
    exact law.complexPrefix_mul_exp_clock N z
  have hconv := Complex.normalized_iteratedDeriv_mul_exp_zero
    (law.complexPrefix N) (law.differentiable_complexPrefix N) (B : Complex) r
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
      Complex.ofReal (B ^ (r - j) / ((r - j).factorial : Real)) := by push_cast; rfl
  simp_rw [mul_div_assoc]
  rw [hcast]
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]
  rfl

theorem prefix_factorialConvolution_eq_esymm (law : QuadraticPrimeLaw) (N r : Nat) :
    Nat.factorialConvolution
      (fun j => (taylorCoefficient (law.complexPrefix N) 0 j).re) r (law.arithmeticClock N) =
      law.prefixEsymm N r := by
  rw [law.prefix_factorialConvolution_eq_product_coefficient]
  unfold taylorCoefficient
  rw [Finset.normalized_iteratedDeriv_prod_linear_zero]
  have hmap : (primeProfilePrefixSet N).val.map (fun p => (law.weight p : Complex)) =
      ((primeProfilePrefixSet N).val.map law.weight).map Complex.ofRealHom := by
    rw [Multiset.map_map]
    rfl
  rw [hmap, <- RingHom.map_multiset_esymm]
  rfl

theorem densityRatio_eq_factorialConvolution (law : QuadraticPrimeLaw) (N r : Nat) :
    law.densityRatio N r =
      Nat.factorialConvolution (fun j => (taylorCoefficient (law.complexPrefix N) 0 j).re)
          (r - 1) (law.arithmeticClock N) /
        Nat.factorialConvolution (fun j => (taylorCoefficient (law.complexPrefix N) 0 j).re)
          r (law.arithmeticClock N) := by
  rw [law.prefix_factorialConvolution_eq_esymm, law.prefix_factorialConvolution_eq_esymm]
  rfl

theorem clock_difference_eq_nicolas (law : QuadraticPrimeLaw) (N : Nat)
    (hTheta : 1 < Chebyshev.theta (N : Real)) :
    law.referenceClock N - law.arithmeticClock N =
      law.nu * nicolasLogMertensOscillation (N : Real) := by
  rw [nicolasLog_nat_eq_primeProfile_clock_difference N hTheta]
  unfold arithmeticClock referenceClock
  ring

theorem tendsto_referenceClock_atTop (law : QuadraticPrimeLaw) :
    Tendsto law.referenceClock atTop atTop := by
  apply tendsto_atTop.2
  intro b
  filter_upwards [tendsto_primeProfile_thetaClock_atTop.eventually_ge_atTop (b / law.nu)]
    with N hN
  have h := mul_le_mul_of_nonneg_left hN law.nu_pos.le
  have hCancel : law.nu * (b / law.nu) = b := by field_simp [law.nu_pos.ne']
  rw [hCancel] at h
  exact h

theorem tendsto_clock_difference_zero (law : QuadraticPrimeLaw) :
    Tendsto (fun N => law.arithmeticClock N - law.referenceClock N) atTop (nhds 0) := by
  have h := tendsto_primePrefixProfile_logSum_sub_thetaClock.const_mul law.nu
  simpa only [arithmeticClock, referenceClock, mul_sub, mul_zero] using h

end PrimeFactorOscillations.QuadraticPrimeLaw

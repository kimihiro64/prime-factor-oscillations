/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.PrimeProfileDenominator
import PrimeFactorOscillations.Helpers.PrimeProfileDerivative
import PrimeFactorOscillations.Mathlib.Analysis.Analytic.FactorialRatioDerivative

/-!
# Uniform reference-ratio slope

The actual prime profile supplies every denominator and derivative bound.
For sufficiently large rank the reference ratio has a strictly negative slope.
-/

set_option autoImplicit false
set_option Elab.async false

namespace PrimeFactorOscillations

theorem exists_primeProfile_reference_slope_bound (b : Real) (hb : 0 <= b) :
    exists (r0 : Nat) (K : Real), 0 < r0 /\ 0 <= K /\
      forall (r : Nat), r0 <= r -> forall (u : Real), 0 < u -> (r : Real) / u <= b ->
        abs (deriv (fun v : Real =>
          Nat.factorialConvolution primeProfileRealCoefficient (r - 1) v /
            Nat.factorialConvolution primeProfileRealCoefficient r v) u +
              (r : Real) / u ^ 2) <= K / u ^ 2 /\
        (2 * K <= r ->
          -(3 * (r : Real)) / (2 * u ^ 2) <=
            deriv (fun v : Real =>
              Nat.factorialConvolution primeProfileRealCoefficient (r - 1) v /
                Nat.factorialConvolution primeProfileRealCoefficient r v) u /\
          deriv (fun v : Real =>
            Nat.factorialConvolution primeProfileRealCoefficient (r - 1) v /
              Nat.factorialConvolution primeProfileRealCoefficient r v) u <=
                -(r : Real) / (2 * u ^ 2)) := by
  choose r0 hr0 hLower using exists_primeProfile_normalized_coefficient_lower_bound b hb
  choose M hM hDeriv using exists_primeProfile_normalized_derivative_bounds b hb
  let d := Real.exp (-(b ^ 2 * tsum (fun p : Nat.Primes =>
    (primeProfileWeight (p : Nat)) ^ 2)) / 2) / 2
  have hd : 0 < d := by dsimp [d]; positivity
  let Q := M / d
  have hQ : 0 <= Q := div_nonneg hM hd.le
  let K := 2 * b * Q + b ^ 2 * (Q + Q ^ 2)
  have hK : 0 <= K := by dsimp [K]; positivity
  refine Exists.intro r0 (Exists.intro K (And.intro hr0 (And.intro hK ?_)))
  intro r hr u hu htb
  have hrpos : 0 < r := hr0.trans_le hr
  have ht : 0 <= (r : Real) / u := div_nonneg (Nat.cast_nonneg r) hu.le
  have hA := hLower r hr ((r : Real) / u) ht htb
  change d <= Nat.normalizedDescFactorialPolynomial primeProfileRealCoefficient r
    ((r : Real) / u) at hA
  have hD := hDeriv r hrpos ((r : Real) / u) ht htb
  have he := Nat.abs_deriv_factorialConvolution_ratio_add_le
    primeProfileRealCoefficient r hrpos u b d M hu htb hd hM hA hD.1 hD.2
  change abs (deriv (fun v : Real =>
    Nat.factorialConvolution primeProfileRealCoefficient (r - 1) v /
      Nat.factorialConvolution primeProfileRealCoefficient r v) u +
        (r : Real) / u ^ 2) <= K / u ^ 2 at he
  refine And.intro he ?_
  intro hRank
  have hPayment : K / u ^ 2 <= (r : Real) / (2 * u ^ 2) := by
    calc
      K / u ^ 2 <= ((r : Real) / 2) / u ^ 2 := by
        apply div_le_div_of_nonneg_right
        . linarith
        . exact sq_nonneg u
      _ = (r : Real) / (2 * u ^ 2) := by ring
  have hSigned := abs_le.mp he
  have hScale : (r : Real) / u ^ 2 = 2 * ((r : Real) / (2 * u ^ 2)) := by ring
  have hThree : -(3 * (r : Real)) / (2 * u ^ 2) =
      -(r : Real) / u ^ 2 - (r : Real) / (2 * u ^ 2) := by ring
  constructor
  . rw [hThree, neg_div]
    linarith only [hSigned.1, hPayment]
  . rw [neg_div]
    linarith only [hSigned.2, hPayment, hScale]

end PrimeFactorOscillations


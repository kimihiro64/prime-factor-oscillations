/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.UniformCarrierBounds

/-!
# Uniform Carrier Geometry

Positive denominators and negative reference slopes in a fixed moving-rank band.
-/

set_option autoImplicit false
set_option Elab.async false

noncomputable section
namespace PrimeFactorOscillations.UniformCarrier

theorem exists_finite_reference_geometry (base : PrimeClockLaw)
    (hs : base.scale = 1) (he : base.error = 0)
    (b : Real) (hb : 0 <= b) :
    exists r0 N0 : Nat, exists d M K : Real,
      0 < r0 /\ 1 <= N0 /\ 0 < d /\ 0 <= M /\ 0 <= K /\
      forall r : Nat, r0 <= r -> forall N : Nat, N0 <= N ->
      forall u : Real, 0 < u -> (r : Real) / u <= b ->
        d <= Nat.normalizedDescFactorialPolynomial (prefixCoefficient base N) r ((r : Real) / u) /\
        0 < Nat.factorialConvolution (prefixCoefficient base N) r u /\
        abs (deriv (Nat.normalizedDescFactorialPolynomial (prefixCoefficient base N) r)
          ((r : Real) / u)) <= M /\
        DifferentiableAt Real (prefixRatio base N r) u /\
        abs (deriv (prefixRatio base N r) u + (r : Real) / u ^ 2) <= K / u ^ 2 := by
  choose r0 hr0 hLower using base.exists_profile_normalized_coefficient_lower_bound b hb
  choose C D hC hD hError using base.exists_prefixProfile_real_normalized_errors b hb
  let d := base.positiveLowerBound b / 4
  have hd : 0 < d := by dsimp [d]; exact div_pos (base.positiveLowerBound_pos b) (by norm_num)
  choose NN hNN using exists_nat_gt (C / d + 1)
  let N0 := max 1 NN
  let R := 2 * (b + 1)
  have hR : 0 < R := by dsimp [R]; positivity
  have hE : 0 <= productBound R := Real.exp_nonneg _
  choose M hM hDeriv using normalized_derivative_uniform_bound b hb (productBound R) hE
  let Q := M / d
  let K := 2 * b * Q + b ^ 2 * (Q + Q ^ 2)
  have hQ : 0 <= Q := div_nonneg hM hd.le
  have hK : 0 <= K := by dsimp [K]; positivity
  refine Exists.intro r0 (Exists.intro N0 (Exists.intro d
    (Exists.intro M (Exists.intro K
      (And.intro hr0 (And.intro (le_max_left _ _)
        (And.intro hd (And.intro hM (And.intro hK ?_)))))))))
  intro r hr N hN u hu htb
  have hrpos : 0 < r := hr0.trans_le hr
  have hN1 : 1 <= N := (le_max_left _ _).trans hN
  have hNN : NN <= N := (le_max_right _ _).trans hN
  have hNpos : (0 : Real) < N := by exact_mod_cast Nat.zero_lt_one.trans_le hN1
  have hNNR : (NN : Real) <= N := by exact_mod_cast hNN
  have hNd : C / d < (N : Real) := by linarith
  have hmul := mul_lt_mul_of_pos_right hNd hd
  have hcancel : C / d * d = C := by field_simp
  rw [hcancel] at hmul
  have hsmall : C / (N : Real) <= d := by
    calc
      _ <= (d * N) / N := div_le_div_of_nonneg_right (by linarith : C <= d * N) hNpos.le
      _ = d := by field_simp
  have ht : 0 <= (r : Real) / u := div_nonneg (Nat.cast_nonneg r) hu.le
  have hLow := hLower r hr ((r : Real) / u) ht htb
  change base.positiveLowerBound b / 2 <=
    Nat.normalizedDescFactorialPolynomial base.realCoefficient r ((r : Real) / u) at hLow
  have hErr := (hError N hN1 r hrpos ((r : Real) / u) ht htb).1
  change abs (Nat.normalizedDescFactorialPolynomial (prefixCoefficient base N) r ((r : Real) / u) -
    Nat.normalizedDescFactorialPolynomial base.realCoefficient r ((r : Real) / u)) <= C / N at hErr
  have hA : d <= Nat.normalizedDescFactorialPolynomial (prefixCoefficient base N) r ((r : Real) / u) := by
    have hSigned := (abs_le.mp hErr).1
    dsimp [d] at *
    linarith only [hSigned, hLow, hsmall]
  have hApos := hd.trans_le hA
  have hc (j : Nat) :
      abs (prefixCoefficient base N j) <= productBound R / (2 * (b + 1)) ^ j :=
    canonical_prefix_coefficient_bound base hs he R hR N j
  have hBounds := hDeriv (prefixCoefficient base N) hc r hrpos ((r : Real) / u) ht htb
  refine And.intro hA (And.intro ?_ (And.intro hBounds.1 (And.intro ?_ ?_)))
  . rw [Nat.factorialConvolution_eq_normalizedDescFactorialPolynomial
      (prefixCoefficient base N) r hrpos u hu.ne']
    exact mul_pos (by positivity) hApos
  . exact (Nat.hasDerivAt_factorialConvolution_ratio (prefixCoefficient base N) r
      hrpos u hu.ne' hApos.ne').differentiableAt
  . exact Nat.abs_deriv_factorialConvolution_ratio_add_le
      (prefixCoefficient base N) r hrpos u b d M hu htb hd hM hA hBounds.1 hBounds.2

end PrimeFactorOscillations.UniformCarrier

/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import Mathlib.Analysis.Analytic.OfScalars
import Mathlib.Analysis.Complex.TaylorSeries
import PrimeFactorOscillations.Definitions.PrimeProfileSeries
import PrimeFactorOscillations.Helpers.PrimeProfileCoefficients
import PrimeFactorOscillations.Helpers.PrimeProfilePositive

/-!
# Entire real scalar series of the prime profile

The actual coefficients sum to the real restriction of the prime product.
Their scalar multilinear series has infinite convergence radius.
-/

set_option autoImplicit false
set_option Elab.async false

namespace PrimeFactorOscillations

open BombieriVinogradov.ComplexAnalysis

theorem hasSum_primeProfileRealCoefficient (t : Real) :
    HasSum (fun j : Nat => primeProfileRealCoefficient j * t ^ j)
      (primeProfile (t : Complex)).re := by
  have h := Complex.hasSum_taylorSeries_of_entire differentiable_primeProfile 0 (t : Complex)
  have hc : HasSum (fun j : Nat => taylorCoefficient primeProfile 0 j * (t : Complex) ^ j)
      (primeProfile (t : Complex)) := by
    simpa only [taylorCoefficient, sub_zero, smul_eq_mul, div_eq_mul_inv,
      mul_comm, mul_left_comm, mul_assoc] using h
  simpa only [primeProfileRealCoefficient, <- Complex.ofReal_pow,
    Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]
    using Complex.hasSum_re hc

theorem exists_primeProfileRealCoefficient_bound (R : Real) (hR : 0 < R) :
    exists C : Real, 0 <= C /\ forall j : Nat,
      norm (primeProfileRealCoefficient j) <= C / R ^ j := by
  obtain h := (isCompact_closedBall (0 : Complex) R).exists_bound_of_continuousOn
    differentiable_primeProfile.continuous.continuousOn
  choose C hC using h
  have hC0 : 0 <= C := (norm_nonneg (primeProfile 0)).trans
    (hC 0 (by simpa only [Metric.mem_closedBall, dist_self] using hR.le))
  refine Exists.intro C (And.intro hC0 ?_)
  intro j
  calc
    norm (primeProfileRealCoefficient j) <= norm (taylorCoefficient primeProfile 0 j) :=
      Complex.abs_re_le_norm _
    _ <= C / R ^ j := norm_taylorCoefficient_le j hR differentiable_primeProfile
      (fun z hz => hC z (Metric.sphere_subset_closedBall hz))

theorem summable_primeProfileRealCoefficient_norm_mul_pow (r : NNReal) :
    Summable (fun j : Nat => norm (primeProfileRealCoefficient j) * (r : Real) ^ j) := by
  let R : Real := (r : Real) + 1
  have hR : 0 < R := by dsimp [R]; positivity
  obtain h := exists_primeProfileRealCoefficient_bound R hR
  choose C hC using h
  have hq0 : 0 <= (r : Real) / R := div_nonneg r.coe_nonneg hR.le
  have hq1 : (r : Real) / R < 1 := (div_lt_one hR).mpr (by dsimp [R]; linarith)
  have hg := (summable_geometric_of_lt_one hq0 hq1).mul_left C
  apply Summable.of_nonneg_of_le (fun j => by positivity) _ hg
  intro j
  calc
    norm (primeProfileRealCoefficient j) * (r : Real) ^ j <=
        (C / R ^ j) * (r : Real) ^ j :=
      mul_le_mul_of_nonneg_right (hC.2 j) (pow_nonneg r.coe_nonneg j)
    _ = C * ((r : Real) / R) ^ j := by rw [div_pow]; ring

theorem primeProfileRealCoefficient_radius_eq_top :
    (FormalMultilinearSeries.ofScalars Real primeProfileRealCoefficient).radius =
      (Top.top : ENNReal) := by
  apply FormalMultilinearSeries.radius_eq_top_of_summable_norm
  intro r
  simpa only [FormalMultilinearSeries.ofScalars_norm] using
    summable_primeProfileRealCoefficient_norm_mul_pow r

end PrimeFactorOscillations


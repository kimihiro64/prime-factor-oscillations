/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Definitions.PrimeCyclePrefix
import PrimeFactorOscillations.Helpers.PrimeProfileApproximationTransfer
import PrimeFactorOscillations.Helpers.PrimeProfileBoundaryMultiplier
import PrimeFactorOscillations.Helpers.PrimeProfileReferenceInvariance

/-!
# Uniform analytic and coefficient estimates for ordered prime cycles

The one-boundary identity gives the full normalized prefix estimate. Cauchy's
estimate controls all Taylor coefficients. The general coefficient transfer
then preserves the inverse-rank saving, without a pointwise law hypothesis
for the reindexed weights.
-/

set_option autoImplicit false
set_option Elab.async false

namespace PrimeFactorOscillations.PrimeCyclePrefix

open BombieriVinogradov.ComplexAnalysis

/-- Ordered-cycle prefixes approach the canonical entire profile at rate `1/N`
on each fixed disc. The initial cutoff may depend on its radius. -/
theorem exists_complexPrefix_uniform_error (f : PrimeCyclePrefix)
    (R : Real) (hR : 0 <= R) :
    exists N0 : Nat, exists C : Real, 1 <= N0 /\ 0 <= C /\
      forall N : Nat, N0 <= N -> forall z : Complex, norm z <= R ->
        norm (f.complexPrefix N z - canonicalPrimeOddsLaw.complexProfile z) <=
          C / (N : Real) := by
  have hprofile : canonicalPrimeOddsLaw.complexProfile = primeProfile := by
    funext z
    simp only [QuadraticPrimeLaw.complexProfile, QuadraticPrimeLaw.complexFactor,
      canonicalPrimeOddsLaw, one_mul, primeProfile, Complex.normalizedLinearFactor]
  have hprefix : forall N : Nat,
      canonicalPrimeOddsLaw.complexPrefix N = primePrefixProfile N := by
    intro N
    funext z
    simp only [QuadraticPrimeLaw.complexPrefix, QuadraticPrimeLaw.complexFactor,
      canonicalPrimeOddsLaw, one_mul, primePrefixProfile, Complex.normalizedLinearFactor]
  obtain he := canonicalPrimeOddsLaw.exists_complexPrefix_uniform_error R hR
  choose C0 hC0 herr using he
  obtain hcompact := (isCompact_closedBall (0 : Complex) R).exists_bound_of_continuousOn
    canonicalPrimeOddsLaw.differentiable_complexProfile.continuous.continuousOn
  choose P hP using hcompact
  have hP0 : 0 <= P := (norm_nonneg (canonicalPrimeOddsLaw.complexProfile 0)).trans
    (hP 0 (by simpa only [Metric.mem_closedBall, dist_self] using hR))
  let B := P + C0
  have hB : 0 <= B := add_nonneg hP0 hC0
  choose n0 hn0 using exists_nat_gt (8 * R)
  refine Exists.intro (n0 + 1) (Exists.intro (C0 + 8 * R * B)
    (And.intro (Nat.succ_le_succ (Nat.zero_le n0))
      (And.intro (by positivity) ?_)))
  intro N hN z hz
  have hN1 : 1 <= N := (Nat.succ_le_succ (Nat.zero_le n0)).trans hN
  have hNpos : 0 < N := hN1
  have hNR1 : (1 : Real) <= (N : Real) := by exact_mod_cast hN1
  have hNR : 8 * R <= (N : Real) := by
    have hcast : (n0 : Real) < (N : Real) := by
      exact_mod_cast (Nat.lt_succ_self n0).trans_le hN
    linarith
  have hzball : Membership.mem (Metric.closedBall (0 : Complex) R) z := by
    simpa only [Metric.mem_closedBall, dist_zero_right] using hz
  have hbase := herr N hN1 z hzball
  rw [hprefix N] at hbase
  have hbound : norm (primePrefixProfile N z) <= B := by
    have ht := norm_le_norm_sub_add (canonicalPrimeOddsLaw.complexPrefix N z)
      (canonicalPrimeOddsLaw.complexProfile z)
    have hsmall : C0 / (N : Real) <= C0 := div_le_self hC0 hNR1
    rw [hprefix N] at ht
    exact ht.trans ((add_le_add hbase (hP z hzball)).trans (by dsimp [B]; linarith))
  rw [hprofile] at hbase
  rw [hprofile]
  rcases f.boundary_factor N hN1 with hsame | hcycle
  { rw [hsame]
    exact hbase.trans (div_le_div_of_nonneg_right (by nlinarith) (Nat.cast_nonneg N)) }
  { choose p q hp hq hpN hNq hNp hcross using hcycle
    have hpqle : p <= q := hpN.trans (Nat.le_of_lt hNq)
    have hdenlower := (primeProfileBoundaryMultiplier_error p q N hp hpqle
      hNpos hNp R hR hNR z hz).1
    have hden : Not (1 + (primeProfileWeight p : Complex) * z = 0) :=
      norm_pos_iff.mp (lt_of_lt_of_le (by norm_num) hdenlower)
    have hid := congrArg (fun t : Complex =>
      t / (1 + (primeProfileWeight p : Complex) * z)) (hcross z)
    rw [mul_div_assoc, div_self hden, mul_one] at hid
    have hmul : f.complexPrefix N z =
        primePrefixProfile N z * primeProfileBoundaryMultiplier p q z := by
      simpa only [primeProfileBoundaryMultiplier, mul_div_assoc] using hid
    rw [hmul]
    exact primeProfileBoundaryMultiplier_prefix_error p q N hp hpqle hNpos hNp
      R hR hNR B C0 hB z hz hbound hbase }

/-- The same eventual cutoff controls every Taylor coefficient with geometric
radius decay; the prefixes need only satisfy the exact boundary identity. -/
theorem exists_prefixProfile_taylor_error (f : PrimeCyclePrefix)
    (R : Real) (hR : 0 < R) :
    exists N0 : Nat, exists C : Real, 1 <= N0 /\ 0 <= C /\
      forall N : Nat, N0 <= N -> forall j : Nat,
        norm (taylorCoefficient (f.complexPrefix N) 0 j -
          taylorCoefficient canonicalPrimeOddsLaw.complexProfile 0 j) <=
            C / ((N : Real) * R ^ j) := by
  obtain he := f.exists_complexPrefix_uniform_error R hR.le
  choose N0 C hN0 hC hbound using he
  refine Exists.intro N0 (Exists.intro C (And.intro hN0 (And.intro hC ?_)))
  intro N hN j
  have hf : Differentiable Complex
      (fun z => f.complexPrefix N z - canonicalPrimeOddsLaw.complexProfile z) :=
    (f.differentiable_complexPrefix N).sub canonicalPrimeOddsLaw.differentiable_complexProfile
  have hc := norm_taylorCoefficient_le j hR hf (by
    intro z hz
    apply hbound N hN z
    have hzball : Membership.mem (Metric.closedBall (0 : Complex) R) z :=
      Metric.sphere_subset_closedBall hz
    simpa only [Metric.mem_closedBall, dist_zero_right] using hzball)
  have hid : iteratedDeriv j
      (fun z => f.complexPrefix N z - canonicalPrimeOddsLaw.complexProfile z) 0 =
        iteratedDeriv j (f.complexPrefix N) 0 -
          iteratedDeriv j canonicalPrimeOddsLaw.complexProfile 0 :=
    iteratedDeriv_fun_sub (f.differentiable_complexPrefix N).contDiff.contDiffAt
      canonicalPrimeOddsLaw.differentiable_complexProfile.contDiff.contDiffAt
  simpa only [taylorCoefficient, hid, sub_div, div_div] using hc

/-- The full coefficient-ratio error retains its inverse-rank factor for
ordered-cycle prefixes, even when their additive displacements are unbounded. -/
theorem exists_factorialConvolution_ratio_error (f : PrimeCyclePrefix)
    (b : Real) (hb : 0 <= b) :
    exists r0 N0 : Nat, exists K : Real,
      0 < r0 /\ 1 <= N0 /\ 0 <= K /\
      forall r : Nat, r0 <= r -> forall N : Nat, N0 <= N ->
      forall u : Real, 0 < u -> (r : Real) / u <= b ->
        0 < Nat.factorialConvolution
          (fun j => (taylorCoefficient (f.complexPrefix N) 0 j).re) r u /\
        0 < Nat.factorialConvolution canonicalPrimeOddsLaw.realCoefficient r u /\
        abs (Nat.factorialConvolution
            (fun j => (taylorCoefficient (f.complexPrefix N) 0 j).re) (r - 1) u /
          Nat.factorialConvolution
            (fun j => (taylorCoefficient (f.complexPrefix N) 0 j).re) r u -
          Nat.factorialConvolution canonicalPrimeOddsLaw.realCoefficient (r - 1) u /
            Nat.factorialConvolution canonicalPrimeOddsLaw.realCoefficient r u) <=
          K / ((r : Real) * (N : Real)) := by
  have hR : 0 < b + 1 := by linarith
  obtain he := f.exists_prefixProfile_taylor_error (b + 1) hR
  choose Nmin A hNmin hA hTaylor using he
  exact canonicalPrimeOddsLaw.exists_approximatingProfile_factorialConvolution_ratio_error
    f.complexPrefix Nmin b hb A hA hTaylor

end PrimeFactorOscillations.PrimeCyclePrefix

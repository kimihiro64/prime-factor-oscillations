/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import PrimeFactorOscillations.Helpers.PrimeClassSamplingPartial

/-!
# The infinite coefficient limit and its actual sampling error

Uniformity in the independent prime cutoff makes the reference coefficients
Cauchy. Passing each finite coefficient sum to this limit preserves the
complete arithmetic budget. Summability then gives the full infinite
coefficient L1 estimate for the literal integer samples.
-/

set_option autoImplicit false
set_option Elab.async false

namespace PrimeFactorOscillations.PrimeClassSampling

open Filter
open PrimeFactorOscillations.PrimeClassDecoder

theorem exists_commonReference_limit
    (a b error : Nat -> Real)
    (herror : Tendsto error atTop (nhds 0))
    (hbound : forall N, 0 < N -> forall Y, N <= Y ->
      abs (a N - b Y) <= error N) :
    exists beta : Real, And (Tendsto b atTop (nhds beta))
      (forall N, 0 < N -> abs (a N - beta) <= error N) := by
  have hcauchy : CauchySeq b := by
    apply Metric.cauchySeq_iff.mpr
    intro epsilon hepsilon
    have hsmall : Filter.Eventually (fun N => error N < epsilon / 2) atTop :=
      herror.eventually (eventually_lt_nhds (half_pos hepsilon))
    choose N hN using ((eventually_ge_atTop 1).and hsmall).exists
    refine Exists.intro N ?_
    intro M hM Y hY
    have hMN := hbound N (by omega) M hM
    have hYN := hbound N (by omega) Y hY
    rw [Real.dist_eq]
    have htriangle := abs_sub_le (b M) (a N) (b Y)
    rw [abs_sub_comm (b M) (a N)] at htriangle
    linarith only [htriangle, hMN, hYN, hN.2]
  choose beta hbeta using cauchySeq_tendsto_of_complete hcauchy
  refine Exists.intro beta (And.intro hbeta ?_)
  intro N hN
  apply le_of_tendsto ((tendsto_const_nhds.sub hbeta).abs)
  filter_upwards [eventually_ge_atTop N] with Y hY
  exact hbound N hN Y hY

noncomputable def limitingCoefficient (P : Set Nat) (k : Nat) : Real :=
  Filter.limUnder atTop (fun Y : Nat =>
    (finiteReferencePolynomial (primeClassPrefix P Y)).coeff k)

theorem samplingBudget_tendsto_zero
    (P : Set Nat) (sigma : Real) (hs1 : sigma < 1) :
    Tendsto (fun N : Nat =>
      (N : Real) ^ (sigma - 1) * Real.exp (2 * tsum (classPowerWeight P sigma)))
      atTop (nhds 0) := by
  have hpow := (tendsto_rpow_neg_atTop (by linarith : 0 < 1 - sigma)).comp
    (tendsto_natCast_atTop_atTop (R := Real))
  have heq : -(1 - sigma) = sigma - 1 := by ring
  simpa only [Function.comp_apply, heq, zero_mul] using
    hpow.mul_const (Real.exp (2 * tsum (classPowerWeight P sigma)))

theorem finiteReference_coefficient_tendsto
    (P : Set Nat) (sigma : Real) (hs0 : 0 <= sigma) (hs1 : sigma < 1)
    (hsum : Summable (classPowerWeight P sigma)) (k : Nat) :
    Tendsto (fun Y : Nat =>
      (finiteReferencePolynomial (primeClassPrefix P Y)).coeff k)
      atTop (nhds (limitingCoefficient P k)) := by
  have hexists := exists_commonReference_limit
    (fun N => (sampleCount P N k : Real) / (N : Real))
    (fun Y => (finiteReferencePolynomial (primeClassPrefix P Y)).coeff k)
    (fun N => (N : Real) ^ (sigma - 1) *
      Real.exp (2 * tsum (classPowerWeight P sigma)))
    (samplingBudget_tendsto_zero P sigma hs1)
    (fun N hN Y hNY => actualSample_single_coefficient_error_le_exp
      P N Y k hNY hN sigma hs0 hs1.le hsum)
  choose beta hbeta using hexists
  have heq : limitingCoefficient P k = beta := hbeta.1.limUnder_eq
  rw [heq]
  exact hbeta.1

theorem actualSample_limiting_partial_error_le
    (P : Set Nat) (N K : Nat) (hN : 0 < N)
    (sigma : Real) (hs0 : 0 <= sigma) (hs1 : sigma < 1)
    (hsum : Summable (classPowerWeight P sigma)) :
    (Finset.range K).sum (fun k =>
      abs ((sampleCount P N k : Real) / (N : Real) - limitingCoefficient P k)) <=
      (N : Real) ^ (sigma - 1) * Real.exp (2 * tsum (classPowerWeight P sigma)) := by
  have hlimit : Tendsto (fun Y : Nat => (Finset.range K).sum (fun k =>
      abs ((sampleCount P N k : Real) / (N : Real) -
        (finiteReferencePolynomial (primeClassPrefix P Y)).coeff k))) atTop
      (nhds ((Finset.range K).sum (fun k =>
        abs ((sampleCount P N k : Real) / (N : Real) - limitingCoefficient P k)))) := by
    apply tendsto_finsetSum (Finset.range K)
    intro k hk
    exact (tendsto_const_nhds.sub
      (finiteReference_coefficient_tendsto P sigma hs0 hs1 hsum k)).abs
  apply le_of_tendsto hlimit
  filter_upwards [eventually_ge_atTop N] with Y hY
  exact actualSample_partial_coefficient_error_le_exp
    P N Y K hY hN sigma hs0 hs1.le hsum

theorem actualSample_limiting_error_summable
    (P : Set Nat) (N : Nat) (hN : 0 < N)
    (sigma : Real) (hs0 : 0 <= sigma) (hs1 : sigma < 1)
    (hsum : Summable (classPowerWeight P sigma)) :
    Summable (fun k =>
      abs ((sampleCount P N k : Real) / (N : Real) - limitingCoefficient P k)) := by
  apply summable_of_sum_range_le (fun k => abs_nonneg _)
  intro K
  exact actualSample_limiting_partial_error_le P N K hN sigma hs0 hs1 hsum

theorem actualSample_limiting_coefficient_l1_error_le
    (P : Set Nat) (N : Nat) (hN : 0 < N)
    (sigma : Real) (hs0 : 0 <= sigma) (hs1 : sigma < 1)
    (hsum : Summable (classPowerWeight P sigma)) :
    tsum (fun k =>
      abs ((sampleCount P N k : Real) / (N : Real) - limitingCoefficient P k)) <=
      (N : Real) ^ (sigma - 1) * Real.exp (2 * tsum (classPowerWeight P sigma)) := by
  apply (actualSample_limiting_error_summable P N hN sigma hs0 hs1 hsum).tsum_le_of_sum_range_le
  intro K
  exact actualSample_limiting_partial_error_le P N K hN sigma hs0 hs1 hsum

end PrimeFactorOscillations.PrimeClassSampling

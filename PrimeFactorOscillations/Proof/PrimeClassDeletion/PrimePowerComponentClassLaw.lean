/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Proof.PrimeClassDeletion.PrimePowerComponentClassArithmetic

/-!
# The complete infinite-class prime-power sampling law

The prime cutoff tends to infinity at fixed sample size N. Every finite
atom subsum has its exact limit, so its uniform complete Euler bound passes
to the whole l1 series. The reference and the sample both have mass one.
-/

set_option autoImplicit false
set_option Elab.async false

namespace PrimeFactorOscillations.PrimeClassSampling

open Filter

theorem classPrimePowerComponent_error_finite_sum_le
    (P : Set Nat) (t : Finset Nat) (N : Nat) (hN : 0 < N)
    (sigma : Real) (hs : 0 < sigma) (hs1 : sigma <= 1)
    (hsum : Summable (classPowerWeight P sigma)) :
    t.sum (fun a => abs (classPrimePowerComponentProbability P N a -
      classPrimePowerReference P a)) <=
      (N : Real) ^ (sigma - 1) * classPrimePowerErrorConstant P sigma := by
  classical
  have hsum1 := classPowerWeight_one_summable P sigma hs1 hsum
  have hleft : Tendsto (fun Y : Nat => t.sum (fun a => abs
      (literalPrimePowerComponentProbability (primeClassPrefix P Y) N a -
        finitePrimePowerReference (primeClassPrefix P Y) a))) atTop
      (nhds (t.sum (fun a => abs (classPrimePowerComponentProbability P N a -
        classPrimePowerReference P a)))) := by
    induction t using Finset.induction_on with
    | empty =>
        simpa only [Finset.sum_empty] using
          (tendsto_const_nhds : Tendsto (fun _ : Nat => (0 : Real)) atTop (nhds 0))
    | @insert a t ha ih =>
        simpa only [Finset.sum_insert ha] using
          (((literalPrimePowerComponentProbability_prefix_tendsto P N a).sub
            (finitePrimePowerReference_prefix_tendsto P hsum1 a)).abs).add ih
  have hright : Tendsto (fun Y : Nat =>
      (N : Real) ^ (sigma - 1) *
        (primeClassPrefix P Y).prod (fun p =>
          (1 + (p : Real) ^ (-sigma)) / (1 - (p : Real) ^ (-sigma))))
      atTop (nhds ((N : Real) ^ (sigma - 1) * classPrimePowerErrorConstant P sigma)) :=
    tendsto_const_nhds.mul (primePowerErrorEulerPrefix_tendsto P sigma hs hsum)
  apply le_of_tendsto_of_tendsto hleft hright
  apply Filter.Eventually.of_forall
  intro Y
  have herror := literalPrimePowerComponentProbability_full_l1_error
    (primeClassPrefix P Y) (primeClassPrefix_prime P Y) N hN sigma hs hs1
  apply le_trans _ herror.2
  exact Summable.sum_le_tsum t (fun a ha => abs_nonneg _) herror.1

theorem classPrimePowerComponent_full_l1_error
    (P : Set Nat) (N : Nat) (hN : 0 < N)
    (sigma : Real) (hs : 0 < sigma) (hs1 : sigma <= 1)
    (hsum : Summable (classPowerWeight P sigma)) :
    And (Summable (fun a => abs (classPrimePowerComponentProbability P N a -
      classPrimePowerReference P a)))
      (tsum (fun a => abs (classPrimePowerComponentProbability P N a -
        classPrimePowerReference P a)) <=
        (N : Real) ^ (sigma - 1) * classPrimePowerErrorConstant P sigma) := by
  have hfinite (t : Finset Nat) :=
    classPrimePowerComponent_error_finite_sum_le P t N hN sigma hs hs1 hsum
  have hsumerror : Summable (fun a => abs
      (classPrimePowerComponentProbability P N a - classPrimePowerReference P a)) := by
    apply summable_of_sum_le
    case hf => exact fun a => abs_nonneg _
    case h => exact hfinite
  refine And.intro hsumerror ?_
  apply Real.tsum_le_of_sum_le
  case hf => exact fun a => abs_nonneg _
  case h => exact hfinite

theorem classPrimePowerComponent_totalVariation_le
    (P : Set Nat) (N : Nat) (hN : 0 < N)
    (sigma : Real) (hs : 0 < sigma) (hs1 : sigma <= 1)
    (hsum : Summable (classPowerWeight P sigma)) :
    tsum (fun a => abs (classPrimePowerComponentProbability P N a -
      classPrimePowerReference P a)) / 2 <=
      min 1 ((N : Real) ^ (sigma - 1) * classPrimePowerErrorConstant P sigma / 2) := by
  have hsum1 := classPowerWeight_one_summable P sigma hs1 hsum
  have hsample := classPrimePowerComponentProbability_hasSum_one P N hN
  have href := classPrimePowerReference_hasSum_one P hsum1
  have herror := classPrimePowerComponent_full_l1_error P N hN sigma hs hs1 hsum
  have hpoint (a : Nat) : abs
      (classPrimePowerComponentProbability P N a - classPrimePowerReference P a) <=
        classPrimePowerComponentProbability P N a + classPrimePowerReference P a := by
    have ha := classPrimePowerComponentProbability_nonneg P N a
    have hb := classPrimePowerReference_nonneg P hsum1 a
    apply abs_le.mpr
    constructor <;> linarith
  have htwo : tsum (fun a => abs
      (classPrimePowerComponentProbability P N a - classPrimePowerReference P a)) <= 2 := by
    calc
      _ <= tsum (fun a => classPrimePowerComponentProbability P N a +
          classPrimePowerReference P a) :=
        Summable.tsum_le_tsum hpoint herror.1 (hsample.summable.add href.summable)
      _ = 2 := by
        rw [hsample.summable.tsum_add href.summable, hsample.tsum_eq, href.tsum_eq]
        norm_num
  exact le_min (by linarith) (by linarith [herror.2])

end PrimeFactorOscillations.PrimeClassSampling

/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.PrimeClassSamplingTaylor

/-!
# Complete actual sampling law for the entire prime-class count profile

The coefficients belong to the actual entire Euler product. They form a
probability distribution, and the full integer sample has the proved
infinite coefficient L1 error. All hypotheses concern the literal prime
class and its power sum; no law or sampling estimate is assumed.
-/

set_option autoImplicit false
set_option Elab.async false

namespace PrimeFactorOscillations.PrimeClassSampling

open PrimeFactorOscillations.PrimeClassDecoder
open BombieriVinogradov.ComplexAnalysis

noncomputable def classProfileMass (P : Set Nat) (k : Nat) : Real :=
  (taylorCoefficient (classEulerProfile P) 0 k).re

theorem classProfileMass_eq_limitingCoefficient
    (P : Set Nat) (sigma : Real) (hs0 : 0 <= sigma) (hs1 : sigma < 1)
    (hsum : Summable (classPowerWeight P sigma)) :
    classProfileMass P = limitingCoefficient P := by
  funext k
  unfold classProfileMass
  rw [classEulerProfile_taylor_eq_limitingCoefficient P sigma hs0 hs1 hsum k]
  rfl

theorem classEulerProfile_count_sampling_law
    (P : Set Nat) (sigma : Real) (hs0 : 0 <= sigma) (hs1 : sigma < 1)
    (hsum : Summable (classPowerWeight P sigma)) :
    And (Differentiable Complex (classEulerProfile P))
      (And (forall k : Nat, 0 <= classProfileMass P k)
        (And (HasSum (classProfileMass P) 1)
          (forall N : Nat, 0 < N ->
            And (Summable (fun k =>
                abs ((sampleCount P N k : Real) / (N : Real) - classProfileMass P k)))
              (tsum (fun k =>
                abs ((sampleCount P N k : Real) / (N : Real) - classProfileMass P k)) <=
                (N : Real) ^ (sigma - 1) *
                  Real.exp (2 * tsum (classPowerWeight P sigma)))))) := by
  rw [classProfileMass_eq_limitingCoefficient P sigma hs0 hs1 hsum]
  refine And.intro
    (differentiable_classEulerProfile P
      (classPowerWeight_one_summable P sigma hs1.le hsum))
    (And.intro (limitingCoefficient_nonneg P sigma hs0 hs1 hsum)
      (And.intro (limitingCoefficient_hasSum_one P sigma hs0 hs1 hsum) ?_))
  intro N hN
  exact And.intro (actualSample_limiting_error_summable P N hN sigma hs0 hs1 hsum)
    (actualSample_limiting_coefficient_l1_error_le P N hN sigma hs0 hs1 hsum)

end PrimeFactorOscillations.PrimeClassSampling

/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import BombieriVinogradov.Helpers.ComplexAnalysis.CauchyTaylor
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import PrimeFactorOscillations.Helpers.QuadraticProfileTail

/-!
# Taylor approximation of the prime profile

The uniform prime-product tail and the cached Bombieri--Vinogradov Cauchy
estimate control every Taylor coefficient with one constant for each radius.
-/

set_option autoImplicit false
set_option Elab.async false

namespace PrimeFactorOscillations.QuadraticPrimeLaw

open BombieriVinogradov.ComplexAnalysis

theorem exists_prefixProfile_taylor_error (law : QuadraticPrimeLaw) (R : Real) (hR : 0 < R) :
    exists C : Real, 0 <= C /\ forall N : Nat, 1 <= N -> forall j : Nat,
      norm (taylorCoefficient (law.complexPrefix N) 0 j -
        taylorCoefficient law.complexProfile 0 j) <= C / ((N : Real) * R ^ j) := by
  obtain h := law.exists_complexPrefix_uniform_error R hR.le
  choose C hC using h
  refine Exists.intro C (And.intro hC.1 ?_)
  intro N hN j
  have hf : Differentiable Complex (fun z => law.complexPrefix N z - law.complexProfile z) :=
    (law.differentiable_complexPrefix N).sub law.differentiable_complexProfile
  have hbound := norm_taylorCoefficient_le j hR hf (by
    intro z hz
    exact hC.2 N hN z (Metric.sphere_subset_closedBall hz))
  have hid : iteratedDeriv j (fun z => law.complexPrefix N z - law.complexProfile z) 0 =
      iteratedDeriv j (law.complexPrefix N) 0 - iteratedDeriv j law.complexProfile 0 :=
    iteratedDeriv_fun_sub (law.differentiable_complexPrefix N).contDiff.contDiffAt
      law.differentiable_complexProfile.contDiff.contDiffAt
  simpa only [taylorCoefficient, hid, sub_div, div_div] using hbound

end PrimeFactorOscillations.QuadraticPrimeLaw

/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/

import Mathlib.Analysis.Fourier.PoissonSummation
import PrimeFactorOscillations.Assembly.DetectorPackets.IntegerQuadraticInitial

/-!
# IntegerQuadraticPoisson

Maintained extraction of completed detector/packet proof components.
All original theorem hypotheses and retained proof bodies are preserved.
This module alone asserts no improved zero-free boundary.
-/

set_option autoImplicit false
set_option Elab.async false

/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/

/-!
# Character-weighted Poisson summation

This is the periodized form of quadratic Poisson summation at an arbitrary
odd squarefree modulus greater than one. The raw Gauss factor is retained.
Both the shifted Poisson identity and the exchange of the finite character
sum with the convergent Fourier series are proved with their full domains.
-/


noncomputable section
namespace PrimeFactorOscillations.IntegerQuadraticPoisson

open IntegerQuadraticCharacter IntegerQuadraticSquarefree IntegerQuadraticInitial
open BombieriVinogradov.LargeSieve
open scoped BigOperators

noncomputable local instance unitFintype (q : Nat) : Fintype (Units (ZMod q)) :=
  Fintype.ofFinite _

theorem schwartz_int_summable (f : SchwartzMap Real Complex) :
    Summable (fun h : Int => f (h : Real)) := by
  exact @summable_of_isBigO Int Complex
    Complex.instNormedAddCommGroup.toSeminormedAddCommGroup inferInstance
    (fun h : Int => f (h : Real)) (fun h : Int => abs (h : Real) ^ (-2 : Real))
    (Real.summable_abs_int_rpow (by norm_num : (1 : Real) < 2))
    (by simpa only [Real.norm_eq_abs, Function.comp_def] using
      (f.isBigO_cocompact_rpow (-2)).comp_tendsto Int.tendsto_coe_cofinite)

theorem fourier_unit_fraction (q : Nat) [NeZero q]
    (k : Units (ZMod q)) (h : Int) :
    (fourier h) (((unitFraction k : Real) : AddCircle (1 : Real))) =
      ZMod.stdAddChar ((h : ZMod q) * (k : ZMod q)) := by
  calc
    _ = additivePhase ((h : Real) * (unitFraction k : Real)) := by
      rw [fourier_coe_apply, additivePhase, circleMap_zero]
      push_cast
      congr 1
      ring
    _ = _ := additivePhase_int_unitFraction h k

theorem weighted_periodization (q : Nat) [NeZero q] (hq : Good q)
    (f : SchwartzMap Real Complex) :
    Finset.sum Finset.univ (fun k : Units (ZMod q) =>
      character q hq.1 (k : ZMod q) *
        tsum (fun m : Int => f ((unitFraction k : Real) + (m : Real)))) =
      gaussSum (character q hq.1) ZMod.stdAddChar *
        tsum (fun h : Int => character q hq.1 (h : ZMod q) *
          (FourierTransform.fourier f) (h : Real)) := by
  classical
  let g : SchwartzMap Real Complex := FourierTransform.fourier f
  have hg := (summable_norm_iff.mpr (schwartz_int_summable g))
  have hterm (k : Units (ZMod q)) :
      Summable (fun h : Int => character q hq.1 (k : ZMod q) *
        (g (h : Real) * (fourier h)
          (((unitFraction k : Real) : AddCircle (1 : Real))))) := by
    apply hg.of_norm_bounded
    intro h
    rw [norm_mul, norm_mul]
    have hp : norm ((fourier h)
        (((unitFraction k : Real) : AddCircle (1 : Real)))) = 1 := by
      simp only [fourier_apply, Circle.norm_coe]
    rw [hp, mul_one]
    exact mul_le_of_le_one_left (norm_nonneg _)
      ((character q hq.1).norm_le_one (k : ZMod q))
  calc
    _ = Finset.sum Finset.univ (fun k : Units (ZMod q) =>
        character q hq.1 (k : ZMod q) *
          tsum (fun h : Int => g (h : Real) * (fourier h)
            (((unitFraction k : Real) : AddCircle (1 : Real))))) := by
      apply Finset.sum_congr rfl
      intro k hk
      rw [f.tsum_eq_tsum_fourier]
    _ = Finset.sum Finset.univ (fun k : Units (ZMod q) =>
        tsum (fun h : Int => character q hq.1 (k : ZMod q) *
          (g (h : Real) * (fourier h)
            (((unitFraction k : Real) : AddCircle (1 : Real)))))) := by
      apply Finset.sum_congr rfl
      intro k hk
      rw [tsum_mul_left]
    _ = tsum (fun h : Int => Finset.sum Finset.univ (fun k : Units (ZMod q) =>
        character q hq.1 (k : ZMod q) *
          (g (h : Real) * (fourier h)
            (((unitFraction k : Real) : AddCircle (1 : Real)))))) := by
      exact (Summable.tsum_finsetSum (fun k hk => hterm k)).symm
    _ = tsum (fun h : Int => g (h : Real) *
        gaussSum (character q hq.1) (ZMod.stdAddChar.mulShift (h : ZMod q))) := by
      apply tsum_congr
      intro h
      simp only [gaussSum, AddChar.mulShift_apply]
      rw [<- sum_units_eq_sum_residues (character q hq.1)
        (fun x : ZMod q => ZMod.stdAddChar ((h : ZMod q) * x))]
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro k hk
      rw [fourier_unit_fraction]
      ring
    _ = tsum (fun h : Int =>
        gaussSum (character q hq.1) ZMod.stdAddChar *
          (character q hq.1 (h : ZMod q) * g (h : Real))) := by
      apply tsum_congr
      intro h
      rw [squarefree_fourier_factor q hq.1 hq.2.1 hq.2.2]
      ring
    _ = _ := tsum_mul_left

end PrimeFactorOscillations.IntegerQuadraticPoisson


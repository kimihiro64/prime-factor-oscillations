/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.PrimeProfileGenerating
import PrimeFactorOscillations.Mathlib.Analysis.Calculus.IteratedDeriv.LinearProduct
import PrimeFactorUnimodality.Helpers.FirstDifference.PrimeSequence
import PrimeFactorUnimodality.Helpers.SymmetricBounds.Ratio

/-!
# Canonical Erdos 690 coefficient identification

The inclusive prime prefix is exactly the dependency's strict prefix at N+1.
Its existing rational symmetric coefficients and density ratio coincide with
the actual real factorial convolution, including zero denominators as total division.
-/

set_option autoImplicit false
set_option Elab.async false

namespace PrimeFactorOscillations

open BombieriVinogradov.ComplexAnalysis

theorem primePrefixProfile_weight_multiset (N : Nat) :
    (primeProfilePrefixSet N).val.map
      (fun p : Nat.Primes => (primeProfileWeight (p : Nat) : Complex)) =
      (((PrimeFactorUnimodality.primesBelow (N + 1)).map
        PrimeFactorUnimodality.primeWeight : List Rat) : Multiset Rat).map
          (Rat.castHom Complex) := by
  let w : Nat -> Complex := fun p => 1 / ((p - 1 : Nat) : Complex)
  have hsub := congrArg (fun s : Finset Nat => s.val.map w)
    (Finset.subtype_map Nat.Prime (s := Finset.range (N + 1)))
  simp only [Finset.map_val, Multiset.map_map, Function.comp_def,
    Function.Embedding.subtype_apply, w] at hsub
  simp only [primeProfilePrefixSet, primeProfileWeight,
    PrimeFactorUnimodality.primesBelow, PrimeFactorUnimodality.primeWeight,
    <- Multiset.map_coe, Finset.sort_eq, Multiset.map_map, Function.comp_def,
    Rat.coe_castHom, Rat.cast_div, Rat.cast_one,
    Rat.cast_natCast, Complex.ofReal_div, Complex.ofReal_one, Complex.ofReal_natCast]
  convert hsub using 1
  rfl

theorem primePrefixProfile_factorialConvolution_eq_weightEsymm (N r : Nat) :
    Nat.factorialConvolution
      (fun j => (taylorCoefficient (primePrefixProfile N) 0 j).re) r
      ((primeProfilePrefixSet N).sum
        (fun p => Real.log (1 + primeProfileWeight (p : Nat)))) =
      (PrimeFactorUnimodality.weightEsymm
        (PrimeFactorUnimodality.primesBelow (N + 1)) r : Real) := by
  rw [primePrefixProfile_factorialConvolution_eq_product_coefficient]
  unfold taylorCoefficient
  rw [Finset.normalized_iteratedDeriv_prod_linear_zero,
    primePrefixProfile_weight_multiset, <- RingHom.map_multiset_esymm]
  simp only [Rat.coe_castHom, Complex.ratCast_re, PrimeFactorUnimodality.weightEsymm]

theorem densityRatio_eq_primePrefixProfile_factorialConvolution (N r : Nat) :
    (PrimeFactorUnimodality.densityRatio
      (PrimeFactorUnimodality.primesBelow (N + 1)) r : Real) =
      Nat.factorialConvolution
        (fun j => (taylorCoefficient (primePrefixProfile N) 0 j).re) (r - 1)
        ((primeProfilePrefixSet N).sum
          (fun p => Real.log (1 + primeProfileWeight (p : Nat)))) /
      Nat.factorialConvolution
        (fun j => (taylorCoefficient (primePrefixProfile N) 0 j).re) r
        ((primeProfilePrefixSet N).sum
          (fun p => Real.log (1 + primeProfileWeight (p : Nat)))) := by
  rw [PrimeFactorUnimodality.densityRatio_eq_weightEsymm_ratio
    _ (PrimeFactorUnimodality.primesBelow_gt_one (N + 1)) r, Rat.cast_div,
    primePrefixProfile_factorialConvolution_eq_weightEsymm,
    primePrefixProfile_factorialConvolution_eq_weightEsymm]

end PrimeFactorOscillations


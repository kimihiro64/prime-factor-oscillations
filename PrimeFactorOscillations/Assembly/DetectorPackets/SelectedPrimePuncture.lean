/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/

import OAI.NumberTheory.DirichletL.GaussSum.FiniteTranslations
import PrimeFactorOscillations.Assembly.DetectorPackets.SexticDiagonalResidueMean

/-!
# SelectedPrimePuncture

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
# A bounded-cost physical filter for selected-prime ramification

One original translate minus the uniform residue average has multiplier
zero on frequencies divisible by c and one on every other frequency.
Its coefficient mass is exactly two, independent of the modulus.
At a proper prime modulus the frequency one survives unchanged.

This is an exact translation adapter for the existing cubic source.
It does not assert the enhanced probe's Mellin normalization or its
joint signed mean estimate.
-/

set_option maxHeartbeats 800000

noncomputable section
open scoped Classical
namespace OAI.SevenEighths.SelectedPrimePuncture

open CubicEisenstein

local notation "O" => ActualEisensteinCubic.O

def weight {R : Type*} [Fintype R] (i : Option R) : Complex :=
  match i with
  | none => 1
  | some _ => -(1/(Fintype.card R:Complex))

theorem weight_sum {R : Type*} [Fintype R] [Nonempty R] :
    (Finset.univ.sum fun i : Option R => weight i)=0 := by
  have hq : Not ((Fintype.card R:Complex)=0) := by
    exact_mod_cast Fintype.card_ne_zero
  simp only [Fintype.sum_option, weight, Finset.sum_const,
    Finset.card_univ, nsmul_eq_mul]
  field_simp
  norm_num

theorem weight_mass {R : Type*} [Fintype R] [Nonempty R] :
    (Finset.univ.sum fun i : Option R => norm (weight i))=2 := by
  have hq : Not ((Fintype.card R:Real)=0) := by
    exact_mod_cast Fintype.card_ne_zero
  simp only [Fintype.sum_option, weight, norm_one, norm_neg, norm_div,
    Complex.norm_natCast, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  field_simp
  norm_num

abbrev Residues (c : O) : Type := HasQuotient.Quotient O (Ideal.span {c})

def shift (c : O) (i : Option (Residues c)) : Complex :=
  match i with
  | none => 0
  | some h => -thetaFourierTranslation c h

theorem multiplier (c : O) (hc : Not (c=0)) [Fintype (Residues c)] (u : O) :
    finiteTranslationMultiplier (shift c) weight u =
      if Ideal.Quotient.mk (Ideal.span {c}) u=0 then 0 else 1 := by
  have hq : Not ((Fintype.card (Residues c):Complex)=0) := by
    exact_mod_cast Fintype.card_ne_zero
  have hp (h : Residues c) :
      ShortDraftTrace.breveE (cuspFrequency u*shift c (some h)) =
        quotientTrace c hc (h*Ideal.Quotient.mk (Ideal.span {c}) u) := by
    change ShortDraftTrace.breveE (cuspFrequency u*(-thetaFourierTranslation c h)) = _
    rw [show cuspFrequency u*(-thetaFourierTranslation c h) =
      -cuspFrequency u*thetaFourierTranslation c h by ring]
    exact thetaFourierTranslation_phase c hc h u
  unfold finiteTranslationMultiplier
  rw [Fintype.sum_option]
  have hzero :
      weight (none:Option (Residues c))*
        ShortDraftTrace.breveE (cuspFrequency u*shift c none)=1 := by
    simp [weight, shift]
  rw [hzero]
  simp only [hp, weight]
  have hs : (Finset.univ.sum fun h : Residues c =>
      quotientTrace c hc (h*Ideal.Quotient.mk (Ideal.span {c}) u)) =
      ((if Ideal.Quotient.mk (Ideal.span {c}) u=0 then Fintype.card (Residues c) else 0):Complex) :=
    by simpa only [apply_ite, Nat.cast_zero] using
      (AddChar.sum_mulShift (Ideal.Quotient.mk (Ideal.span {c}) u)
        (show (quotientTrace c hc).IsPrimitive from
          GeneralPrimitiveTrace.eisTraceModChar_breveE_primitive c hc))
  rw [<-Finset.mul_sum, hs]
  by_cases hu : Ideal.Quotient.mk (Ideal.span {c}) u=0
  . simp only [hu, ite_true]
    field_simp
    norm_num
  . simp [hu]

theorem principal_multiplier (c : O) (hc : Not (c=0))
    [(Ideal.span {c}:Ideal O).IsMaximal] [Fintype (Residues c)] :
    finiteTranslationMultiplier (shift c) weight 1=1 := by
  rw [multiplier c hc]
  have h : Not (Ideal.Quotient.mk (Ideal.span {c}) (1:O)=0) := by
    simpa only [map_one] using (one_ne_zero : Not ((1:Residues c)=0))
  rw [if_neg h]

theorem principal_coefficient (c : O) (hc : Not (c=0))
    [(Ideal.span {c}:Ideal O).IsMaximal] [Fintype (Residues c)] :
    (sourceBesselCoefficients.finiteTranslate (shift c) weight).value 1 =
      sourceBesselCoefficients.value 1 := by
  change finiteTranslationMultiplier (shift c) weight 1*sourceBesselCoefficients.value 1 = _
  rw [principal_multiplier c hc, one_mul]

theorem physical_source (c : O) [Fintype (Residues c)]
    (v : Real) (hv : 0 < v) (z : Complex) :
    (Finset.univ.sum fun i : Option (Residues c) =>
      weight i*cubicSourceResidualFunction (upperPoint (z+shift c i) v hv)) =
      (sourceBesselCoefficients.finiteTranslate (shift c) weight).fullFunction 0
        (upperPoint z v hv) := by
  rw [cubicSource_finite_translation]
  rw [weight_sum]
  simp

-- Apply the filter to the full frequency before factoring out sixth powers.
theorem sixth_frequency_multiplier (c : O) (hc : Not (c=0))
    [Fintype (Residues c)] (u : O) (m : Nat) :
    finiteTranslationMultiplier (shift c) weight (u*c^(6*m)) =
      if m=0 then finiteTranslationMultiplier (shift c) weight u else 0 := by
  by_cases hm : m=0
  . simp only [hm, mul_zero, pow_zero, mul_one, ite_true]
  . rw [if_neg hm, multiplier c hc]
    have hz : Ideal.Quotient.mk (Ideal.span {c}) c=0 :=
      Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (by simp))
    have h6 : Not (6*m=0) := by omega
    rw [map_mul, map_pow, hz, zero_pow h6, mul_zero]
    simp

theorem sixth_frequency_sum (c : O) (hc : Not (c=0))
    [Fintype (Residues c)] (u : O) (f : Nat -> Complex) :
    tsum (fun m : Nat =>
      finiteTranslationMultiplier (shift c) weight (u*c^(6*m))*f m) =
      finiteTranslationMultiplier (shift c) weight u*f 0 := by
  simp_rw [sixth_frequency_multiplier c hc u]
  simp

end OAI.SevenEighths.SelectedPrimePuncture

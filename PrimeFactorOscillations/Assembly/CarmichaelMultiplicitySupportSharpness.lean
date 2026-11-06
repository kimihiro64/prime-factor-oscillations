/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Assembly.CarmichaelFivePointMass
import PrimeFactorOscillations.Assembly.CarmichaelSimpleTreeSharpness
import PrimeFactorOscillations.Assembly.CarmichaelZetaTripleMultiplicity

/-!
# Complete affine multiplicity-support coefficient region

The universal region is a<=39 and a+b<=40. The simple-tree family forces
the first face; the exact five-point spectrum forces the second face.
The resulting triple-excess and weak-double coefficients are both sharp.
All old simple-spectrum and actual-zeta consumers remain imported.
-/

set_option autoImplicit false
set_option Elab.async false

noncomputable section

namespace PrimeFactorOscillations.CarmichaelDyadicSharpness

theorem universal_affine_multiplicity_support_iff (a b : Real) :
    (forall (I : Type) [Fintype I] (S : ReflectedSpectrum I (7 / 8)),
      a * S.weakUnitMass + b * S.weakRepeatedUnitMass <= S.carrierMass) <->
      a <= 39 /\ a + b <= 40 := by
  constructor
  . intro h
    have ha : a <= 39 := by
      by_contra hn
      have hLarge : 39 < a := lt_of_not_ge hn
      have hDen : 0 < a + 1 := by linarith
      have hCoeff : a / (a + 1) <= 39 / 40 := by
        apply (universal_simple_carrier_coefficient_iff (a / (a + 1))).mp
        intro I inst S hSimple
        have hQ : S.weakRepeatedUnitMass = 0 := by
          unfold ReflectedSpectrum.weakRepeatedUnitMass
          apply Finset.sum_eq_zero
          intro i hi
          simp [ReflectedSpectrum.repeatedUnitAt, hSimple i]
        have hE : S.weakExcessMass = 0 := by
          unfold ReflectedSpectrum.weakExcessMass
          apply Finset.sum_eq_zero
          intro i hi
          simp [ReflectedSpectrum.excessMassAt, hSimple i]
        have hBound := h I S
        rw [hQ, mul_zero, add_zero] at hBound
        have hWeak := S.weakMass_eq_unit_add_excess
        rw [hE, add_zero] at hWeak
        have hTotal := S.totalMass_eq_weakMass_add_carrierMass
        have hRaw : a * S.totalMass <= (a + 1) * S.carrierMass := by
          rw [hTotal, hWeak]
          nlinarith only [hBound]
        have hDiv := div_le_div_of_nonneg_right hRaw hDen.le
        have hCancel : (a + 1) * S.carrierMass / (a + 1) = S.carrierMass := by
          field_simp [hDen.ne']
        rw [hCancel] at hDiv
        convert hDiv using 1 <;> ring
      have hMul := mul_le_mul_of_nonneg_right hCoeff hDen.le
      have hCancel : a / (a + 1) * (a + 1) = a := by field_simp [hDen.ne']
      rw [hCancel] at hMul
      linarith
    have hab : a + b <= 40 := by
      have hFive := h (Fin 5) (fiveSpectrum 1 (by norm_num : (0 : Real) < 1))
      rw [fiveSpectrum_weakUnitMass, fiveSpectrum_weakRepeatedUnitMass,
        fiveSpectrum_carrierMass] at hFive
      norm_num at hFive
      exact hFive
    exact And.intro ha hab
  . intro h I inst S
    exact S.carrier_affine_support_bound a b h.1 h.2

theorem universal_triple_compensated_coefficient_iff (c : Real) :
    (forall (I : Type) [Fintype I] (S : ReflectedSpectrum I (7 / 8)),
      c * (S.totalMass - S.weakTripleExcessMass) <= S.carrierMass) <->
      c <= 20 / 21 := by
  constructor
  . intro h
    have hFive := h (Fin 5) (fiveSpectrum 1 (by norm_num : (0 : Real) < 1))
    rw [fiveSpectrum_totalMass, fiveSpectrum_weakTripleExcessMass,
      fiveSpectrum_carrierMass] at hFive
    norm_num at hFive
    linarith
  . intro hc I inst S
    exact (mul_le_mul_of_nonneg_right hc S.totalMass_sub_triple_nonneg).trans
      S.carrier_triple_compensated_bound

theorem universal_double_weak_carrier_coefficient_iff (c : Real) :
    (forall (I : Type) [Fintype I] (S : ReflectedSpectrum I (7 / 8)),
      (forall i, Membership.mem S.weakIndices i -> S.mult i <= 2) ->
        c * S.totalMass <= S.carrierMass) <-> c <= 20 / 21 := by
  constructor
  . intro h
    have hFive := h (Fin 5) (fiveSpectrum 1 (by norm_num : (0 : Real) < 1))
      (fiveSpectrum_double_weak 1 (by norm_num))
    rw [fiveSpectrum_totalMass, fiveSpectrum_carrierMass] at hFive
    norm_num at hFive
    linarith
  . intro hc I inst S hDouble
    have hNonneg : 0 <= S.totalMass :=
      Finset.sum_nonneg (fun i _ => S.mass_nonneg i)
    exact (mul_le_mul_of_nonneg_right hc hNonneg).trans (S.double_weak_carrier_bound hDouble)

end PrimeFactorOscillations.CarmichaelDyadicSharpness

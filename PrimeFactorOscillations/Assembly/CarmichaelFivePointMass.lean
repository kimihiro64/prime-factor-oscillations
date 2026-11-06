/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Assembly.CarmichaelFivePointRows
import PrimeFactorOscillations.Assembly.CarmichaelTripleMultiplicity

/-!
# Exact equality in the joint and triple-excess carrier bounds

For every H>0 the five-point model has
P=Q=1/H^2, W=2/H^2, C=40/H^2, A=42/H^2 and T=0.
Thus the coefficient 20/21 is attained, not just approached.
-/

set_option autoImplicit false
set_option Elab.async false

noncomputable section

namespace PrimeFactorOscillations.CarmichaelDyadicSharpness

theorem fiveSpectrum_totalMass (H : Real) (hH : 0 < H) :
    (fiveSpectrum H hH).totalMass = 42 / H ^ 2 := by
  change Finset.univ.sum (fun i : Fin 5 =>
    (fiveMultiplicity i : Real) / (fivePoint H i).im ^ 2) = _
  norm_num [Fin.sum_univ_succ, fiveMultiplicity, fivePoint]
  field_simp [hH.ne']
  ring

theorem fiveSpectrum_weakMass (H : Real) (hH : 0 < H) :
    (fiveSpectrum H hH).weakMass = 2 / H ^ 2 := by
  unfold ReflectedSpectrum.weakMass
  rw [fiveSpectrum_weakIndices, Finset.sum_singleton]
  norm_num [ReflectedSpectrum.mass, fiveSpectrum, fivePoint, fiveMultiplicity]

theorem fiveSpectrum_weakUnitMass (H : Real) (hH : 0 < H) :
    (fiveSpectrum H hH).weakUnitMass = 1 / H ^ 2 := by
  unfold ReflectedSpectrum.weakUnitMass
  rw [fiveSpectrum_weakIndices, Finset.sum_singleton]
  rfl

theorem fiveSpectrum_weakRepeatedUnitMass (H : Real) (hH : 0 < H) :
    (fiveSpectrum H hH).weakRepeatedUnitMass = 1 / H ^ 2 := by
  unfold ReflectedSpectrum.weakRepeatedUnitMass
  rw [fiveSpectrum_weakIndices, Finset.sum_singleton]
  norm_num [ReflectedSpectrum.repeatedUnitAt, ReflectedSpectrum.unitMass,
    fiveSpectrum, fivePoint, fiveMultiplicity]

theorem fiveSpectrum_weakTripleExcessMass (H : Real) (hH : 0 < H) :
    (fiveSpectrum H hH).weakTripleExcessMass = 0 := by
  unfold ReflectedSpectrum.weakTripleExcessMass
  rw [fiveSpectrum_weakIndices, Finset.sum_singleton]
  norm_num [ReflectedSpectrum.tripleExcessAt, fiveSpectrum, fiveMultiplicity]

theorem fiveSpectrum_carrierMass (H : Real) (hH : 0 < H) :
    (fiveSpectrum H hH).carrierMass = 40 / H ^ 2 := by
  have h := (fiveSpectrum H hH).totalMass_eq_weakMass_add_carrierMass
  rw [fiveSpectrum_totalMass, fiveSpectrum_weakMass] at h
  calc
    _ = 42 / H ^ 2 - 2 / H ^ 2 := by linarith
    _ = 40 / H ^ 2 := by ring

theorem fiveSpectrum_totalMass_pos (H : Real) (hH : 0 < H) :
    0 < (fiveSpectrum H hH).totalMass := by
  rw [fiveSpectrum_totalMass]
  exact div_pos (by norm_num) (pow_pos hH 2)

theorem fiveSpectrum_carrier_ratio (H : Real) (hH : 0 < H) :
    (fiveSpectrum H hH).carrierMass / (fiveSpectrum H hH).totalMass = 20 / 21 := by
  rw [fiveSpectrum_carrierMass, fiveSpectrum_totalMass]
  field_simp [hH.ne']
  ring

theorem fiveSpectrum_joint_equality (H : Real) (hH : 0 < H) :
    (fiveSpectrum H hH).carrierMass =
      39 * (fiveSpectrum H hH).weakUnitMass +
        (fiveSpectrum H hH).weakRepeatedUnitMass := by
  rw [fiveSpectrum_carrierMass, fiveSpectrum_weakUnitMass, fiveSpectrum_weakRepeatedUnitMass]
  ring

theorem fiveSpectrum_double_weak (H : Real) (hH : 0 < H) :
    forall i, Membership.mem (fiveSpectrum H hH).weakIndices i ->
      (fiveSpectrum H hH).mult i <= 2 := by
  intro i hi
  have he := (fiveSpectrum_weak_iff H hH i).mp hi
  subst i
  norm_num [fiveSpectrum, fiveMultiplicity]

end PrimeFactorOscillations.CarmichaelDyadicSharpness

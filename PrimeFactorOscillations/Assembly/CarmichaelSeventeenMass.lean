/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Assembly.CarmichaelSeventeenRows

/-!
# Exact sharpness masses for the fifth-multiplicity tail

All masses scale by H^(-2). The full carrier has mass1484/H^2;
P=Q=37/H^2 and R5=1/H^2. Thus the full gap equals4R5 exactly.
-/

set_option autoImplicit false
set_option Elab.async false

noncomputable section

namespace PrimeFactorOscillations.CarmichaelDyadicSharpness

theorem seventeenSpectrum_totalMass (H : Real) (hH : 0 < H) :
    (seventeenSpectrum H hH).totalMass = 1565 / H ^ 2 := by
  change Finset.univ.sum (fun i : Fin 17 =>
    (seventeenMultiplicity i : Real) / (seventeenPoint H i).im ^ 2) = _
  norm_num [Fin.sum_univ_succ, seventeenMultiplicity, seventeenPoint,
    seventeenHeightDenominator]
  field_simp [hH.ne']
  ring

theorem seventeenSpectrum_weakMass (H : Real) (hH : 0 < H) :
    (seventeenSpectrum H hH).weakMass = 81 / H ^ 2 := by
  unfold ReflectedSpectrum.weakMass
  rw [seventeenSpectrum_weakIndices]
  norm_num [ReflectedSpectrum.mass, seventeenSpectrum, seventeenPoint,
    seventeenHeightDenominator, seventeenMultiplicity]
  field_simp [hH.ne']
  ring

theorem seventeenSpectrum_weakUnitMass (H : Real) (hH : 0 < H) :
    (seventeenSpectrum H hH).weakUnitMass = 37 / H ^ 2 := by
  unfold ReflectedSpectrum.weakUnitMass
  rw [seventeenSpectrum_weakIndices]
  norm_num [ReflectedSpectrum.unitMass, seventeenSpectrum, seventeenPoint,
    seventeenHeightDenominator]
  field_simp [hH.ne']
  ring

theorem seventeenSpectrum_weakRepeatedUnitMass (H : Real) (hH : 0 < H) :
    (seventeenSpectrum H hH).weakRepeatedUnitMass = 37 / H ^ 2 := by
  unfold ReflectedSpectrum.weakRepeatedUnitMass
  rw [seventeenSpectrum_weakIndices]
  norm_num [ReflectedSpectrum.repeatedUnitAt, ReflectedSpectrum.unitMass,
    seventeenSpectrum, seventeenPoint, seventeenHeightDenominator, seventeenMultiplicity]
  field_simp [hH.ne']
  ring

theorem seventeenSpectrum_weakFifthUnitMass (H : Real) (hH : 0 < H) :
    (seventeenSpectrum H hH).weakFifthUnitMass = 1 / H ^ 2 := by
  unfold ReflectedSpectrum.weakFifthUnitMass
  rw [seventeenSpectrum_weakIndices]
  norm_num [ReflectedSpectrum.fifthUnitAt, ReflectedSpectrum.unitMass,
    seventeenSpectrum, seventeenPoint, seventeenHeightDenominator, seventeenMultiplicity]

theorem seventeenSpectrum_carrierMass (H : Real) (hH : 0 < H) :
    (seventeenSpectrum H hH).carrierMass = 1484 / H ^ 2 := by
  have h := (seventeenSpectrum H hH).totalMass_eq_weakMass_add_carrierMass
  rw [seventeenSpectrum_totalMass, seventeenSpectrum_weakMass] at h
  calc
    _ = 1565 / H ^ 2 - 81 / H ^ 2 := by linarith
    _ = 1484 / H ^ 2 := by ring

theorem seventeenSpectrum_totalMass_pos (H : Real) (hH : 0 < H) :
    0 < (seventeenSpectrum H hH).totalMass := by
  rw [seventeenSpectrum_totalMass]
  exact div_pos (by norm_num) (pow_pos hH 2)

theorem seventeenSpectrum_weakFifthUnitMass_pos (H : Real) (hH : 0 < H) :
    0 < (seventeenSpectrum H hH).weakFifthUnitMass := by
  rw [seventeenSpectrum_weakFifthUnitMass]
  exact div_pos (by norm_num) (pow_pos hH 2)

theorem seventeenSpectrum_fifth_gap (H : Real) (hH : 0 < H) :
    (seventeenSpectrum H hH).carrierMass -
        39 * (seventeenSpectrum H hH).weakUnitMass -
        (seventeenSpectrum H hH).weakRepeatedUnitMass =
      4 * (seventeenSpectrum H hH).weakFifthUnitMass := by
  rw [seventeenSpectrum_carrierMass, seventeenSpectrum_weakUnitMass,
    seventeenSpectrum_weakRepeatedUnitMass, seventeenSpectrum_weakFifthUnitMass]
  ring

end PrimeFactorOscillations.CarmichaelDyadicSharpness

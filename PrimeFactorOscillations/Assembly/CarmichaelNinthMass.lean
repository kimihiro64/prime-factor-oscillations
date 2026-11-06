/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Assembly.CarmichaelNinthRows

/-!
# Exact masses of the ninth-tail equality witness

All formulas hold for every positive H. The complete carrier deficit is
44/H^2, split as 4*(5/H^2)+16*(1/H^2)+8/H^2.
-/

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 4000000

noncomputable section

namespace PrimeFactorOscillations.CarmichaelDyadicSharpness

theorem ninthSpectrum_totalMass (H : Real) (hH : 0 < H) :
    (ninthSpectrum H hH).totalMass = 9713 / H ^ 2 := by
  change Finset.univ.sum (fun i : Fin 29 =>
    (ninthMultiplicity i : Real) / (ninthPoint H i).im ^ 2) = _
  norm_num [Fin.sum_univ_succ, ninthMultiplicity, ninthPoint, ninthHeightDenominator]
  field_simp [hH.ne']
  ring

theorem ninthSpectrum_weakMass (H : Real) (hH : 0 < H) :
    (ninthSpectrum H hH).weakMass = 509 / H ^ 2 := by
  unfold ReflectedSpectrum.weakMass
  rw [ninthSpectrum_weakIndices]
  norm_num [ReflectedSpectrum.mass, ninthSpectrum, ninthPoint,
    ninthHeightDenominator, ninthMultiplicity]
  field_simp [hH.ne']
  ring

theorem ninthSpectrum_weakUnitMass (H : Real) (hH : 0 < H) :
    (ninthSpectrum H hH).weakUnitMass = 229 / H ^ 2 := by
  unfold ReflectedSpectrum.weakUnitMass
  rw [ninthSpectrum_weakIndices]
  norm_num [ReflectedSpectrum.unitMass, ninthSpectrum, ninthPoint, ninthHeightDenominator]
  field_simp [hH.ne']
  ring

theorem ninthSpectrum_weakRepeatedUnitMass (H : Real) (hH : 0 < H) :
    (ninthSpectrum H hH).weakRepeatedUnitMass = 229 / H ^ 2 := by
  unfold ReflectedSpectrum.weakRepeatedUnitMass
  rw [ninthSpectrum_weakIndices]
  norm_num [ReflectedSpectrum.repeatedUnitAt, ReflectedSpectrum.unitMass,
    ninthSpectrum, ninthPoint, ninthHeightDenominator, ninthMultiplicity]
  field_simp [hH.ne']
  ring

theorem ninthSpectrum_weakFifthUnitMass (H : Real) (hH : 0 < H) :
    (ninthSpectrum H hH).weakFifthUnitMass = 5 / H ^ 2 := by
  unfold ReflectedSpectrum.weakFifthUnitMass
  rw [ninthSpectrum_weakIndices]
  norm_num [ReflectedSpectrum.fifthUnitAt, ReflectedSpectrum.unitMass,
    ninthSpectrum, ninthPoint, ninthHeightDenominator, ninthMultiplicity]
  field_simp [hH.ne']
  ring

theorem ninthSpectrum_weakNinthUnitMass (H : Real) (hH : 0 < H) :
    (ninthSpectrum H hH).weakNinthUnitMass = 1 / H ^ 2 := by
  unfold ReflectedSpectrum.weakNinthUnitMass
  rw [ninthSpectrum_weakIndices]
  norm_num [ReflectedSpectrum.ninthUnitAt, ReflectedSpectrum.unitMass,
    ninthSpectrum, ninthPoint, ninthHeightDenominator, ninthMultiplicity]

theorem ninthSpectrum_globalOffcriticalExcess (H : Real) (hH : 0 < H) :
    (ninthSpectrum H hH).globalOffcriticalExcess = 8 / H ^ 2 := by
  change Finset.univ.sum (fun i : Fin 29 =>
    if (ninthPoint H i).re < 1 / 2 then
      ((ninthMultiplicity i - 3 : Nat) : Real) * (1 / (ninthPoint H i).im ^ 2)
    else 0) = _
  norm_num [Fin.sum_univ_succ, ninthMultiplicity, ninthPoint,
    ninthRealCode, ninthHeightDenominator]
  field_simp [hH.ne']
  ring

theorem ninthSpectrum_carrierMass (H : Real) (hH : 0 < H) :
    (ninthSpectrum H hH).carrierMass = 9204 / H ^ 2 := by
  have h := (ninthSpectrum H hH).totalMass_eq_weakMass_add_carrierMass
  rw [ninthSpectrum_totalMass, ninthSpectrum_weakMass] at h
  calc
    _ = 9713 / H ^ 2 - 509 / H ^ 2 := by linarith
    _ = 9204 / H ^ 2 := by ring

theorem ninthSpectrum_global_excess_equality (H : Real) (hH : 0 < H) :
    (ninthSpectrum H hH).carrierMass =
      39 * (ninthSpectrum H hH).weakUnitMass +
      (ninthSpectrum H hH).weakRepeatedUnitMass +
      4 * (ninthSpectrum H hH).weakFifthUnitMass +
      16 * (ninthSpectrum H hH).weakNinthUnitMass +
      (ninthSpectrum H hH).globalOffcriticalExcess := by
  rw [ninthSpectrum_carrierMass, ninthSpectrum_weakUnitMass,
    ninthSpectrum_weakRepeatedUnitMass, ninthSpectrum_weakFifthUnitMass,
    ninthSpectrum_weakNinthUnitMass, ninthSpectrum_globalOffcriticalExcess]
  ring

theorem ninthSpectrum_weakNinthUnitMass_pos (H : Real) (hH : 0 < H) :
    0 < (ninthSpectrum H hH).weakNinthUnitMass := by
  rw [ninthSpectrum_weakNinthUnitMass]
  exact div_pos (by norm_num) (pow_pos hH 2)

end PrimeFactorOscillations.CarmichaelDyadicSharpness


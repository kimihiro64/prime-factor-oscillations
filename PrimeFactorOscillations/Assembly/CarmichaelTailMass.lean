/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Assembly.CarmichaelSeventeenMass
import PrimeFactorOscillations.Assembly.CarmichaelTailRows

/-!
# Exact homogeneous masses of all three coefficient-facet witnesses

The nine-point model has(R5,V3,D)=(1,0,16)/H^2.
The thirteen-point model has(R5,V3,D)=(0,4,4)/H^2.
The completed seventeen-point model has(R5,V3,D)=(1,4,4)/H^2.
-/

set_option autoImplicit false
set_option Elab.async false

noncomputable section

namespace PrimeFactorOscillations.CarmichaelDyadicSharpness

theorem tailNineSpectrum_totalMass (H : Real) (hH : 0 < H) :
    (tailNineSpectrum H hH).totalMass = 733 / H ^ 2 := by
  change Finset.univ.sum (fun i : Fin 9 =>
    (tailNineMultiplicity i : Real) / (tailNinePoint H i).im ^ 2) = _
  norm_num [Fin.sum_univ_succ, tailNineMultiplicity, tailNinePoint,
    tailNineHeightDenominator]
  field_simp [hH.ne']
  ring

theorem tailNineSpectrum_weakMass (H : Real) (hH : 0 < H) :
    (tailNineSpectrum H hH).weakMass = 37 / H ^ 2 := by
  unfold ReflectedSpectrum.weakMass
  rw [tailNineSpectrum_weakIndices]
  norm_num [ReflectedSpectrum.mass, tailNineSpectrum, tailNinePoint,
    tailNineHeightDenominator, tailNineMultiplicity]
  field_simp [hH.ne']
  ring

theorem tailNineSpectrum_weakUnitMass (H : Real) (hH : 0 < H) :
    (tailNineSpectrum H hH).weakUnitMass = 17 / H ^ 2 := by
  unfold ReflectedSpectrum.weakUnitMass
  rw [tailNineSpectrum_weakIndices]
  norm_num [ReflectedSpectrum.unitMass, tailNineSpectrum, tailNinePoint,
    tailNineHeightDenominator, tailNineMultiplicity]
  field_simp [hH.ne']
  ring

theorem tailNineSpectrum_weakRepeatedUnitMass (H : Real) (hH : 0 < H) :
    (tailNineSpectrum H hH).weakRepeatedUnitMass = 17 / H ^ 2 := by
  unfold ReflectedSpectrum.weakRepeatedUnitMass
  rw [tailNineSpectrum_weakIndices]
  norm_num [ReflectedSpectrum.repeatedUnitAt, ReflectedSpectrum.unitMass, tailNineSpectrum, tailNinePoint,
    tailNineHeightDenominator, tailNineMultiplicity]
  field_simp [hH.ne']
  ring

theorem tailNineSpectrum_weakFifthUnitMass (H : Real) (hH : 0 < H) :
    (tailNineSpectrum H hH).weakFifthUnitMass = 1 / H ^ 2 := by
  unfold ReflectedSpectrum.weakFifthUnitMass
  rw [tailNineSpectrum_weakIndices]
  norm_num [ReflectedSpectrum.fifthUnitAt, ReflectedSpectrum.unitMass, tailNineSpectrum, tailNinePoint,
    tailNineHeightDenominator, tailNineMultiplicity]

theorem tailNineSpectrum_weakOffTripleUnitMass (H : Real) (hH : 0 < H) :
    (tailNineSpectrum H hH).weakOffTripleUnitMass = 0 / H ^ 2 := by
  classical
  unfold ReflectedSpectrum.weakOffTripleUnitMass ReflectedSpectrum.offTripleUnitAt
  rw [tailNineSpectrum_weakIndices]
  norm_num [Fin.sum_univ_succ, ReflectedSpectrum.unitMass,
    tailNineSpectrum, tailNinePoint, tailNineRealCode,
    tailNineHeightDenominator, tailNineMultiplicity]

theorem tailNineSpectrum_carrierMass (H : Real) (hH : 0 < H) :
    (tailNineSpectrum H hH).carrierMass = 696 / H ^ 2 := by
  have h := (tailNineSpectrum H hH).totalMass_eq_weakMass_add_carrierMass
  rw [tailNineSpectrum_totalMass, tailNineSpectrum_weakMass] at h
  calc
    _ = 733 / H ^ 2 - 37 / H ^ 2 := by linarith
    _ = 696 / H ^ 2 := by ring

theorem tailThirteenSpectrum_totalMass (H : Real) (hH : 0 < H) :
    (tailThirteenSpectrum H hH).totalMass = 890 / H ^ 2 := by
  change Finset.univ.sum (fun i : Fin 13 =>
    (tailThirteenMultiplicity i : Real) / (tailThirteenPoint H i).im ^ 2) = _
  norm_num [Fin.sum_univ_succ, tailThirteenMultiplicity, tailThirteenPoint,
    tailThirteenHeightDenominator]
  field_simp [hH.ne']
  ring

theorem tailThirteenSpectrum_weakMass (H : Real) (hH : 0 < H) :
    (tailThirteenSpectrum H hH).weakMass = 46 / H ^ 2 := by
  unfold ReflectedSpectrum.weakMass
  rw [tailThirteenSpectrum_weakIndices]
  norm_num [ReflectedSpectrum.mass, tailThirteenSpectrum, tailThirteenPoint,
    tailThirteenHeightDenominator, tailThirteenMultiplicity]
  field_simp [hH.ne']
  ring

theorem tailThirteenSpectrum_weakUnitMass (H : Real) (hH : 0 < H) :
    (tailThirteenSpectrum H hH).weakUnitMass = 21 / H ^ 2 := by
  unfold ReflectedSpectrum.weakUnitMass
  rw [tailThirteenSpectrum_weakIndices]
  norm_num [ReflectedSpectrum.unitMass, tailThirteenSpectrum, tailThirteenPoint,
    tailThirteenHeightDenominator, tailThirteenMultiplicity]
  field_simp [hH.ne']
  ring

theorem tailThirteenSpectrum_weakRepeatedUnitMass (H : Real) (hH : 0 < H) :
    (tailThirteenSpectrum H hH).weakRepeatedUnitMass = 21 / H ^ 2 := by
  unfold ReflectedSpectrum.weakRepeatedUnitMass
  rw [tailThirteenSpectrum_weakIndices]
  norm_num [ReflectedSpectrum.repeatedUnitAt, ReflectedSpectrum.unitMass, tailThirteenSpectrum, tailThirteenPoint,
    tailThirteenHeightDenominator, tailThirteenMultiplicity]
  field_simp [hH.ne']
  ring

theorem tailThirteenSpectrum_weakFifthUnitMass (H : Real) (hH : 0 < H) :
    (tailThirteenSpectrum H hH).weakFifthUnitMass = 0 / H ^ 2 := by
  unfold ReflectedSpectrum.weakFifthUnitMass
  rw [tailThirteenSpectrum_weakIndices]
  norm_num [ReflectedSpectrum.fifthUnitAt, ReflectedSpectrum.unitMass, tailThirteenSpectrum, tailThirteenPoint,
    tailThirteenHeightDenominator, tailThirteenMultiplicity]

theorem tailThirteenSpectrum_weakOffTripleUnitMass (H : Real) (hH : 0 < H) :
    (tailThirteenSpectrum H hH).weakOffTripleUnitMass = 4 / H ^ 2 := by
  classical
  unfold ReflectedSpectrum.weakOffTripleUnitMass ReflectedSpectrum.offTripleUnitAt
  rw [tailThirteenSpectrum_weakIndices]
  norm_num [Fin.sum_univ_succ, ReflectedSpectrum.unitMass,
    tailThirteenSpectrum, tailThirteenPoint, tailThirteenRealCode,
    tailThirteenHeightDenominator, tailThirteenMultiplicity]
  all_goals field_simp [hH.ne']
  all_goals ring

theorem tailThirteenSpectrum_carrierMass (H : Real) (hH : 0 < H) :
    (tailThirteenSpectrum H hH).carrierMass = 844 / H ^ 2 := by
  have h := (tailThirteenSpectrum H hH).totalMass_eq_weakMass_add_carrierMass
  rw [tailThirteenSpectrum_totalMass, tailThirteenSpectrum_weakMass] at h
  calc
    _ = 890 / H ^ 2 - 46 / H ^ 2 := by linarith
    _ = 844 / H ^ 2 := by ring

theorem seventeenSpectrum_weakOffTripleUnitMass (H : Real) (hH : 0 < H) :
    (seventeenSpectrum H hH).weakOffTripleUnitMass = 4 / H ^ 2 := by
  classical
  unfold ReflectedSpectrum.weakOffTripleUnitMass ReflectedSpectrum.offTripleUnitAt
  rw [seventeenSpectrum_weakIndices]
  norm_num [Fin.sum_univ_succ, ReflectedSpectrum.unitMass,
    seventeenSpectrum, seventeenPoint, seventeenRealCode,
    seventeenHeightDenominator, seventeenMultiplicity]
  all_goals field_simp [hH.ne']
  all_goals ring

end PrimeFactorOscillations.CarmichaelDyadicSharpness

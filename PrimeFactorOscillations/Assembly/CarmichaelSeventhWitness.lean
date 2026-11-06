/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Assembly.CarmichaelNinthSupport
import PrimeFactorOscillations.Assembly.CarmichaelSeventeenMass

/-!
# The sharp global-excess coefficient on seventeen points

Raising the central order to seven and its first reflected reference pair
to four gives D=8, R5=1, R9=0 and J3=4, all scaled by H^(-2).
-/

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1000000

noncomputable section

namespace PrimeFactorOscillations.CarmichaelDyadicSharpness

open CarmichaelTraceSharpness DirichletCompensatedProbe

theorem seventeenSpectrum_globalOffcriticalExcess (H : Real) (hH : 0 < H) :
    (seventeenSpectrum H hH).globalOffcriticalExcess = 0 := by
  apply (seventeenSpectrum H hH).globalOffcriticalExcess_eq_zero_iff.mpr
  intro i hi
  fin_cases i <;> norm_num [seventeenSpectrum, seventeenPoint, seventeenRealCode,
    seventeenMultiplicity] at *

theorem seventeenSpectrum_weakNinthUnitMass (H : Real) (hH : 0 < H) :
    (seventeenSpectrum H hH).weakNinthUnitMass = 0 := by
  unfold ReflectedSpectrum.weakNinthUnitMass
  apply Finset.sum_eq_zero
  intro i hi
  fin_cases i <;> norm_num [ReflectedSpectrum.ninthUnitAt, seventeenSpectrum,
    seventeenMultiplicity]

def seventhMultiplicity (i : Fin 17) : Nat :=
  if i = 0 then 7 else if i = 1 \/ i = 2 then 4 else seventeenMultiplicity i

def seventhSpectrum (H : Real) (hH : 0 < H) : ReflectedSpectrum (Fin 17) (7 / 8) :=
  { seventeenSpectrum H hH with
    mult := seventhMultiplicity
    mult_pos := by
      intro i
      fin_cases i <;> norm_num [seventhMultiplicity, seventeenMultiplicity]
    mult_mirror := by
      intro i
      fin_cases i <;> rfl }

theorem seventhSpectrum_two_order (H : Real) (hH : 0 < H) (i : Fin 17) :
    (seventhSpectrum H hH).rowOrder 2 i =
      (seventeenTwoTarget i).elim 0 seventhMultiplicity := by
  cases ht : seventeenTwoTarget i with
  | none =>
      change atomicOrder (seventeenPoint H) seventhMultiplicity
        (powerMap 2 (seventeenPoint H i)) = 0
      exact atomicOrder_zero _ _ _ (seventeenPoint_two_absent H i ht)
  | some j =>
      change atomicOrder (seventeenPoint H) seventhMultiplicity
        (powerMap 2 (seventeenPoint H i)) = seventhMultiplicity j
      rw [seventeenPoint_two_of_target H i j ht]
      exact atomicOrder_at _ _ (seventeenPoint_injective H) j

theorem seventhSpectrum_four_order (H : Real) (hH : 0 < H) (i : Fin 17) :
    (seventhSpectrum H hH).rowOrder 4 i =
      (seventeenFourTarget i).elim 0 seventhMultiplicity := by
  cases ht : seventeenFourTarget i with
  | none =>
      change atomicOrder (seventeenPoint H) seventhMultiplicity
        (powerMap 4 (seventeenPoint H i)) = 0
      exact atomicOrder_zero _ _ _ (seventeenPoint_four_absent H i ht)
  | some j =>
      change atomicOrder (seventeenPoint H) seventhMultiplicity
        (powerMap 4 (seventeenPoint H i)) = seventhMultiplicity j
      rw [seventeenPoint_four_of_target H i j ht]
      exact atomicOrder_at _ _ (seventeenPoint_injective H) j

theorem seventhSpectrum_weakIndices (H : Real) (hH : 0 < H) :
    (seventhSpectrum H hH).weakIndices = {0, 1, 3, 5} := by
  classical
  apply Finset.ext
  intro i
  rw [ReflectedSpectrum.weakIndices, Finset.mem_filter]
  simp only [Finset.mem_univ, true_and]
  rw [seventhSpectrum_two_order, seventhSpectrum_four_order]
  change ((seventhMultiplicity i : Real) <=
      2 * (((seventeenTwoTarget i).elim 0 seventhMultiplicity : Nat) : Real) /\
    (seventhMultiplicity i : Real) <=
      4 * (((seventeenFourTarget i).elim 0 seventhMultiplicity : Nat) : Real)) <->
        Membership.mem ({0, 1, 3, 5} : Finset (Fin 17)) i
  fin_cases i <;> norm_num [seventhMultiplicity, seventeenMultiplicity,
    seventeenTwoTarget, seventeenFourTarget]

theorem seventhSpectrum_totalMass (H : Real) (hH : 0 < H) :
    (seventhSpectrum H hH).totalMass = 1575 / H ^ 2 := by
  change Finset.univ.sum (fun i : Fin 17 =>
    (seventhMultiplicity i : Real) / (seventeenPoint H i).im ^ 2) = _
  norm_num [Fin.sum_univ_succ, seventhMultiplicity, seventeenMultiplicity,
    seventeenPoint, seventeenHeightDenominator]
  field_simp [hH.ne']
  ring

theorem seventhSpectrum_weakMass (H : Real) (hH : 0 < H) :
    (seventhSpectrum H hH).weakMass = 87 / H ^ 2 := by
  unfold ReflectedSpectrum.weakMass
  rw [seventhSpectrum_weakIndices]
  norm_num [ReflectedSpectrum.mass, seventhSpectrum, seventeenSpectrum, seventhMultiplicity,
    seventeenMultiplicity, seventeenPoint, seventeenHeightDenominator]
  field_simp [hH.ne']
  ring

theorem seventhSpectrum_weakUnitMass (H : Real) (hH : 0 < H) :
    (seventhSpectrum H hH).weakUnitMass = 37 / H ^ 2 := by
  unfold ReflectedSpectrum.weakUnitMass
  rw [seventhSpectrum_weakIndices]
  norm_num [ReflectedSpectrum.unitMass, seventhSpectrum, seventeenSpectrum,
    seventeenPoint, seventeenHeightDenominator]
  field_simp [hH.ne']
  ring

theorem seventhSpectrum_weakRepeatedUnitMass (H : Real) (hH : 0 < H) :
    (seventhSpectrum H hH).weakRepeatedUnitMass = 37 / H ^ 2 := by
  unfold ReflectedSpectrum.weakRepeatedUnitMass
  rw [seventhSpectrum_weakIndices]
  norm_num [ReflectedSpectrum.repeatedUnitAt, ReflectedSpectrum.unitMass,
    seventhSpectrum, seventeenSpectrum, seventhMultiplicity, seventeenMultiplicity,
    seventeenPoint, seventeenHeightDenominator]
  field_simp [hH.ne']
  ring

theorem seventhSpectrum_weakFifthUnitMass (H : Real) (hH : 0 < H) :
    (seventhSpectrum H hH).weakFifthUnitMass = 1 / H ^ 2 := by
  unfold ReflectedSpectrum.weakFifthUnitMass
  rw [seventhSpectrum_weakIndices]
  norm_num [ReflectedSpectrum.fifthUnitAt, ReflectedSpectrum.unitMass,
    seventhSpectrum, seventeenSpectrum, seventhMultiplicity, seventeenMultiplicity,
    seventeenPoint, seventeenHeightDenominator]

theorem seventhSpectrum_weakNinthUnitMass (H : Real) (hH : 0 < H) :
    (seventhSpectrum H hH).weakNinthUnitMass = 0 := by
  unfold ReflectedSpectrum.weakNinthUnitMass
  apply Finset.sum_eq_zero
  intro i hi
  fin_cases i <;> norm_num [ReflectedSpectrum.ninthUnitAt, seventhSpectrum,
    seventhMultiplicity, seventeenMultiplicity]

theorem seventhSpectrum_globalOffcriticalExcess (H : Real) (hH : 0 < H) :
    (seventhSpectrum H hH).globalOffcriticalExcess = 4 / H ^ 2 := by
  change Finset.univ.sum (fun i : Fin 17 =>
    if (seventeenPoint H i).re < 1 / 2 then
      ((seventhMultiplicity i - 3 : Nat) : Real) * (1 / (seventeenPoint H i).im ^ 2)
    else 0) = _
  norm_num [Fin.sum_univ_succ, seventhMultiplicity, seventeenMultiplicity,
    seventeenPoint, seventeenRealCode, seventeenHeightDenominator]
  field_simp [hH.ne']
  ring

theorem seventhSpectrum_carrierMass (H : Real) (hH : 0 < H) :
    (seventhSpectrum H hH).carrierMass = 1488 / H ^ 2 := by
  have h := (seventhSpectrum H hH).totalMass_eq_weakMass_add_carrierMass
  rw [seventhSpectrum_totalMass, seventhSpectrum_weakMass] at h
  calc
    _ = 1575 / H ^ 2 - 87 / H ^ 2 := by linarith
    _ = 1488 / H ^ 2 := by ring

theorem seventhSpectrum_global_excess_equality (H : Real) (hH : 0 < H) :
    (seventhSpectrum H hH).carrierMass =
      39 * (seventhSpectrum H hH).weakUnitMass +
      (seventhSpectrum H hH).weakRepeatedUnitMass +
      4 * (seventhSpectrum H hH).weakFifthUnitMass +
      16 * (seventhSpectrum H hH).weakNinthUnitMass +
      (seventhSpectrum H hH).globalOffcriticalExcess := by
  rw [seventhSpectrum_carrierMass, seventhSpectrum_weakUnitMass,
    seventhSpectrum_weakRepeatedUnitMass, seventhSpectrum_weakFifthUnitMass,
    seventhSpectrum_weakNinthUnitMass, seventhSpectrum_globalOffcriticalExcess]
  ring

end PrimeFactorOscillations.CarmichaelDyadicSharpness


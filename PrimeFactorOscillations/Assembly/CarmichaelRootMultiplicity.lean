/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Assembly.CarmichaelSeventeenMass

/-!
# Both central orders in the minimal geometry

The same seventeen-point carrier attains fifth-tail equality with central
order five or six. All positive heights are allowed.
-/

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1000000

noncomputable section

namespace PrimeFactorOscillations.CarmichaelDyadicSharpness

open CarmichaelTraceSharpness DirichletCompensatedProbe

def seventeenRootMultiplicity (M : Nat) (i : Fin 17) : Nat :=
  if i = 0 then M else seventeenMultiplicity i

def seventeenRootSpectrum (H : Real) (hH : 0 < H) (M : Nat)
    (hM : M = 5 \/ M = 6) : ReflectedSpectrum (Fin 17) (7 / 8) :=
  { seventeenSpectrum H hH with
    mult := seventeenRootMultiplicity M
    mult_pos := by
      intro i
      rcases hM with hM | hM <;> fin_cases i <;>
        norm_num [seventeenRootMultiplicity, seventeenMultiplicity, hM]
    mult_mirror := by
      intro i
      fin_cases i <;> rfl }

theorem seventeenRootSpectrum_two_order (H : Real) (hH : 0 < H) (M : Nat)
    (hM : M = 5 \/ M = 6) (i : Fin 17) :
    (seventeenRootSpectrum H hH M hM).rowOrder 2 i =
      (seventeenTwoTarget i).elim 0 (seventeenRootMultiplicity M) := by
  cases ht : seventeenTwoTarget i with
  | none =>
      change atomicOrder (seventeenPoint H) (seventeenRootMultiplicity M)
        (powerMap 2 (seventeenPoint H i)) = 0
      exact atomicOrder_zero _ _ _ (seventeenPoint_two_absent H i ht)
  | some j =>
      change atomicOrder (seventeenPoint H) (seventeenRootMultiplicity M)
        (powerMap 2 (seventeenPoint H i)) = seventeenRootMultiplicity M j
      rw [seventeenPoint_two_of_target H i j ht]
      exact atomicOrder_at _ _ (seventeenPoint_injective H) j

theorem seventeenRootSpectrum_four_order (H : Real) (hH : 0 < H) (M : Nat)
    (hM : M = 5 \/ M = 6) (i : Fin 17) :
    (seventeenRootSpectrum H hH M hM).rowOrder 4 i =
      (seventeenFourTarget i).elim 0 (seventeenRootMultiplicity M) := by
  cases ht : seventeenFourTarget i with
  | none =>
      change atomicOrder (seventeenPoint H) (seventeenRootMultiplicity M)
        (powerMap 4 (seventeenPoint H i)) = 0
      exact atomicOrder_zero _ _ _ (seventeenPoint_four_absent H i ht)
  | some j =>
      change atomicOrder (seventeenPoint H) (seventeenRootMultiplicity M)
        (powerMap 4 (seventeenPoint H i)) = seventeenRootMultiplicity M j
      rw [seventeenPoint_four_of_target H i j ht]
      exact atomicOrder_at _ _ (seventeenPoint_injective H) j

theorem seventeenRootSpectrum_weak_iff (H : Real) (hH : 0 < H) (M : Nat)
    (hM : M = 5 \/ M = 6) (i : Fin 17) :
    Membership.mem (seventeenRootSpectrum H hH M hM).weakIndices i <->
      i = 0 \/ i = 1 \/ i = 3 \/ i = 5 := by
  classical
  rw [ReflectedSpectrum.weakIndices, Finset.mem_filter]
  simp only [Finset.mem_univ, true_and]
  rw [seventeenRootSpectrum_two_order, seventeenRootSpectrum_four_order]
  change ((seventeenRootMultiplicity M i : Real) <=
      2 * (((seventeenTwoTarget i).elim 0 (seventeenRootMultiplicity M) : Nat) : Real) /\
    (seventeenRootMultiplicity M i : Real) <=
      4 * (((seventeenFourTarget i).elim 0 (seventeenRootMultiplicity M) : Nat) : Real)) <->
        i = 0 \/ i = 1 \/ i = 3 \/ i = 5
  rcases hM with hM | hM <;> fin_cases i <;>
    norm_num [seventeenRootMultiplicity, seventeenMultiplicity, seventeenTwoTarget,
      seventeenFourTarget, hM]

theorem seventeenRootSpectrum_weakIndices (H : Real) (hH : 0 < H) (M : Nat)
    (hM : M = 5 \/ M = 6) :
    (seventeenRootSpectrum H hH M hM).weakIndices = {0, 1, 3, 5} := by
  classical
  apply Finset.ext
  intro i
  rw [seventeenRootSpectrum_weak_iff]
  simp only [Finset.mem_insert, Finset.mem_singleton]

theorem seventeenRootSpectrum_totalMass (H : Real) (hH : 0 < H) (M : Nat)
    (hM : M = 5 \/ M = 6) :
    (seventeenRootSpectrum H hH M hM).totalMass = (1560 + M) / H ^ 2 := by
  change Finset.univ.sum (fun i : Fin 17 =>
    (seventeenRootMultiplicity M i : Real) / (seventeenPoint H i).im ^ 2) = _
  norm_num [Fin.sum_univ_succ, seventeenRootMultiplicity, seventeenMultiplicity,
    seventeenPoint, seventeenHeightDenominator]
  field_simp [hH.ne']
  ring

theorem seventeenRootSpectrum_weakMass (H : Real) (hH : 0 < H) (M : Nat)
    (hM : M = 5 \/ M = 6) :
    (seventeenRootSpectrum H hH M hM).weakMass = (76 + M) / H ^ 2 := by
  unfold ReflectedSpectrum.weakMass
  rw [seventeenRootSpectrum_weakIndices]
  norm_num [ReflectedSpectrum.mass, seventeenRootSpectrum, seventeenRootMultiplicity,
    seventeenSpectrum, seventeenPoint, seventeenHeightDenominator, seventeenMultiplicity]
  field_simp [hH.ne']
  ring

theorem seventeenRootSpectrum_weakUnitMass (H : Real) (hH : 0 < H) (M : Nat)
    (hM : M = 5 \/ M = 6) :
    (seventeenRootSpectrum H hH M hM).weakUnitMass = 37 / H ^ 2 := by
  unfold ReflectedSpectrum.weakUnitMass
  rw [seventeenRootSpectrum_weakIndices]
  norm_num [ReflectedSpectrum.unitMass, seventeenRootSpectrum, seventeenSpectrum,
    seventeenPoint, seventeenHeightDenominator]
  field_simp [hH.ne']
  ring

theorem seventeenRootSpectrum_weakRepeatedUnitMass (H : Real) (hH : 0 < H) (M : Nat)
    (hM : M = 5 \/ M = 6) :
    (seventeenRootSpectrum H hH M hM).weakRepeatedUnitMass = 37 / H ^ 2 := by
  unfold ReflectedSpectrum.weakRepeatedUnitMass
  rw [seventeenRootSpectrum_weakIndices]
  rcases hM with hM | hM <;>
    norm_num [ReflectedSpectrum.repeatedUnitAt, ReflectedSpectrum.unitMass,
      seventeenRootSpectrum, seventeenSpectrum, seventeenRootMultiplicity,
      seventeenPoint, seventeenHeightDenominator, seventeenMultiplicity, hM] <;>
    field_simp [hH.ne'] <;> ring

theorem seventeenRootSpectrum_weakFifthUnitMass (H : Real) (hH : 0 < H) (M : Nat)
    (hM : M = 5 \/ M = 6) :
    (seventeenRootSpectrum H hH M hM).weakFifthUnitMass = 1 / H ^ 2 := by
  unfold ReflectedSpectrum.weakFifthUnitMass
  rw [seventeenRootSpectrum_weakIndices]
  rcases hM with hM | hM <;>
    norm_num [ReflectedSpectrum.fifthUnitAt, ReflectedSpectrum.unitMass,
      seventeenRootSpectrum, seventeenSpectrum, seventeenRootMultiplicity,
      seventeenPoint, seventeenHeightDenominator, seventeenMultiplicity, hM]

theorem seventeenRootSpectrum_carrierMass (H : Real) (hH : 0 < H) (M : Nat)
    (hM : M = 5 \/ M = 6) :
    (seventeenRootSpectrum H hH M hM).carrierMass = 1484 / H ^ 2 := by
  have h := (seventeenRootSpectrum H hH M hM).totalMass_eq_weakMass_add_carrierMass
  rw [seventeenRootSpectrum_totalMass, seventeenRootSpectrum_weakMass] at h
  calc
    _ = (1560 + M) / H ^ 2 - (76 + M) / H ^ 2 := by linarith
    _ = 1484 / H ^ 2 := by ring

theorem seventeenRootSpectrum_fifth_equality (H : Real) (hH : 0 < H) (M : Nat)
    (hM : M = 5 \/ M = 6) :
    (seventeenRootSpectrum H hH M hM).carrierMass =
      39 * (seventeenRootSpectrum H hH M hM).weakUnitMass +
      (seventeenRootSpectrum H hH M hM).weakRepeatedUnitMass +
      4 * (seventeenRootSpectrum H hH M hM).weakFifthUnitMass := by
  rw [seventeenRootSpectrum_carrierMass, seventeenRootSpectrum_weakUnitMass,
    seventeenRootSpectrum_weakRepeatedUnitMass, seventeenRootSpectrum_weakFifthUnitMass]
  ring

theorem seventeenRootSpectrum_weakFifthUnitMass_pos (H : Real) (hH : 0 < H) (M : Nat)
    (hM : M = 5 \/ M = 6) :
    0 < (seventeenRootSpectrum H hH M hM).weakFifthUnitMass := by
  rw [seventeenRootSpectrum_weakFifthUnitMass]
  exact div_pos (by norm_num) (pow_pos hH 2)

end PrimeFactorOscillations.CarmichaelDyadicSharpness


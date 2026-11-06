/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Assembly.CarmichaelTailTables

/-!
# Complete actual reference rows of the two tail extremizers

Every present quadratic/quartic target and every absent target is certified.
The common-weak supports are exactly{0,3} and{0,1,5}.
-/

set_option autoImplicit false
set_option Elab.async false

noncomputable section

namespace PrimeFactorOscillations.CarmichaelDyadicSharpness

open DirichletCompensatedProbe CarmichaelWeightedSignal CarmichaelTraceSharpness

theorem tailNinePoint_two_of_target (H : Real) (i j : Fin 9)
    (h : tailNineTwoTarget i = some j) :
    powerMap 2 (tailNinePoint H i) = tailNinePoint H j := by
  have hc := (tailNineTwoTarget_iff i j).mp h
  have hcr : (2 : Real) * (tailNineRealCode j : Real) =
      (tailNineRealCode i : Real) + 64 := by exact_mod_cast hc
  have hd := tailNineTwoTarget_height i j h
  have hdr : (tailNineHeightDenominator j : Real) =
      2 * (tailNineHeightDenominator i : Real) := by exact_mod_cast hd
  have hz : Not ((tailNineHeightDenominator i : Real) = 0) := by
    exact_mod_cast (Nat.ne_of_gt (tailNineHeightDenominator_pos i))
  apply Complex.ext
  . rw [tailNinePoint_power_re H 2 (by norm_num)]
    change ((tailNineRealCode i : Real) / 64 + 2 - 1) / 2 =
      (tailNineRealCode j : Real) / 64
    linarith
  . rw [tailNinePoint_power_im H 2 (by norm_num)]
    change (H / (tailNineHeightDenominator i : Real)) / 2 =
      H / (tailNineHeightDenominator j : Real)
    rw [hdr]
    field_simp [hz] <;> ring

theorem tailNinePoint_four_of_target (H : Real) (i j : Fin 9)
    (h : tailNineFourTarget i = some j) :
    powerMap 4 (tailNinePoint H i) = tailNinePoint H j := by
  have hc := (tailNineFourTarget_iff i j).mp h
  have hcr : (4 : Real) * (tailNineRealCode j : Real) =
      (tailNineRealCode i : Real) + 192 := by exact_mod_cast hc
  have hd := tailNineFourTarget_height i j h
  have hdr : (tailNineHeightDenominator j : Real) =
      4 * (tailNineHeightDenominator i : Real) := by exact_mod_cast hd
  have hz : Not ((tailNineHeightDenominator i : Real) = 0) := by
    exact_mod_cast (Nat.ne_of_gt (tailNineHeightDenominator_pos i))
  apply Complex.ext
  . rw [tailNinePoint_power_re H 4 (by norm_num)]
    change ((tailNineRealCode i : Real) / 64 + 4 - 1) / 4 =
      (tailNineRealCode j : Real) / 64
    linarith
  . rw [tailNinePoint_power_im H 4 (by norm_num)]
    change (H / (tailNineHeightDenominator i : Real)) / 4 =
      H / (tailNineHeightDenominator j : Real)
    rw [hdr]
    field_simp [hz] <;> ring

theorem tailNinePoint_two_absent (H : Real) (i : Fin 9)
    (h : tailNineTwoTarget i = none) :
    forall j : Fin 9, Not (tailNinePoint H j = powerMap 2 (tailNinePoint H i)) := by
  intro j hj
  have he := congrArg Complex.re hj
  rw [tailNinePoint_power_re H 2 (by norm_num)] at he
  change (tailNineRealCode j : Real) / 64 =
    ((tailNineRealCode i : Real) / 64 + 2 - 1) / 2 at he
  have hcr : (2 : Real) * (tailNineRealCode j : Real) =
      (tailNineRealCode i : Real) + 64 := by linarith
  have hc : 2 * tailNineRealCode j = tailNineRealCode i + 64 := by exact_mod_cast hcr
  have ht := (tailNineTwoTarget_iff i j).mpr hc
  rw [h] at ht
  cases ht

theorem tailNinePoint_four_absent (H : Real) (i : Fin 9)
    (h : tailNineFourTarget i = none) :
    forall j : Fin 9, Not (tailNinePoint H j = powerMap 4 (tailNinePoint H i)) := by
  intro j hj
  have he := congrArg Complex.re hj
  rw [tailNinePoint_power_re H 4 (by norm_num)] at he
  change (tailNineRealCode j : Real) / 64 =
    ((tailNineRealCode i : Real) / 64 + 4 - 1) / 4 at he
  have hcr : (4 : Real) * (tailNineRealCode j : Real) =
      (tailNineRealCode i : Real) + 192 := by linarith
  have hc : 4 * tailNineRealCode j = tailNineRealCode i + 192 := by exact_mod_cast hcr
  have ht := (tailNineFourTarget_iff i j).mpr hc
  rw [h] at ht
  cases ht

theorem tailNineSpectrum_two_order (H : Real) (hH : 0 < H) (i : Fin 9) :
    (tailNineSpectrum H hH).rowOrder 2 i =
      (tailNineTwoTarget i).elim 0 tailNineMultiplicity := by
  cases ht : tailNineTwoTarget i with
  | none =>
      change atomicOrder (tailNinePoint H) tailNineMultiplicity
        (powerMap 2 (tailNinePoint H i)) = 0
      exact atomicOrder_zero _ _ _ (tailNinePoint_two_absent H i ht)
  | some j =>
      change atomicOrder (tailNinePoint H) tailNineMultiplicity
        (powerMap 2 (tailNinePoint H i)) = tailNineMultiplicity j
      rw [tailNinePoint_two_of_target H i j ht]
      exact atomicOrder_at _ _ (tailNinePoint_injective H) j

theorem tailNineSpectrum_four_order (H : Real) (hH : 0 < H) (i : Fin 9) :
    (tailNineSpectrum H hH).rowOrder 4 i =
      (tailNineFourTarget i).elim 0 tailNineMultiplicity := by
  cases ht : tailNineFourTarget i with
  | none =>
      change atomicOrder (tailNinePoint H) tailNineMultiplicity
        (powerMap 4 (tailNinePoint H i)) = 0
      exact atomicOrder_zero _ _ _ (tailNinePoint_four_absent H i ht)
  | some j =>
      change atomicOrder (tailNinePoint H) tailNineMultiplicity
        (powerMap 4 (tailNinePoint H i)) = tailNineMultiplicity j
      rw [tailNinePoint_four_of_target H i j ht]
      exact atomicOrder_at _ _ (tailNinePoint_injective H) j

theorem tailNineSpectrum_weak_iff (H : Real) (hH : 0 < H) (i : Fin 9) :
    Membership.mem (tailNineSpectrum H hH).weakIndices i <->
      i = 0 \/ i = 3 := by
  classical
  rw [ReflectedSpectrum.weakIndices, Finset.mem_filter]
  simp only [Finset.mem_univ, true_and]
  rw [tailNineSpectrum_two_order, tailNineSpectrum_four_order]
  change ((tailNineMultiplicity i : Real) <=
      2 * (((tailNineTwoTarget i).elim 0 tailNineMultiplicity : Nat) : Real) /\
    (tailNineMultiplicity i : Real) <=
      4 * (((tailNineFourTarget i).elim 0 tailNineMultiplicity : Nat) : Real)) <->
        i = 0 \/ i = 3
  fin_cases i <;> norm_num [tailNineMultiplicity, tailNineTwoTarget, tailNineFourTarget]

theorem tailNineSpectrum_weakIndices (H : Real) (hH : 0 < H) :
    (tailNineSpectrum H hH).weakIndices = {0, 3} := by
  classical
  apply Finset.ext
  intro i
  rw [tailNineSpectrum_weak_iff]
  simp only [Finset.mem_insert, Finset.mem_singleton]

theorem tailThirteenPoint_two_of_target (H : Real) (i j : Fin 13)
    (h : tailThirteenTwoTarget i = some j) :
    powerMap 2 (tailThirteenPoint H i) = tailThirteenPoint H j := by
  have hc := (tailThirteenTwoTarget_iff i j).mp h
  have hcr : (2 : Real) * (tailThirteenRealCode j : Real) =
      (tailThirteenRealCode i : Real) + 64 := by exact_mod_cast hc
  have hd := tailThirteenTwoTarget_height i j h
  have hdr : (tailThirteenHeightDenominator j : Real) =
      2 * (tailThirteenHeightDenominator i : Real) := by exact_mod_cast hd
  have hz : Not ((tailThirteenHeightDenominator i : Real) = 0) := by
    exact_mod_cast (Nat.ne_of_gt (tailThirteenHeightDenominator_pos i))
  apply Complex.ext
  . rw [tailThirteenPoint_power_re H 2 (by norm_num)]
    change ((tailThirteenRealCode i : Real) / 64 + 2 - 1) / 2 =
      (tailThirteenRealCode j : Real) / 64
    linarith
  . rw [tailThirteenPoint_power_im H 2 (by norm_num)]
    change (H / (tailThirteenHeightDenominator i : Real)) / 2 =
      H / (tailThirteenHeightDenominator j : Real)
    rw [hdr]
    field_simp [hz] <;> ring

theorem tailThirteenPoint_four_of_target (H : Real) (i j : Fin 13)
    (h : tailThirteenFourTarget i = some j) :
    powerMap 4 (tailThirteenPoint H i) = tailThirteenPoint H j := by
  have hc := (tailThirteenFourTarget_iff i j).mp h
  have hcr : (4 : Real) * (tailThirteenRealCode j : Real) =
      (tailThirteenRealCode i : Real) + 192 := by exact_mod_cast hc
  have hd := tailThirteenFourTarget_height i j h
  have hdr : (tailThirteenHeightDenominator j : Real) =
      4 * (tailThirteenHeightDenominator i : Real) := by exact_mod_cast hd
  have hz : Not ((tailThirteenHeightDenominator i : Real) = 0) := by
    exact_mod_cast (Nat.ne_of_gt (tailThirteenHeightDenominator_pos i))
  apply Complex.ext
  . rw [tailThirteenPoint_power_re H 4 (by norm_num)]
    change ((tailThirteenRealCode i : Real) / 64 + 4 - 1) / 4 =
      (tailThirteenRealCode j : Real) / 64
    linarith
  . rw [tailThirteenPoint_power_im H 4 (by norm_num)]
    change (H / (tailThirteenHeightDenominator i : Real)) / 4 =
      H / (tailThirteenHeightDenominator j : Real)
    rw [hdr]
    field_simp [hz] <;> ring

theorem tailThirteenPoint_two_absent (H : Real) (i : Fin 13)
    (h : tailThirteenTwoTarget i = none) :
    forall j : Fin 13, Not (tailThirteenPoint H j = powerMap 2 (tailThirteenPoint H i)) := by
  intro j hj
  have he := congrArg Complex.re hj
  rw [tailThirteenPoint_power_re H 2 (by norm_num)] at he
  change (tailThirteenRealCode j : Real) / 64 =
    ((tailThirteenRealCode i : Real) / 64 + 2 - 1) / 2 at he
  have hcr : (2 : Real) * (tailThirteenRealCode j : Real) =
      (tailThirteenRealCode i : Real) + 64 := by linarith
  have hc : 2 * tailThirteenRealCode j = tailThirteenRealCode i + 64 := by exact_mod_cast hcr
  have ht := (tailThirteenTwoTarget_iff i j).mpr hc
  rw [h] at ht
  cases ht

theorem tailThirteenPoint_four_absent (H : Real) (i : Fin 13)
    (h : tailThirteenFourTarget i = none) :
    forall j : Fin 13, Not (tailThirteenPoint H j = powerMap 4 (tailThirteenPoint H i)) := by
  intro j hj
  have he := congrArg Complex.re hj
  rw [tailThirteenPoint_power_re H 4 (by norm_num)] at he
  change (tailThirteenRealCode j : Real) / 64 =
    ((tailThirteenRealCode i : Real) / 64 + 4 - 1) / 4 at he
  have hcr : (4 : Real) * (tailThirteenRealCode j : Real) =
      (tailThirteenRealCode i : Real) + 192 := by linarith
  have hc : 4 * tailThirteenRealCode j = tailThirteenRealCode i + 192 := by exact_mod_cast hcr
  have ht := (tailThirteenFourTarget_iff i j).mpr hc
  rw [h] at ht
  cases ht

theorem tailThirteenSpectrum_two_order (H : Real) (hH : 0 < H) (i : Fin 13) :
    (tailThirteenSpectrum H hH).rowOrder 2 i =
      (tailThirteenTwoTarget i).elim 0 tailThirteenMultiplicity := by
  cases ht : tailThirteenTwoTarget i with
  | none =>
      change atomicOrder (tailThirteenPoint H) tailThirteenMultiplicity
        (powerMap 2 (tailThirteenPoint H i)) = 0
      exact atomicOrder_zero _ _ _ (tailThirteenPoint_two_absent H i ht)
  | some j =>
      change atomicOrder (tailThirteenPoint H) tailThirteenMultiplicity
        (powerMap 2 (tailThirteenPoint H i)) = tailThirteenMultiplicity j
      rw [tailThirteenPoint_two_of_target H i j ht]
      exact atomicOrder_at _ _ (tailThirteenPoint_injective H) j

theorem tailThirteenSpectrum_four_order (H : Real) (hH : 0 < H) (i : Fin 13) :
    (tailThirteenSpectrum H hH).rowOrder 4 i =
      (tailThirteenFourTarget i).elim 0 tailThirteenMultiplicity := by
  cases ht : tailThirteenFourTarget i with
  | none =>
      change atomicOrder (tailThirteenPoint H) tailThirteenMultiplicity
        (powerMap 4 (tailThirteenPoint H i)) = 0
      exact atomicOrder_zero _ _ _ (tailThirteenPoint_four_absent H i ht)
  | some j =>
      change atomicOrder (tailThirteenPoint H) tailThirteenMultiplicity
        (powerMap 4 (tailThirteenPoint H i)) = tailThirteenMultiplicity j
      rw [tailThirteenPoint_four_of_target H i j ht]
      exact atomicOrder_at _ _ (tailThirteenPoint_injective H) j

theorem tailThirteenSpectrum_weak_iff (H : Real) (hH : 0 < H) (i : Fin 13) :
    Membership.mem (tailThirteenSpectrum H hH).weakIndices i <->
      i = 0 \/ i = 1 \/ i = 5 := by
  classical
  rw [ReflectedSpectrum.weakIndices, Finset.mem_filter]
  simp only [Finset.mem_univ, true_and]
  rw [tailThirteenSpectrum_two_order, tailThirteenSpectrum_four_order]
  change ((tailThirteenMultiplicity i : Real) <=
      2 * (((tailThirteenTwoTarget i).elim 0 tailThirteenMultiplicity : Nat) : Real) /\
    (tailThirteenMultiplicity i : Real) <=
      4 * (((tailThirteenFourTarget i).elim 0 tailThirteenMultiplicity : Nat) : Real)) <->
        i = 0 \/ i = 1 \/ i = 5
  fin_cases i <;> norm_num [tailThirteenMultiplicity, tailThirteenTwoTarget, tailThirteenFourTarget]

theorem tailThirteenSpectrum_weakIndices (H : Real) (hH : 0 < H) :
    (tailThirteenSpectrum H hH).weakIndices = {0, 1, 5} := by
  classical
  apply Finset.ext
  intro i
  rw [tailThirteenSpectrum_weak_iff]
  simp only [Finset.mem_insert, Finset.mem_singleton]

end PrimeFactorOscillations.CarmichaelDyadicSharpness

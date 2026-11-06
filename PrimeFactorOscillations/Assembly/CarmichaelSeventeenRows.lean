/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Assembly.CarmichaelSeventeenSpectrum

/-!
# Actual reference ownership and full readouts of the seventeen-point model

The integer-coordinate ownership certificates evaluate every actual row.
Right quadratic collisions remain present. All other references are proved
absent; no reference-nonvanishing or simple-zero assumption is inserted.
-/

set_option autoImplicit false
set_option Elab.async false

noncomputable section

namespace PrimeFactorOscillations.CarmichaelDyadicSharpness

open DirichletCompensatedProbe CarmichaelWeightedSignal CarmichaelTraceSharpness

theorem seventeenPoint_two_of_target (H : Real) (i j : Fin 17)
    (h : seventeenTwoTarget i = some j) :
    powerMap 2 (seventeenPoint H i) = seventeenPoint H j := by
  have hc := (seventeenTwoTarget_iff i j).mp h
  have hcr : (2 : Real) * (seventeenRealCode j : Real) =
      (seventeenRealCode i : Real) + 64 := by exact_mod_cast hc
  have hd := seventeenTwoTarget_height i j h
  have hdr : (seventeenHeightDenominator j : Real) =
      2 * (seventeenHeightDenominator i : Real) := by exact_mod_cast hd
  have hz : Not ((seventeenHeightDenominator i : Real) = 0) := by
    exact_mod_cast (Nat.ne_of_gt (seventeenHeightDenominator_pos i))
  apply Complex.ext
  . rw [seventeenPoint_power_re H 2 (by norm_num)]
    change ((seventeenRealCode i : Real) / 64 + 2 - 1) / 2 =
      (seventeenRealCode j : Real) / 64
    linarith
  . rw [seventeenPoint_power_im H 2 (by norm_num)]
    change (H / (seventeenHeightDenominator i : Real)) / 2 =
      H / (seventeenHeightDenominator j : Real)
    rw [hdr]
    field_simp [hz] <;> ring

theorem seventeenPoint_four_of_target (H : Real) (i j : Fin 17)
    (h : seventeenFourTarget i = some j) :
    powerMap 4 (seventeenPoint H i) = seventeenPoint H j := by
  have hc := (seventeenFourTarget_iff i j).mp h
  have hcr : (4 : Real) * (seventeenRealCode j : Real) =
      (seventeenRealCode i : Real) + 192 := by exact_mod_cast hc
  have hd := seventeenFourTarget_height i j h
  have hdr : (seventeenHeightDenominator j : Real) =
      4 * (seventeenHeightDenominator i : Real) := by exact_mod_cast hd
  have hz : Not ((seventeenHeightDenominator i : Real) = 0) := by
    exact_mod_cast (Nat.ne_of_gt (seventeenHeightDenominator_pos i))
  apply Complex.ext
  . rw [seventeenPoint_power_re H 4 (by norm_num)]
    change ((seventeenRealCode i : Real) / 64 + 4 - 1) / 4 =
      (seventeenRealCode j : Real) / 64
    linarith
  . rw [seventeenPoint_power_im H 4 (by norm_num)]
    change (H / (seventeenHeightDenominator i : Real)) / 4 =
      H / (seventeenHeightDenominator j : Real)
    rw [hdr]
    field_simp [hz] <;> ring

theorem seventeenPoint_two_absent (H : Real) (i : Fin 17)
    (h : seventeenTwoTarget i = none) :
    forall j : Fin 17, Not (seventeenPoint H j = powerMap 2 (seventeenPoint H i)) := by
  intro j hj
  have he := congrArg Complex.re hj
  rw [seventeenPoint_power_re H 2 (by norm_num)] at he
  change (seventeenRealCode j : Real) / 64 =
    ((seventeenRealCode i : Real) / 64 + 2 - 1) / 2 at he
  have hcr : (2 : Real) * (seventeenRealCode j : Real) =
      (seventeenRealCode i : Real) + 64 := by linarith
  have hc : 2 * seventeenRealCode j = seventeenRealCode i + 64 := by exact_mod_cast hcr
  have ht := (seventeenTwoTarget_iff i j).mpr hc
  rw [h] at ht
  cases ht

theorem seventeenPoint_four_absent (H : Real) (i : Fin 17)
    (h : seventeenFourTarget i = none) :
    forall j : Fin 17, Not (seventeenPoint H j = powerMap 4 (seventeenPoint H i)) := by
  intro j hj
  have he := congrArg Complex.re hj
  rw [seventeenPoint_power_re H 4 (by norm_num)] at he
  change (seventeenRealCode j : Real) / 64 =
    ((seventeenRealCode i : Real) / 64 + 4 - 1) / 4 at he
  have hcr : (4 : Real) * (seventeenRealCode j : Real) =
      (seventeenRealCode i : Real) + 192 := by linarith
  have hc : 4 * seventeenRealCode j = seventeenRealCode i + 192 := by exact_mod_cast hcr
  have ht := (seventeenFourTarget_iff i j).mpr hc
  rw [h] at ht
  cases ht

theorem seventeenSpectrum_two_order (H : Real) (hH : 0 < H) (i : Fin 17) :
    (seventeenSpectrum H hH).rowOrder 2 i =
      (seventeenTwoTarget i).elim 0 seventeenMultiplicity := by
  cases ht : seventeenTwoTarget i with
  | none =>
      change atomicOrder (seventeenPoint H) seventeenMultiplicity
        (powerMap 2 (seventeenPoint H i)) = 0
      exact atomicOrder_zero _ _ _ (seventeenPoint_two_absent H i ht)
  | some j =>
      change atomicOrder (seventeenPoint H) seventeenMultiplicity
        (powerMap 2 (seventeenPoint H i)) = seventeenMultiplicity j
      rw [seventeenPoint_two_of_target H i j ht]
      exact atomicOrder_at _ _ (seventeenPoint_injective H) j

theorem seventeenSpectrum_four_order (H : Real) (hH : 0 < H) (i : Fin 17) :
    (seventeenSpectrum H hH).rowOrder 4 i =
      (seventeenFourTarget i).elim 0 seventeenMultiplicity := by
  cases ht : seventeenFourTarget i with
  | none =>
      change atomicOrder (seventeenPoint H) seventeenMultiplicity
        (powerMap 4 (seventeenPoint H i)) = 0
      exact atomicOrder_zero _ _ _ (seventeenPoint_four_absent H i ht)
  | some j =>
      change atomicOrder (seventeenPoint H) seventeenMultiplicity
        (powerMap 4 (seventeenPoint H i)) = seventeenMultiplicity j
      rw [seventeenPoint_four_of_target H i j ht]
      exact atomicOrder_at _ _ (seventeenPoint_injective H) j

theorem seventeenSpectrum_weak_iff (H : Real) (hH : 0 < H) (i : Fin 17) :
    Membership.mem (seventeenSpectrum H hH).weakIndices i <->
      i = 0 \/ i = 1 \/ i = 3 \/ i = 5 := by
  classical
  rw [ReflectedSpectrum.weakIndices, Finset.mem_filter]
  simp only [Finset.mem_univ, true_and]
  rw [seventeenSpectrum_two_order, seventeenSpectrum_four_order]
  change ((seventeenMultiplicity i : Real) <=
      2 * (((seventeenTwoTarget i).elim 0 seventeenMultiplicity : Nat) : Real) /\
    (seventeenMultiplicity i : Real) <=
      4 * (((seventeenFourTarget i).elim 0 seventeenMultiplicity : Nat) : Real)) <->
        i = 0 \/ i = 1 \/ i = 3 \/ i = 5
  fin_cases i <;> norm_num [seventeenMultiplicity, seventeenTwoTarget, seventeenFourTarget]

theorem seventeenSpectrum_weakIndices (H : Real) (hH : 0 < H) :
    (seventeenSpectrum H hH).weakIndices = {0, 1, 3, 5} := by
  classical
  apply Finset.ext
  intro i
  rw [seventeenSpectrum_weak_iff]
  simp only [Finset.mem_insert, Finset.mem_singleton]

theorem seventeenSpectrum_den_ne (H : Real) (hH : 0 < H) (d : Real) (i : Fin 17) :
    Not ((seventeenSpectrum H hH).point i + (d : Complex) - 1 = 0) := by
  intro hz
  have he := congrArg Complex.im hz
  simp only [Complex.sub_im, Complex.add_im, Complex.ofReal_im, Complex.one_im,
    Complex.zero_im, add_zero, sub_zero] at he
  exact (ne_of_gt ((seventeenSpectrum H hH).im_pos i)) he

theorem seventeenSpectrum_full_residue_ne_zero (H : Real) (hH : 0 < H)
    (d : Real) (hd : 1 < d) (i : Fin 17) :
    Not (atomicPowerResidue (seventeenSpectrum H hH).point
      (seventeenSpectrum H hH).mult d ((seventeenSpectrum H hH).point i) = 0) := by
  apply atomicPowerResidue_ne_zero _ _ d hd _
    (ne_of_gt ((seventeenSpectrum H hH).im_pos i)) (seventeenSpectrum_den_ne H hH d i)
  rw [atomicOrder_at _ _ (seventeenSpectrum H hH).point_injective i]
  exact (seventeenSpectrum H hH).mult_pos i

theorem seventeenSpectrum_readout_scaled_limit (H : Real) (hH : 0 < H)
    (d : Real) (hd : 0 < d) (i : Fin 17) :
    Filter.Tendsto
      (fun s => (s - (seventeenSpectrum H hH).point i) *
        affinePowerReadout
          (atomicReadout (seventeenSpectrum H hH).point (seventeenSpectrum H hH).mult) d s)
      (nhdsWithin ((seventeenSpectrum H hH).point i)
        (Set.compl {(seventeenSpectrum H hH).point i}))
      (nhds (atomicPowerResidue (seventeenSpectrum H hH).point
        (seventeenSpectrum H hH).mult d ((seventeenSpectrum H hH).point i))) := by
  exact atomicPower_scaled_limit _ _ d hd _ (seventeenSpectrum_den_ne H hH d i)

theorem seventeenSpectrum_projection_negative_iff (H : Real) (hH : 0 < H)
    (d : Real) (i : Fin 17) :
    (atomicPowerResidue (seventeenSpectrum H hH).point (seventeenSpectrum H hH).mult d
        ((seventeenSpectrum H hH).point i) *
      ((seventeenSpectrum H hH).point i + (d : Complex) - 1)).im < 0 <->
      d * ((seventeenSpectrum H hH).rowOrder d i : Real) <
        ((seventeenSpectrum H hH).mult i : Real) := by
  let S := seventeenSpectrum H hH
  have h := atomicPower_projection S.point S.mult d (S.point i)
    (seventeenSpectrum_den_ne H hH d i)
  rw [atomicOrder_at _ _ S.point_injective i] at h
  change (atomicPowerResidue S.point S.mult d (S.point i) *
      (S.point i + (d : Complex) - 1)).im =
    (d * (S.rowOrder d i : Real) - (S.mult i : Real)) * (S.point i).im at h
  rw [h]
  constructor
  . intro hNeg
    by_contra hn
    have hNonneg := mul_nonneg (sub_nonneg.mpr (le_of_not_gt hn)) (S.im_pos i).le
    exact (not_lt_of_ge hNonneg) hNeg
  . intro hNeg
    exact mul_neg_of_neg_of_pos (sub_neg.mpr hNeg) (S.im_pos i)

end PrimeFactorOscillations.CarmichaelDyadicSharpness

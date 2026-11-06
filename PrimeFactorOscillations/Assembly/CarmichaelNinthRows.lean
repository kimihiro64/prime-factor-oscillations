/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Assembly.CarmichaelNinthTables

/-!
# Every actual reference row of the ninth-tail extremizer

The real and height tables determine every row, every absent reference and
the exact seven-element common-weak set. Full compensated limits and signs
retain both target and reference orders.
-/

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 4000000

noncomputable section

namespace PrimeFactorOscillations.CarmichaelDyadicSharpness

open DirichletCompensatedProbe CarmichaelWeightedSignal CarmichaelTraceSharpness

theorem ninthPoint_two_of_target (H : Real) (i j : Fin 29)
    (h : ninthTwoTarget i = some j) :
    powerMap 2 (ninthPoint H i) = ninthPoint H j := by
  have hc := (ninthTwoTarget_iff i j).mp h
  have hcr : (2 : Real) * (ninthRealCode j : Real) =
      (ninthRealCode i : Real) + 128 := by exact_mod_cast hc
  have hd := ninthTwoTarget_height i j h
  have hdr : (ninthHeightDenominator j : Real) =
      2 * (ninthHeightDenominator i : Real) := by exact_mod_cast hd
  have hz : Not ((ninthHeightDenominator i : Real) = 0) := by
    exact_mod_cast (Nat.ne_of_gt (ninthHeightDenominator_pos i))
  apply Complex.ext
  . rw [ninthPoint_power_re H 2 (by norm_num)]
    change ((ninthRealCode i : Real) / 128 + 2 - 1) / 2 =
      (ninthRealCode j : Real) / 128
    linarith
  . rw [ninthPoint_power_im H 2 (by norm_num)]
    change (H / (ninthHeightDenominator i : Real)) / 2 =
      H / (ninthHeightDenominator j : Real)
    rw [hdr]
    field_simp [hz] <;> ring

theorem ninthPoint_four_of_target (H : Real) (i j : Fin 29)
    (h : ninthFourTarget i = some j) :
    powerMap 4 (ninthPoint H i) = ninthPoint H j := by
  have hc := (ninthFourTarget_iff i j).mp h
  have hcr : (4 : Real) * (ninthRealCode j : Real) =
      (ninthRealCode i : Real) + 384 := by exact_mod_cast hc
  have hd := ninthFourTarget_height i j h
  have hdr : (ninthHeightDenominator j : Real) =
      4 * (ninthHeightDenominator i : Real) := by exact_mod_cast hd
  have hz : Not ((ninthHeightDenominator i : Real) = 0) := by
    exact_mod_cast (Nat.ne_of_gt (ninthHeightDenominator_pos i))
  apply Complex.ext
  . rw [ninthPoint_power_re H 4 (by norm_num)]
    change ((ninthRealCode i : Real) / 128 + 4 - 1) / 4 =
      (ninthRealCode j : Real) / 128
    linarith
  . rw [ninthPoint_power_im H 4 (by norm_num)]
    change (H / (ninthHeightDenominator i : Real)) / 4 =
      H / (ninthHeightDenominator j : Real)
    rw [hdr]
    field_simp [hz] <;> ring

theorem ninthPoint_two_absent (H : Real) (i : Fin 29)
    (h : ninthTwoTarget i = none) :
    forall j : Fin 29, Not (ninthPoint H j = powerMap 2 (ninthPoint H i)) := by
  intro j hj
  have he := congrArg Complex.re hj
  rw [ninthPoint_power_re H 2 (by norm_num)] at he
  change (ninthRealCode j : Real) / 128 =
    ((ninthRealCode i : Real) / 128 + 2 - 1) / 2 at he
  have hcr : (2 : Real) * (ninthRealCode j : Real) =
      (ninthRealCode i : Real) + 128 := by linarith
  have hc : 2 * ninthRealCode j = ninthRealCode i + 128 := by exact_mod_cast hcr
  have ht := (ninthTwoTarget_iff i j).mpr hc
  rw [h] at ht
  cases ht

theorem ninthPoint_four_absent (H : Real) (i : Fin 29)
    (h : ninthFourTarget i = none) :
    forall j : Fin 29, Not (ninthPoint H j = powerMap 4 (ninthPoint H i)) := by
  intro j hj
  have he := congrArg Complex.re hj
  rw [ninthPoint_power_re H 4 (by norm_num)] at he
  change (ninthRealCode j : Real) / 128 =
    ((ninthRealCode i : Real) / 128 + 4 - 1) / 4 at he
  have hcr : (4 : Real) * (ninthRealCode j : Real) =
      (ninthRealCode i : Real) + 384 := by linarith
  have hc : 4 * ninthRealCode j = ninthRealCode i + 384 := by exact_mod_cast hcr
  have ht := (ninthFourTarget_iff i j).mpr hc
  rw [h] at ht
  cases ht

theorem ninthSpectrum_two_order (H : Real) (hH : 0 < H) (i : Fin 29) :
    (ninthSpectrum H hH).rowOrder 2 i =
      (ninthTwoTarget i).elim 0 ninthMultiplicity := by
  cases ht : ninthTwoTarget i with
  | none =>
      change atomicOrder (ninthPoint H) ninthMultiplicity
        (powerMap 2 (ninthPoint H i)) = 0
      exact atomicOrder_zero _ _ _ (ninthPoint_two_absent H i ht)
  | some j =>
      change atomicOrder (ninthPoint H) ninthMultiplicity
        (powerMap 2 (ninthPoint H i)) = ninthMultiplicity j
      rw [ninthPoint_two_of_target H i j ht]
      exact atomicOrder_at _ _ (ninthPoint_injective H) j

theorem ninthSpectrum_four_order (H : Real) (hH : 0 < H) (i : Fin 29) :
    (ninthSpectrum H hH).rowOrder 4 i =
      (ninthFourTarget i).elim 0 ninthMultiplicity := by
  cases ht : ninthFourTarget i with
  | none =>
      change atomicOrder (ninthPoint H) ninthMultiplicity
        (powerMap 4 (ninthPoint H i)) = 0
      exact atomicOrder_zero _ _ _ (ninthPoint_four_absent H i ht)
  | some j =>
      change atomicOrder (ninthPoint H) ninthMultiplicity
        (powerMap 4 (ninthPoint H i)) = ninthMultiplicity j
      rw [ninthPoint_four_of_target H i j ht]
      exact atomicOrder_at _ _ (ninthPoint_injective H) j

theorem ninthSpectrum_weak_iff (H : Real) (hH : 0 < H) (i : Fin 29) :
    Membership.mem (ninthSpectrum H hH).weakIndices i <->
      i = 0 \/ i = 1 \/ i = 3 \/ i = 5 \/ i = 7 \/ i = 9 \/ i = 13 := by
  classical
  rw [ReflectedSpectrum.weakIndices, Finset.mem_filter]
  simp only [Finset.mem_univ, true_and]
  rw [ninthSpectrum_two_order, ninthSpectrum_four_order]
  change ((ninthMultiplicity i : Real) <=
      2 * (((ninthTwoTarget i).elim 0 ninthMultiplicity : Nat) : Real) /\
    (ninthMultiplicity i : Real) <=
      4 * (((ninthFourTarget i).elim 0 ninthMultiplicity : Nat) : Real)) <->
        i = 0 \/ i = 1 \/ i = 3 \/ i = 5 \/ i = 7 \/ i = 9 \/ i = 13
  fin_cases i <;> norm_num [ninthMultiplicity, ninthTwoTarget, ninthFourTarget]

theorem ninthSpectrum_weakIndices (H : Real) (hH : 0 < H) :
    (ninthSpectrum H hH).weakIndices = {0, 1, 3, 5, 7, 9, 13} := by
  classical
  apply Finset.ext
  intro i
  rw [ninthSpectrum_weak_iff]
  simp only [Finset.mem_insert, Finset.mem_singleton]

theorem ninthSpectrum_den_ne (H : Real) (hH : 0 < H) (d : Real) (i : Fin 29) :
    Not ((ninthSpectrum H hH).point i + (d : Complex) - 1 = 0) := by
  intro hz
  have he := congrArg Complex.im hz
  simp only [Complex.sub_im, Complex.add_im, Complex.ofReal_im, Complex.one_im,
    Complex.zero_im, add_zero, sub_zero] at he
  exact (ne_of_gt ((ninthSpectrum H hH).im_pos i)) he

theorem ninthSpectrum_full_residue_ne_zero (H : Real) (hH : 0 < H)
    (d : Real) (hd : 1 < d) (i : Fin 29) :
    Not (atomicPowerResidue (ninthSpectrum H hH).point
      (ninthSpectrum H hH).mult d ((ninthSpectrum H hH).point i) = 0) := by
  apply atomicPowerResidue_ne_zero _ _ d hd _
    (ne_of_gt ((ninthSpectrum H hH).im_pos i)) (ninthSpectrum_den_ne H hH d i)
  rw [atomicOrder_at _ _ (ninthSpectrum H hH).point_injective i]
  exact (ninthSpectrum H hH).mult_pos i

theorem ninthSpectrum_readout_scaled_limit (H : Real) (hH : 0 < H)
    (d : Real) (hd : 0 < d) (i : Fin 29) :
    Filter.Tendsto
      (fun s => (s - (ninthSpectrum H hH).point i) *
        affinePowerReadout
          (atomicReadout (ninthSpectrum H hH).point (ninthSpectrum H hH).mult) d s)
      (nhdsWithin ((ninthSpectrum H hH).point i)
        (Set.compl {(ninthSpectrum H hH).point i}))
      (nhds (atomicPowerResidue (ninthSpectrum H hH).point
        (ninthSpectrum H hH).mult d ((ninthSpectrum H hH).point i))) := by
  exact atomicPower_scaled_limit _ _ d hd _ (ninthSpectrum_den_ne H hH d i)

theorem ninthSpectrum_projection_negative_iff (H : Real) (hH : 0 < H)
    (d : Real) (i : Fin 29) :
    (atomicPowerResidue (ninthSpectrum H hH).point (ninthSpectrum H hH).mult d
        ((ninthSpectrum H hH).point i) *
      ((ninthSpectrum H hH).point i + (d : Complex) - 1)).im < 0 <->
      d * ((ninthSpectrum H hH).rowOrder d i : Real) <
        ((ninthSpectrum H hH).mult i : Real) := by
  let S := ninthSpectrum H hH
  have h := atomicPower_projection S.point S.mult d (S.point i)
    (ninthSpectrum_den_ne H hH d i)
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


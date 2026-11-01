/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Assembly.FiniteFieldNativeDensityOne
import PrimeFactorOscillations.Assembly.FiniteFieldNativeFlatEnergy
import PrimeFactorOscillations.Assembly.FiniteFieldNativeFullCounting

/-!
# Sharp full-height native capacity and physical stability

Almost all actual positive prime pairs fit simultaneously in a flat
codebook. Its cardinality has the sharp leading constant one half, and
the same finite codebook retains the exact signed physical energy and
optimal five-eighths stability before its independent field-scale limit.
-/

set_option autoImplicit false
set_option Elab.async false

open Filter
open scoped Classical Topology

namespace PrimeFactorOscillations.FiniteFieldIntegerSignature

/-- Sharp full-height capacity, density-one retention and the complete
physical limit hold on the same positive-gap prime-pair codebooks. -/
theorem eventually_native_full_pair_sharp_capacity
    (eps : Real) (heps : 0 < eps) :
    Filter.Eventually (fun Y : Nat =>
      (forall V : Finset (Prod Nat Nat), V <= nativeFullPrimePairGapSet Y ->
        (V.card : Real) <=
          (1 / 2 + eps) * ((Y : Real) ^ 2 / Real.log (Y : Real) ^ 2)) /\
      exists M : Finset (Prod Nat Nat),
        M <= nativeFullPrimePairGapSet Y /\
        (1 - eps) * ((nativeFullPrimePairGapSet Y).card : Real) <= (M.card : Real) /\
        (1 / 2 - eps) * ((Y : Real) ^ 2 / Real.log (Y : Real) ^ 2) <= (M.card : Real) /\
        2 <= M.card /\
        (forall a : Prod Nat Nat, Membership.mem M a ->
          forall b : Prod Nat Nat, Membership.mem M b -> Not (a = b) ->
            nativeAgreementRate a.1 a.2 b.1 b.2 = 3 / 8) /\
        let n : M -> Nat := fun a => a.val.1
        let h : M -> Nat := fun a => a.val.2
        (forall c : M -> Real,
          Tendsto (nativeAgreementMassForm n h c) atTop
            (nhds ((3 / 8 : Real) * (Finset.univ.sum c) ^ 2 +
              (5 / 8 : Real) * Finset.univ.sum (fun i => (c i) ^ 2)))) /\
        (forall kappa : Real,
          (forall c : M -> Real,
            kappa * Finset.univ.sum (fun i => (c i) ^ 2) <=
              nativeAgreementForm n h c) <-> kappa <= 5 / 8)) atTop := by
  classical
  let delta : Real := min (eps / 8) (1 / 8)
  have hd : 0 < delta := lt_min (by positivity) (by norm_num)
  have hdSmall : delta <= 1 / 8 := min_le_right _ _
  have hdEight : 8 * delta <= eps := by
    have hh : delta <= eps / 8 := min_le_left _ _
    linarith
  have hdEps : delta <= eps := by linarith
  have hRet := eventually_native_full_prime_pair_density_one delta hd
  have hLow := tendsto_native_full_pair_count_ratio.eventually
    (lt_mem_nhds (show (1 / 2 : Real) - delta < 1 / 2 by linarith))
  have hUp := tendsto_native_full_pair_count_ratio.eventually
    (gt_mem_nhds (show (1 / 2 : Real) < 1 / 2 + delta by linarith))
  have hGrow := Real.eventually_const_mul_log_natpow_le_rpow
    (8 : Real) 2 (s := (2 : Real)) (by norm_num)
  filter_upwards [hRet, hLow, hUp, hGrow, eventually_ge_atTop (2 : Nat)]
    with Y hRetY hLowY hUpY hGrowth hY
  let S := nativeFullPrimePairGapSet Y
  let D : Real := (Y : Real) ^ 2 / Real.log (Y : Real) ^ 2
  have hy1 : (1 : Real) < Y := by exact_mod_cast (show 1 < Y by omega)
  have hyPos : (0 : Real) < Y := zero_lt_one.trans hy1
  have hlPos : 0 < Real.log (Y : Real) := Real.log_pos hy1
  have hl0 : Not (Real.log (Y : Real) = 0) := ne_of_gt hlPos
  have hDpos : 0 < D := by dsimp only [D]; positivity
  have hD0 : 0 <= D := hDpos.le
  have hDne : Not (D = 0) := ne_of_gt hDpos
  have hCancel : ((S.card : Real) / D) * D = (S.card : Real) := by
    field_simp [hDne]
  have hLowerS : (1 / 2 - delta) * D <= (S.card : Real) := by
    have hh : (1 / 2 : Real) - delta <= (S.card : Real) / D := hLowY.le
    have hm := mul_le_mul_of_nonneg_right hh hD0
    rw [hCancel] at hm
    exact hm
  have hUpperS : (S.card : Real) <= (1 / 2 + delta) * D := by
    have hh : (S.card : Real) / D <= (1 / 2 : Real) + delta := hUpY.le
    have hm := mul_le_mul_of_nonneg_right hh hD0
    rw [hCancel] at hm
    exact hm
  have hUpper (V : Finset (Prod Nat Nat)) (hV : V <= S) :
      (V.card : Real) <= (1 / 2 + eps) * D := by
    have hc : (V.card : Real) <= (S.card : Real) := by
      exact_mod_cast Finset.card_le_card hV
    exact (hc.trans hUpperS).trans
      (mul_le_mul_of_nonneg_right (by linarith : (1 / 2 : Real) + delta <= 1 / 2 + eps) hD0)
  choose M hSub hCount hGeometry hFlat using hRetY
  have hNonneg : 0 <= 1 - delta := by linarith
  have hLowerProduct : (1 - delta) * ((1 / 2 - delta) * D) <= (M.card : Real) :=
    (mul_le_mul_of_nonneg_left hLowerS hNonneg).trans hCount
  have hCoefficient : (1 / 2 : Real) - eps <= (1 - delta) * (1 / 2 - delta) := by
    nlinarith only [hdEight, hd.le, sq_nonneg delta]
  have hAbsolute : (1 / 2 - eps) * D <= (M.card : Real) := by
    have hh := mul_le_mul_of_nonneg_right hCoefficient hD0
    exact hh.trans (by simpa only [mul_assoc] using hLowerProduct)
  have hRelative : (1 - eps) * (S.card : Real) <= (M.card : Real) :=
    (mul_le_mul_of_nonneg_right
      (by linarith : 1 - eps <= 1 - delta) (Nat.cast_nonneg S.card)).trans hCount
  have hGrowthNat : 8 * Real.log (Y : Real) ^ 2 <= (Y : Real) ^ 2 := by
    norm_num [Real.rpow_natCast] at hGrowth
    exact hGrowth
  have hD8 : (8 : Real) <= D := by
    have hh := div_nonneg (sub_nonneg.mpr hGrowthNat)
      (sq_nonneg (Real.log (Y : Real)))
    have he : ((Y : Real) ^ 2 - 8 * Real.log (Y : Real) ^ 2) /
        Real.log (Y : Real) ^ 2 = D - 8 := by
      dsimp only [D]
      field_simp [hl0]
    rw [he] at hh
    linarith only [hh]
  have hQuarter : (1 / 4 : Real) <= (1 - delta) * (1 / 2 - delta) := by
    nlinarith only [hdSmall, sq_nonneg delta]
  have hTwoReal : (2 : Real) <= (M.card : Real) := by
    have hh := mul_le_mul_of_nonneg_right hQuarter hD0
    have ht : (2 : Real) <= (1 / 4) * D := by nlinarith only [hD8]
    exact (ht.trans hh).trans (by simpa only [mul_assoc] using hLowerProduct)
  have hTwo : 2 <= M.card := by exact_mod_cast hTwoReal
  refine And.intro hUpper (Exists.intro M
    (And.intro hSub (And.intro hRelative (And.intro hAbsolute
      (And.intro hTwo (And.intro hFlat ?_))))))
  let n : M -> Nat := fun a => a.val.1
  let h : M -> Nat := fun a => a.val.2
  have hn (a : M) : Nat.Prime (n a) := (hGeometry a.val a.property).1
  have hnh (a : M) : Nat.Prime (n a + h a) := (hGeometry a.val a.property).2.1
  have hh (a : M) : 0 < h a := (hGeometry a.val a.property).2.2.1
  have hinj : Function.Injective (fun a : M => Prod.mk (n a) (h a)) := by
    intro a b he
    apply Subtype.ext
    exact he
  have hflat (a b : M) (hab : Not (a = b)) :
      nativeAgreementRate (n a) (h a) (n b) (h b) = 3 / 8 := by
    apply hFlat a.val a.property b.val b.property
    intro he
    exact hab (Subtype.ext he)
  refine And.intro ?_ ?_
  . intro c
    exact native_flat_agreement_mass_form_tendsto n h hn hnh hh hinj hflat c
  . intro kappa
    apply Iff.intro
    . intro hBound
      choose a ha b hb hab using Finset.one_lt_card.mp (show 1 < M.card by omega)
      let i : M := Subtype.mk a ha
      let j : M := Subtype.mk b hb
      have hij : Not (i = j) := by
        intro he
        have hv := congrArg (fun v : M => v.val) he
        exact hab hv
      exact native_flat_agreement_stability_optimal n h hflat i j hij kappa hBound
    . intro hk c
      have hs : 0 <= Finset.univ.sum (fun i : M => (c i) ^ 2) :=
        Finset.sum_nonneg (fun i hi => sq_nonneg (c i))
      exact (mul_le_mul_of_nonneg_right hk hs).trans
        (native_flat_agreement_stability n h hflat c)

end PrimeFactorOscillations.FiniteFieldIntegerSignature

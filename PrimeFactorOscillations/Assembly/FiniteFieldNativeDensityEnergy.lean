/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Assembly.FiniteFieldNativeDensityOne
import PrimeFactorOscillations.Assembly.FiniteFieldNativeFlatEnergy

/-!
# Density-one native codebooks with sharp physical stability

The same almost-full actual prime-pair codebook has the exact signed
physical energy limit and the optimal five-eighths stability constant.
Each chosen finite codebook is fixed before the independent field scale.
-/

set_option autoImplicit false
set_option Elab.async false

open Filter
open scoped Classical Topology

namespace PrimeFactorOscillations.FiniteFieldIntegerSignature

open PrimeFactorOscillations.QRH

/-- Density-one retention, exact physical energy and optimal stability
hold simultaneously for the same actual prime-pair codebooks. -/
theorem eventually_native_density_one_physical_capacity
    (eps : Real) (heps : 0 < eps) :
    Filter.Eventually (fun Y : Nat =>
      exists M : Finset (Prod Nat Nat),
        M <= primeBlockGapSet (2 * (Y / 4)) (3 * (Y / 4)) (4 * (Y / 4)) /\
        (1 - eps) *
          ((primeBlockGapSet (2 * (Y / 4)) (3 * (Y / 4)) (4 * (Y / 4))).card : Real) <=
            (M.card : Real) /\
        (forall a : Prod Nat Nat, Membership.mem M a ->
          Nat.Prime a.1 /\ Nat.Prime (a.1 + a.2) /\ 0 < a.2 /\
            a.2 < a.1 /\ a.1 + a.2 <= Y) /\
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
  have hRet := eventually_native_prime_pair_density_one
    (min eps (1 / 2)) (lt_min heps (by norm_num))
  have hGrow := Real.eventually_const_mul_log_natpow_le_rpow
    (8000 : Real) 2 (s := (2 : Real)) (by norm_num)
  filter_upwards [hRet, eventually_squarefree_quarter_prime_pair_supply, hGrow]
    with Y hRetY hSq hGrowth
  let S := primeBlockGapSet (2 * (Y / 4)) (3 * (Y / 4)) (4 * (Y / 4))
  choose M hSub hCount hGeometry hFlat using hRetY
  have hlPos : 0 < Real.log (Y : Real) := lt_of_lt_of_le zero_lt_one hSq.2.1
  have hl0 : Not (Real.log (Y : Real) = 0) := ne_of_gt hlPos
  have hden : 0 < 2000 * Real.log (Y : Real) ^ 2 := by positivity
  have hGrowthNat : 8000 * Real.log (Y : Real) ^ 2 <= (Y : Real) ^ 2 := by
    norm_num [Real.rpow_natCast] at hGrowth
    exact hGrowth
  have hFourLower : (4 : Real) <=
      (Y : Real) ^ 2 / (2000 * Real.log (Y : Real) ^ 2) := by
    have ht : (4 : Real) * (2000 * Real.log (Y : Real) ^ 2) <=
        (Y : Real) ^ 2 := by nlinarith only [hGrowthNat]
    have hd := div_nonneg (sub_nonneg.mpr ht) hden.le
    have he : ((Y : Real) ^ 2 - 4 * (2000 * Real.log (Y : Real) ^ 2)) /
        (2000 * Real.log (Y : Real) ^ 2) =
          (Y : Real) ^ 2 / (2000 * Real.log (Y : Real) ^ 2) - 4 := by field_simp
    rw [he] at hd
    linarith only [hd]
  have hSqSub : squarefreePrimeBlockGapSet
      (2 * (Y / 4)) (3 * (Y / 4)) (4 * (Y / 4)) <= S := Finset.filter_subset _ _
  have hSqCard :
      ((squarefreePrimeBlockGapSet
        (2 * (Y / 4)) (3 * (Y / 4)) (4 * (Y / 4))).card : Real) <= (S.card : Real) := by
    exact_mod_cast Finset.card_le_card hSqSub
  have hFourS : (4 : Real) <= (S.card : Real) :=
    hFourLower.trans (hSq.2.2.trans hSqCard)
  have hHalf : (1 / 2 : Real) * (S.card : Real) <= (M.card : Real) := by
    have hc : (1 / 2 : Real) <= 1 - min eps (1 / 2) := by
      have hh := min_le_right eps (1 / 2 : Real)
      linarith
    exact (mul_le_mul_of_nonneg_right hc (Nat.cast_nonneg S.card)).trans hCount
  have hTwo : 2 <= M.card := by
    have hh : (2 : Real) <= (M.card : Real) := by nlinarith only [hFourS, hHalf]
    exact_mod_cast hh
  have hRetention : (1 - eps) * (S.card : Real) <= (M.card : Real) := by
    have hc : 1 - eps <= 1 - min eps (1 / 2) := by
      have hh := min_le_left eps (1 / 2 : Real)
      linarith
    exact (mul_le_mul_of_nonneg_right hc (Nat.cast_nonneg S.card)).trans hCount
  refine Exists.intro M (And.intro hSub (And.intro hRetention
    (And.intro hGeometry (And.intro hTwo (And.intro hFlat ?_)))))
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

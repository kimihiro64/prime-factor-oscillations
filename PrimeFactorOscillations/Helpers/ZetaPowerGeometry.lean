/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.XiZeroMultiplicity
import PrimeFactorOscillations.Helpers.XiZetaMultiplicity
import PrimeFactorOscillations.Helpers.ZetaZeroGeometry

/-!
# Unconditional reflection geometry for zeta multiplicity energies

Finite positive-height zero windows retain the actual analytic multiplicities.
Reflection gives a disjoint equal-energy copy of the right-half zero set.
The conjugation-order argument follows the factorization proof in
PrimeNumberTheoremAnd/IEANTN/KadiriZeroCounting.lean at
f6147e7572ab3abe5428101bc0b13627bcb005df, with a local slope proof.
These supporting facts use no RH assumption.
-/

set_option autoImplicit false
set_option Elab.async false

noncomputable section

namespace PrimeFactorOscillations.CarmichaelWeightedSignal

private theorem hasDerivAt_doubleConj {f : Complex -> Complex} {f' z : Complex}
    (hf : HasDerivAt f f' ((starRingEnd Complex) z)) :
    HasDerivAt (fun w => (starRingEnd Complex) (f ((starRingEnd Complex) w)))
      ((starRingEnd Complex) f') z := by
  rw [hasDerivAt_iff_tendsto_slope] at hf
  rw [hasDerivAt_iff_tendsto_slope]
  have hc : Filter.Tendsto (starRingEnd Complex)
      (nhdsWithin z (Set.compl {z}))
      (nhdsWithin ((starRingEnd Complex) z)
        (Set.compl {(starRingEnd Complex) z})) := by
    apply tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within
    . exact (Complex.continuous_conj.tendsto z).mono_left nhdsWithin_le_nhds
    . apply Filter.Eventually.mono self_mem_nhdsWithin
      intro w hw he
      apply hw
      have hh := congrArg (starRingEnd Complex) he
      simpa only [Complex.conj_conj, Set.mem_singleton_iff] using hh
  have hcomp := (Complex.continuous_conj.tendsto f').comp (hf.comp hc)
  refine Filter.Tendsto.congr (fun u => ?_) hcomp
  simp [Function.comp_apply, slope_def_field]

private theorem analyticAt_doubleConj {f : Complex -> Complex} {z : Complex}
    (hf : AnalyticAt Complex f ((starRingEnd Complex) z)) :
    AnalyticAt Complex
      (fun w => (starRingEnd Complex) (f ((starRingEnd Complex) w))) z := by
  rw [Complex.analyticAt_iff_eventually_differentiableAt] at hf
  rw [Complex.analyticAt_iff_eventually_differentiableAt]
  have hc : Filter.Tendsto (starRingEnd Complex) (nhds z)
      (nhds ((starRingEnd Complex) z)) := Complex.continuous_conj.tendsto z
  apply Filter.Eventually.mono (hc.eventually hf)
  intro w hw
  exact (hasDerivAt_doubleConj hw.hasDerivAt).differentiableAt

private theorem analyticOrderAt_doubleConj {f : Complex -> Complex} {z : Complex}
    (hf : AnalyticAt Complex f ((starRingEnd Complex) z)) :
    analyticOrderAt
        (fun w => (starRingEnd Complex) (f ((starRingEnd Complex) w))) z =
      analyticOrderAt f ((starRingEnd Complex) z) := by
  have hcfc := analyticAt_doubleConj hf
  have hc : Filter.Tendsto (starRingEnd Complex) (nhds z)
      (nhds ((starRingEnd Complex) z)) := Complex.continuous_conj.tendsto z
  cases h : analyticOrderAt f ((starRingEnd Complex) z) with
  | top =>
      rw [analyticOrderAt_eq_top] at h
      rw [analyticOrderAt_eq_top]
      apply Filter.Eventually.mono (hc.eventually h)
      intro w hw
      rw [hw, map_zero]
  | coe n =>
      rw [hf.analyticOrderAt_eq_natCast] at h
      choose g hg hg0 hfg using h
      rw [hcfc.analyticOrderAt_eq_natCast]
      refine Exists.intro
        (fun w => (starRingEnd Complex) (g ((starRingEnd Complex) w)))
        (And.intro (analyticAt_doubleConj hg) (And.intro ?_ ?_))
      . intro h0
        apply hg0
        have hh := congrArg (starRingEnd Complex) h0
        simpa only [map_zero, Complex.conj_conj] using hh
      . apply Filter.Eventually.mono (hc.eventually hfg)
        intro w hw
        rw [hw]
        simp only [smul_eq_mul, map_mul, map_pow, map_sub, Complex.conj_conj]

theorem zetaMultiplicity_conj {rho : Complex} (hOne : Not (rho = 1)) :
    analyticOrderNatAt riemannZeta ((starRingEnd Complex) rho) =
      analyticOrderNatAt riemannZeta rho := by
  have han : AnalyticAt Complex riemannZeta rho :=
    riemannZeta_analyticOn_compl_one rho (by simpa only [Set.mem_compl_iff,
      Set.mem_singleton_iff] using hOne)
  have hfun : (fun w : Complex =>
      (starRingEnd Complex) (riemannZeta ((starRingEnd Complex) w))) = riemannZeta := by
    funext w
    rw [riemannZeta_conj, Complex.conj_conj]
  have h := analyticOrderAt_doubleConj
    (f := riemannZeta) (z := (starRingEnd Complex) rho)
    (by simpa only [Complex.conj_conj] using han)
  rw [hfun, Complex.conj_conj] at h
  exact congrArg ENat.toNat h

def upperZeroFinset (T : Real) : Finset PrimeClassDeletion.ZetaDistinctZero := by
  classical
  exact (show Set.Finite {z : PrimeClassDeletion.ZetaDistinctZero |
      0 < z.val.im /\ z.val.im <= T} from
    (PrimeClassDeletion.zetaDistinctZero_bounded_height_finite T).subset (by
      intro z hz
      change abs z.val.im <= T
      rw [abs_of_pos hz.1]
      exact hz.2)).toFinset

theorem mem_upperZeroFinset (T : Real) (z : PrimeClassDeletion.ZetaDistinctZero) :
    Membership.mem (upperZeroFinset T) z <-> 0 < z.val.im /\ z.val.im <= T := by
  classical
  simp only [upperZeroFinset, Set.Finite.mem_toFinset, Set.mem_ofPred_eq]

def zeroReflection (rho : Complex) : Complex :=
  1 - (starRingEnd Complex) rho

theorem zeroReflection_re (rho : Complex) :
    (zeroReflection rho).re = 1 - rho.re := by
  simp [zeroReflection]

theorem zeroReflection_im (rho : Complex) :
    (zeroReflection rho).im = rho.im := by
  simp [zeroReflection]

theorem zeroReflection_involutive (rho : Complex) :
    zeroReflection (zeroReflection rho) = rho := by
  apply Complex.ext <;> simp [zeroReflection]

private theorem reflection_strip {rho : Complex}
    (hr : 0 < rho.re /\ rho.re < 1) :
    0 < (zeroReflection rho).re /\ (zeroReflection rho).re < 1 := by
  rw [zeroReflection_re]
  exact And.intro (by linarith [hr.2]) (by linarith [hr.1])

theorem zetaMultiplicity_reflection {rho : Complex}
    (hr : 0 < rho.re /\ rho.re < 1) :
    analyticOrderNatAt riemannZeta (zeroReflection rho) =
      analyticOrderNatAt riemannZeta rho := by
  have hc : 0 < ((starRingEnd Complex) rho).re /\
      ((starRingEnd Complex) rho).re < 1 := by
    simpa only [Complex.conj_re] using hr
  have ht := reflection_strip hr
  have hOne : Not (rho = 1) :=
    fun h => (ne_of_lt hr.2) (congrArg Complex.re h)
  have hcOne : Not ((starRingEnd Complex) rho = 1) :=
    fun h => (ne_of_lt hc.2) (congrArg Complex.re h)
  have htOne : Not (zeroReflection rho = 1) :=
    fun h => (ne_of_lt ht.2) (congrArg Complex.re h)
  have h := xiZeroMultiplicity_one_sub ((starRingEnd Complex) rho)
  change xiZeroMultiplicity (zeroReflection rho) =
    xiZeroMultiplicity ((starRingEnd Complex) rho) at h
  rw [xiZeroMultiplicity_eq_zetaOrder ht.1 htOne,
    xiZeroMultiplicity_eq_zetaOrder hc.1 hcOne] at h
  exact h.trans (zetaMultiplicity_conj hOne)

private theorem zeta_zero_reflection {rho : Complex}
    (hz : riemannZeta rho = 0) (hr : 0 < rho.re /\ rho.re < 1) :
    riemannZeta (zeroReflection rho) = 0 := by
  have hc : riemannZeta ((starRingEnd Complex) rho) = 0 := by
    rw [riemannZeta_conj, hz, map_zero]
  have hcr : 0 < ((starRingEnd Complex) rho).re /\
      ((starRingEnd Complex) rho).re < 1 := by
    simpa only [Complex.conj_re] using hr
  have hXi := (PrimeClassDeletion.riemannXi_zero_iff_nontrivial_zeta_zero
    ((starRingEnd Complex) rho)).mpr (And.intro hc hcr)
  have hRef : Complex.riemannXi (zeroReflection rho) = 0 := by
    rw [zeroReflection, Complex.riemannXi_one_sub]
    exact hXi
  exact ((PrimeClassDeletion.riemannXi_zero_iff_nontrivial_zeta_zero
    (zeroReflection rho)).mp hRef).1

def zetaZeroWindow (T : Real) (rho : Complex) : Prop :=
  riemannZeta rho = 0 /\ 0 < rho.re /\ rho.re < 1 /\
    0 < rho.im /\ rho.im <= T

def upperZeroValues (T : Real) : Finset Complex := by
  classical
  exact (upperZeroFinset T).image (fun z => z.val)

theorem mem_upperZeroValues (T : Real) (rho : Complex) :
    Membership.mem (upperZeroValues T) rho <-> zetaZeroWindow T rho := by
  classical
  constructor
  . intro h
    choose z hz he using Finset.mem_image.mp h
    have hw := (mem_upperZeroFinset T z).mp hz
    subst rho
    exact And.intro z.property.1
      (And.intro z.property.2.1 (And.intro z.property.2.2 hw))
  . intro h
    let z : PrimeClassDeletion.ZetaDistinctZero :=
      Subtype.mk rho (And.intro h.1 (And.intro h.2.1 h.2.2.1))
    have hz : Membership.mem (upperZeroFinset T) z :=
      (mem_upperZeroFinset T z).mpr h.2.2.2
    exact Finset.mem_image.mpr (Exists.intro z (And.intro hz rfl))

theorem reflection_mem_upperZeroValues {T : Real} {rho : Complex}
    (h : Membership.mem (upperZeroValues T) rho) :
    Membership.mem (upperZeroValues T) (zeroReflection rho) := by
  have hw := (mem_upperZeroValues T rho).mp h
  have hr : 0 < rho.re /\ rho.re < 1 := And.intro hw.2.1 hw.2.2.1
  have ht := reflection_strip hr
  apply (mem_upperZeroValues T (zeroReflection rho)).mpr
  exact And.intro (zeta_zero_reflection hw.1 hr)
    (And.intro ht.1 (And.intro ht.2
      (by simpa only [zeroReflection_im] using hw.2.2.2)))

def zetaHeightMass (rho : Complex) : Real :=
  (analyticOrderNatAt riemannZeta rho : Real) / rho.im

theorem zetaHeightMass_reflection {rho : Complex}
    (hr : 0 < rho.re /\ rho.re < 1) :
    zetaHeightMass (zeroReflection rho) = zetaHeightMass rho := by
  simp only [zetaHeightMass, zetaMultiplicity_reflection hr, zeroReflection_im]

theorem zeta_right_half_energy_le (T : Real) :
    2 * ((upperZeroValues T).filter (fun rho => (1 / 2 : Real) < rho.re)).sum
      (fun rho => (zetaHeightMass rho) ^ 2) <=
      (upperZeroValues T).sum (fun rho => (zetaHeightMass rho) ^ 2) := by
  classical
  let S := upperZeroValues T
  let R := S.filter (fun rho => (1 / 2 : Real) < rho.re)
  have hInj : Function.Injective zeroReflection := by
    intro x y hxy
    have h := congrArg zeroReflection hxy
    simpa only [zeroReflection_involutive] using h
  have hDisjoint : Disjoint R (R.image zeroReflection) := by
    apply Finset.disjoint_left.mpr
    intro rho hr hi
    choose tau ht he using Finset.mem_image.mp hi
    have hRho : (1 / 2 : Real) < rho.re := (Finset.mem_filter.mp hr).2
    have hTau : (1 / 2 : Real) < tau.re := (Finset.mem_filter.mp ht).2
    rw [<- he, zeroReflection_re] at hRho
    linarith
  have hSubset : Union.union R (R.image zeroReflection) <= S := by
    intro rho h
    apply Or.elim (Finset.mem_union.mp h)
    . intro hr
      exact (Finset.mem_filter.mp hr).1
    . intro hi
      choose tau ht he using Finset.mem_image.mp hi
      rw [<- he]
      exact reflection_mem_upperZeroValues (Finset.mem_filter.mp ht).1
  have hImageSum : (R.image zeroReflection).sum
      (fun rho => (zetaHeightMass rho) ^ 2) =
      R.sum (fun rho => (zetaHeightMass rho) ^ 2) := by
    rw [Finset.sum_image (fun i _ j _ hij => hInj hij)]
    apply Finset.sum_congr rfl
    intro rho hr
    have hw := (mem_upperZeroValues T rho).mp (Finset.mem_filter.mp hr).1
    rw [zetaHeightMass_reflection (And.intro hw.2.1 hw.2.2.1)]
  have hSum := Finset.sum_le_sum_of_subset_of_nonneg hSubset
    (fun rho _ _ => sq_nonneg (zetaHeightMass rho))
  rw [Finset.sum_union hDisjoint, hImageSum] at hSum
  change 2 * R.sum (fun rho => (zetaHeightMass rho) ^ 2) <=
    S.sum (fun rho => (zetaHeightMass rho) ^ 2)
  linarith

end PrimeFactorOscillations.CarmichaelWeightedSignal

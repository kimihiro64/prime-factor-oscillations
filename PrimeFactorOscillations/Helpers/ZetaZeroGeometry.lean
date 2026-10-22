/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.LogGaussianZetaExplicit
import PrimeFactorOscillations.Helpers.Robin1984.Analytic.RiemannZetaRealEuler
import PrimeNumberTheoremAnd.IEANTN.ZetaDefinitions

/-!
# Actual zero geometry for Gaussian exposure

The existing real-axis nonvanishing and compact zero-set providers are
consumed on the actual distinct-zero subtype. Conjugation preserves the
real part, gives a positive-height representative, and bounded height
ranges contain finitely many candidates. No RH assumption is used.
-/

set_option autoImplicit false
set_option Elab.async false

namespace PrimeFactorOscillations.PrimeClassDeletion

theorem zetaDistinctZero_im_ne_zero (z : ZetaDistinctZero) : Not (z.val.im = 0) := by
  intro hIm
  have hReal : z.val = (z.val.re : Complex) := by
    apply Complex.ext
    . rfl
    . simpa only [Complex.ofReal_im] using hIm
  apply Robin1984.riemannZeta_real_ne_zero_of_mem_Ioo_zero_one z.property.2
  rw [<- hReal]
  exact z.property.1

noncomputable def zetaDistinctZeroConj (z : ZetaDistinctZero) : ZetaDistinctZero := by
  refine Subtype.mk ((starRingEnd Complex) z.val) (And.intro ?_ ?_)
  . rw [riemannZeta_conj, z.property.1, map_zero]
  . simpa only [Complex.conj_re] using z.property.2

theorem zetaDistinctZero_exists_positive_height (z : ZetaDistinctZero) :
    Exists fun w : ZetaDistinctZero => And (w.val.re = z.val.re)
      (And (w.val.im ^ 2 = z.val.im ^ 2) (0 < w.val.im)) := by
  by_cases h : 0 < z.val.im
  . exact Exists.intro z (And.intro rfl (And.intro rfl h))
  . refine Exists.intro (zetaDistinctZeroConj z) (And.intro ?_ (And.intro ?_ ?_))
    . exact Complex.conj_re z.val
    . change ((starRingEnd Complex) z.val).im ^ 2 = z.val.im ^ 2
      rw [Complex.conj_im, neg_sq]
    . change 0 < ((starRingEnd Complex) z.val).im
      rw [Complex.conj_im]
      exact neg_pos.mpr (lt_of_le_of_ne (le_of_not_gt h) (zetaDistinctZero_im_ne_zero z))

theorem zetaDistinctZero_bounded_height_finite (T : Real) :
    Set.Finite {z : ZetaDistinctZero | abs z.val.im <= T} := by
  let C : Set Complex := Metric.closedBall 0 (1 + abs T)
  have hFinite : Set.Finite (C.inter riemannZeta.zeroes) :=
    riemannZeta.zeroes_on_Compact_finite' (isCompact_closedBall 0 (1 + abs T))
  have hInj : Set.InjOn (fun z : ZetaDistinctZero => z.val)
      (Set.preimage (fun z : ZetaDistinctZero => z.val) (C.inter riemannZeta.zeroes)) := by
    intro x hx y hy hxy
    exact Subtype.ext hxy
  have hPre := Set.Finite.preimage hInj hFinite
  apply hPre.subset
  intro z hz
  refine And.intro ?_ z.property.1
  change dist z.val 0 <= 1 + abs T
  rw [dist_zero_right]
  calc
    norm z.val <= abs z.val.re + abs z.val.im := Complex.norm_le_abs_re_add_abs_im z.val
    _ <= 1 + abs T := add_le_add
      (by rw [abs_of_pos z.property.2.1]; exact z.property.2.2.le)
      (hz.trans (le_abs_self T))

theorem zetaDistinctZero_coefficient_ne_zero (z : ZetaDistinctZero) :
    Not ((((analyticOrderAt riemannZeta z.val).toNat : Complex) / z.val) = 0) := by
  have hOne : Not (z.val = 1) := by
    intro h
    have hRe := z.property.2.2
    rw [h, Complex.one_re] at hRe
    exact (lt_irrefl 1) hRe
  have hZero : Not (z.val = 0) := by
    intro h
    have hRe := z.property.2.1
    rw [h, Complex.zero_re] at hRe
    exact (lt_irrefl 0) hRe
  have hXi := (riemannXi_zero_iff_nontrivial_zeta_zero z.val).mpr z.property
  have hMultiplicity := (xiZeroMultiplicity_pos_iff z.val).mpr hXi
  rw [xiZeroMultiplicity_eq_zetaOrder z.property.2.1 hOne] at hMultiplicity
  have hNat : Not ((analyticOrderAt riemannZeta z.val).toNat = 0) :=
    Nat.ne_of_gt hMultiplicity
  exact div_ne_zero (Nat.cast_ne_zero.mpr hNat) hZero

end PrimeFactorOscillations.PrimeClassDeletion

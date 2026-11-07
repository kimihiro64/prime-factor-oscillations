/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import PrimeFactorOscillations.Mathlib.Analysis.Complex.PairedResolventKernel

/-!
# Sharp positivity for finite compensated reflected resolvents

The exact fixed-radius criterion is a sum of two semiaxes. It is weaker
than the infinitesimal radius condition when the radii differ. Failure
has an explicit vertical witness; no numerical test is used.
-/

set_option autoImplicit false
set_option Elab.async false

noncomputable section

namespace Complex

theorem pairedResolventGram_boundary_sos (r R w y a b : Real)
    (ha : a ^ 2 = r ^ 2 - w ^ 2) (hb : b ^ 2 = R ^ 2 - w ^ 2) :
    pairedResolventGram r R w y =
      (y ^ 2 - a * b) ^ 2 + ((a + b) ^ 2 - 4 * w ^ 2) * y ^ 2 := by
  unfold pairedResolventGram
  rw [show r ^ 2 = a ^ 2 + w ^ 2 by linarith only [ha],
    show R ^ 2 = b ^ 2 + w ^ 2 by linarith only [hb]]
  ring

theorem pairedResolventGram_strip_difference (r R x w y : Real) :
    pairedResolventGram r R x y - pairedResolventGram r R w y =
      (w ^ 2 - x ^ 2) * (r ^ 2 + R ^ 2 + 6 * y ^ 2 - x ^ 2 - w ^ 2) := by
  unfold pairedResolventGram
  ring

theorem pairedResolventGram_mono_square (r R x w y : Real)
    (hx : x ^ 2 <= w ^ 2) (hr : w ^ 2 <= r ^ 2) (hR : w ^ 2 <= R ^ 2) :
    pairedResolventGram r R w y <= pairedResolventGram r R x y := by
  have hFactor : 0 <= r ^ 2 + R ^ 2 + 6 * y ^ 2 - x ^ 2 - w ^ 2 := by
    nlinarith only [hx, hr, hR, sq_nonneg y]
  have hProduct := mul_nonneg (sub_nonneg.mpr hx) hFactor
  rw [<- pairedResolventGram_strip_difference] at hProduct
  exact sub_nonneg.mp hProduct

theorem pairedResolventDifference_nonneg_iff_gram (r R x y : Real)
    (hr : abs x < r) (hR : r < R) :
    Iff (0 <= pairedResolventDifference r R x y)
      (0 <= pairedResolventGram r R x y) := by
  have hr0 : 0 < r := (abs_nonneg x).trans_lt hr
  have hSquare : 0 < R ^ 2 - r ^ 2 := by
    have hh := mul_pos (sub_pos.mpr hR) (show 0 < R + r by linarith only [hr0, hR])
    nlinarith only [hh]
  have hFactor := mul_pos hr0 hSquare
  have hDen := mul_pos (pairedResolventDen_pos r x y hr)
    (pairedResolventDen_pos R x y (hr.trans hR))
  rw [pairedResolventDifference_formula r R x y hr hR]
  constructor
  . intro h
    by_contra hn
    have hNeg := div_neg_of_neg_of_pos
      (mul_neg_of_pos_of_neg hFactor (lt_of_not_ge hn)) hDen
    exact not_lt_of_ge h hNeg
  . intro h
    exact div_nonneg (mul_nonneg hFactor.le h) hDen.le

theorem pairedResolventGram_boundary_witness (r R w : Real)
    (hA : 0 <= r ^ 2 - w ^ 2) (hB : 0 <= R ^ 2 - w ^ 2) :
    pairedResolventGram r R w
        (Real.sqrt (Real.sqrt (r ^ 2 - w ^ 2) * Real.sqrt (R ^ 2 - w ^ 2))) =
      ((Real.sqrt (r ^ 2 - w ^ 2) + Real.sqrt (R ^ 2 - w ^ 2)) ^ 2 - 4 * w ^ 2) *
        (Real.sqrt (r ^ 2 - w ^ 2) * Real.sqrt (R ^ 2 - w ^ 2)) := by
  rw [pairedResolventGram_boundary_sos r R w _ _ _
    (Real.sq_sqrt hA) (Real.sq_sqrt hB),
    Real.sq_sqrt (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))]
  ring

theorem pairedResolventGram_boundary_nonneg_iff (w r R : Real)
    (hw : 0 <= w) (hr : w < r) (hR : r < R) :
    Iff (forall y : Real, 0 <= pairedResolventGram r R w y)
      (2 * w <= Real.sqrt (r ^ 2 - w ^ 2) + Real.sqrt (R ^ 2 - w ^ 2)) := by
  have hr0 : 0 < r := hw.trans_lt hr
  have hA : 0 < r ^ 2 - w ^ 2 := by
    have hh := mul_pos (sub_pos.mpr hr) (show 0 < r + w by linarith only [hr0, hw])
    nlinarith only [hh]
  have hB : 0 < R ^ 2 - w ^ 2 := by
    have hh := mul_pos (sub_pos.mpr (hr.trans hR))
      (show 0 < R + w by linarith only [hr0, hR, hw])
    nlinarith only [hh]
  let a : Real := Real.sqrt (r ^ 2 - w ^ 2)
  let b : Real := Real.sqrt (R ^ 2 - w ^ 2)
  have ha : 0 < a := Real.sqrt_pos.mpr hA
  have hb : 0 < b := Real.sqrt_pos.mpr hB
  have haSquare : a ^ 2 = r ^ 2 - w ^ 2 := Real.sq_sqrt hA.le
  have hbSquare : b ^ 2 = R ^ 2 - w ^ 2 := Real.sq_sqrt hB.le
  change Iff (forall y : Real, 0 <= pairedResolventGram r R w y) (2 * w <= a + b)
  constructor
  . intro h
    have hAB : 0 < a * b := mul_pos ha hb
    have hy : (Real.sqrt (a * b)) ^ 2 = a * b := Real.sq_sqrt hAB.le
    have hh := h (Real.sqrt (a * b))
    rw [pairedResolventGram_boundary_sos r R w _ a b haSquare hbSquare, hy] at hh
    norm_num at hh
    by_contra hn
    have hLess : a + b < 2 * w := lt_of_not_ge hn
    have hCoef : (a + b) ^ 2 - 4 * w ^ 2 < 0 := by
      have hp := mul_neg_of_neg_of_pos (sub_neg.mpr hLess)
        (show 0 < a + b + 2 * w by linarith only [ha, hb, hw])
      nlinarith only [hp]
    have hp := mul_neg_of_neg_of_pos hCoef hAB
    exact not_lt_of_ge hh hp
  . intro h y
    rw [pairedResolventGram_boundary_sos r R w y a b haSquare hbSquare]
    have hCoef : 0 <= (a + b) ^ 2 - 4 * w ^ 2 := by
      have hp := mul_nonneg (sub_nonneg.mpr h)
        (show 0 <= a + b + 2 * w by linarith only [ha, hb, hw])
      nlinarith only [hp]
    exact add_nonneg (sq_nonneg _) (mul_nonneg hCoef (sq_nonneg y))

theorem pairedResolventStrip_nonneg_iff (w r R : Real)
    (hw : 0 <= w) (hr : w < r) (hR : r < R) :
    Iff
      (forall x : Real, abs x <= w -> forall y : Real,
        0 <= pairedResolventDifference r R x y)
      (2 * w <= Real.sqrt (r ^ 2 - w ^ 2) + Real.sqrt (R ^ 2 - w ^ 2)) := by
  constructor
  . intro h
    apply (pairedResolventGram_boundary_nonneg_iff w r R hw hr hR).mp
    intro y
    exact (pairedResolventDifference_nonneg_iff_gram r R w y
      (by rwa [abs_of_nonneg hw]) hR).mp
        (h w (by rw [abs_of_nonneg hw]) y)
  . intro h x hx y
    have hAbs := hx.trans_lt hr
    apply (pairedResolventDifference_nonneg_iff_gram r R x y hAbs hR).mpr
    have hBoundary := (pairedResolventGram_boundary_nonneg_iff w r R hw hr hR).mpr h y
    apply hBoundary.trans
    have hxBounds := abs_le.mp hx
    have hxSquare : x ^ 2 <= w ^ 2 := by
      have hh := mul_nonneg
        (show 0 <= w - x by linarith only [hxBounds.2])
        (show 0 <= w + x by linarith only [hxBounds.1])
      nlinarith only [hh]
    have hrSquare : w ^ 2 <= r ^ 2 := by
      have hh := mul_pos (sub_pos.mpr hr)
        (show 0 < r + w by linarith only [hr, hw])
      nlinarith only [hh]
    have hRSquare : w ^ 2 <= R ^ 2 := by
      have hh := mul_pos (sub_pos.mpr (hr.trans hR))
        (show 0 < R + w by linarith only [hr, hR, hw])
      nlinarith only [hh]
    exact pairedResolventGram_mono_square r R x w y hxSquare hrSquare hRSquare

theorem pairedResolventDifference_negative_witness (w r R : Real)
    (hw : 0 <= w) (hr : w < r) (hR : r < R)
    (hFail : Real.sqrt (r ^ 2 - w ^ 2) + Real.sqrt (R ^ 2 - w ^ 2) < 2 * w) :
    pairedResolventDifference r R w
      (Real.sqrt (Real.sqrt (r ^ 2 - w ^ 2) * Real.sqrt (R ^ 2 - w ^ 2))) < 0 := by
  have hr0 : 0 < r := hw.trans_lt hr
  have hA : 0 < r ^ 2 - w ^ 2 := by
    have hh := mul_pos (sub_pos.mpr hr) (show 0 < r + w by linarith only [hr0, hw])
    nlinarith only [hh]
  have hB : 0 < R ^ 2 - w ^ 2 := by
    have hh := mul_pos (sub_pos.mpr (hr.trans hR))
      (show 0 < R + w by linarith only [hr0, hR, hw])
    nlinarith only [hh]
  have hRoots : 0 < Real.sqrt (r ^ 2 - w ^ 2) * Real.sqrt (R ^ 2 - w ^ 2) :=
    mul_pos (Real.sqrt_pos.mpr hA) (Real.sqrt_pos.mpr hB)
  have hCoef : (Real.sqrt (r ^ 2 - w ^ 2) + Real.sqrt (R ^ 2 - w ^ 2)) ^ 2 -
      4 * w ^ 2 < 0 := by
    have hh := mul_neg_of_neg_of_pos (sub_neg.mpr hFail)
      (show 0 < Real.sqrt (r ^ 2 - w ^ 2) + Real.sqrt (R ^ 2 - w ^ 2) + 2 * w by
        linarith only [Real.sqrt_pos.mpr hA, Real.sqrt_pos.mpr hB, hw])
    nlinarith only [hh]
  have hGram : pairedResolventGram r R w
      (Real.sqrt (Real.sqrt (r ^ 2 - w ^ 2) * Real.sqrt (R ^ 2 - w ^ 2))) < 0 := by
    rw [pairedResolventGram_boundary_witness r R w hA.le hB.le]
    exact mul_neg_of_neg_of_pos hCoef hRoots
  have hSquare : 0 < R ^ 2 - r ^ 2 := by
    have hh := mul_pos (sub_pos.mpr hR) (show 0 < R + r by linarith only [hr0, hR])
    nlinarith only [hh]
  have hAbs : abs w < r := by rwa [abs_of_nonneg hw]
  rw [pairedResolventDifference_formula r R w _ hAbs hR]
  exact div_neg_of_neg_of_pos (mul_neg_of_pos_of_neg (mul_pos hr0 hSquare) hGram)
    (mul_pos (pairedResolventDen_pos r w _ hAbs)
      (pairedResolventDen_pos R w _ (hAbs.trans hR)))

end Complex

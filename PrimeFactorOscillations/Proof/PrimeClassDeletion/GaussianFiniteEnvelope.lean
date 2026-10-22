/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import PrimeFactorOscillations.Helpers.ZetaZeroGeometry
import PrimeFactorOscillations.Proof.PrimeClassDeletion.GaussianRecordExponents

/-!
# Finite candidate sets and attained Gaussian zero envelopes

An explicit height cutoff controls every zero whose exponent exceeds
a fixed level, uniformly on a bounded shift interval. This supplies
the actual infinite-zero-set maximum needed by the exposure theorem.
-/

set_option autoImplicit false
set_option Elab.async false

namespace PrimeFactorOscillations.PrimeClassDeletion

theorem gaussianZeroExponent_height_bound
    (c beta gamma tau L : Real) (hc : 0 < c)
    (hb0 : 0 <= beta) (hb1 : beta <= 1)
    (hScore : L <= gaussianZeroExponent c beta gamma tau) :
    abs gamma <= 2 * (1 + c / 2 + abs L) / c + 1 + abs tau := by
  let r : Real := abs (gamma - tau)
  have hProd := mul_nonneg (sub_nonneg.mpr hb1)
    (add_nonneg (by norm_num : (0 : Real) <= 1) hb0)
  have hBetaSq : beta ^ 2 <= 1 := by nlinarith only [hProd]
  have hTop : beta + c / 2 * beta ^ 2 <= 1 + c / 2 := by
    calc
      _ <= 1 + c / 2 * 1 :=
        add_le_add hb1 (mul_le_mul_of_nonneg_left hBetaSq (by linarith only [hc]))
      _ = _ := by ring
  have hAbsSq : r ^ 2 = (gamma - tau) ^ 2 := sq_abs (gamma - tau)
  have hLower : -abs L <= L := neg_abs_le L
  have hQuad : r ^ 2 * c <= 2 * (1 + c / 2 + abs L) := by
    rw [hAbsSq]
    unfold gaussianZeroExponent at hScore
    nlinarith only [hScore, hTop, hLower]
  have hSq : r ^ 2 <= 2 * (1 + c / 2 + abs L) / c := by
    calc
      r ^ 2 = (r ^ 2 * c) / c := by field_simp [hc.ne']
      _ <= _ := div_le_div_of_nonneg_right hQuad hc.le
  have hR : r <= 2 * (1 + c / 2 + abs L) / c + 1 := by
    nlinarith only [hSq, sq_nonneg (r - 1 / 2)]
  calc
    abs gamma = abs ((gamma - tau) + tau) := by congr 1; ring
    _ <= r + abs tau := by
      simpa only [Real.norm_eq_abs] using norm_add_le (gamma - tau) tau
    _ <= _ := add_le_add hR (le_refl _)

theorem gaussianZeroExponent_uniform_candidates_finite
    (c T L : Real) (hc : 0 < c) :
    Set.Finite {z : ZetaDistinctZero | Exists fun tau : Real =>
      And (abs tau <= T) (L <= gaussianZeroExponent c z.val.re z.val.im tau)} := by
  apply (zetaDistinctZero_bounded_height_finite
    (2 * (1 + c / 2 + abs L) / c + 1 + T)).subset
  intro z hz
  cases hz with
  | intro tau ht =>
    have hBound := gaussianZeroExponent_height_bound c z.val.re z.val.im tau L hc
      z.property.2.1.le z.property.2.2.le ht.2
    exact hBound.trans (add_le_add (le_refl _) ht.1)

theorem gaussianZeroExponent_exists_max
    (c tau : Real) (hc : 0 < c) (z0 : ZetaDistinctZero) :
    Exists fun w : ZetaDistinctZero => forall z : ZetaDistinctZero,
      gaussianZeroExponent c z.val.re z.val.im tau <=
        gaussianZeroExponent c w.val.re w.val.im tau := by
  classical
  let L : Real := gaussianZeroExponent c z0.val.re z0.val.im tau
  let S : Set ZetaDistinctZero :=
    {z | L <= gaussianZeroExponent c z.val.re z.val.im tau}
  have hFinite : Set.Finite S := by
    apply (gaussianZeroExponent_uniform_candidates_finite c (abs tau) L hc).subset
    intro z hz
    exact Exists.intro tau (And.intro (le_refl _) hz)
  have hz0 : Membership.mem S z0 := le_refl L
  have hMem : Membership.mem hFinite.toFinset z0 := hFinite.mem_toFinset.mpr hz0
  have hMax := Finset.exists_max_image hFinite.toFinset
    (fun z : ZetaDistinctZero => gaussianZeroExponent c z.val.re z.val.im tau)
    (Exists.intro z0 hMem)
  cases hMax with
  | intro w hw =>
    refine Exists.intro w ?_
    intro z
    by_cases hz : Membership.mem S z
    . exact hw.2 z (hFinite.mem_toFinset.mpr hz)
    . have hBase := hw.2 z0 hMem
      have hLess : gaussianZeroExponent c z.val.re z.val.im tau < L := lt_of_not_ge hz
      exact hLess.le.trans hBase

noncomputable def gaussianZetaEnvelope (c tau : Real) : Real :=
  sSup (Set.range (fun z : ZetaDistinctZero =>
    gaussianZeroExponent c z.val.re z.val.im tau))

theorem gaussianZetaEnvelope_attained
    (c tau : Real) (hc : 0 < c) (z0 : ZetaDistinctZero) :
    Exists fun w : ZetaDistinctZero =>
      And (gaussianZetaEnvelope c tau = gaussianZeroExponent c w.val.re w.val.im tau)
        (forall z : ZetaDistinctZero, gaussianZeroExponent c z.val.re z.val.im tau <=
          gaussianZeroExponent c w.val.re w.val.im tau) := by
  cases gaussianZeroExponent_exists_max c tau hc z0 with
  | intro w hw =>
    refine Exists.intro w (And.intro ?_ hw)
    have hGreatest : IsGreatest
        (Set.range (fun z : ZetaDistinctZero =>
          gaussianZeroExponent c z.val.re z.val.im tau))
        (gaussianZeroExponent c w.val.re w.val.im tau) := by
      refine And.intro (Exists.intro w rfl) ?_
      intro a ha
      cases ha with
      | intro z hz =>
        rw [<- hz]
        exact hw z
    exact hGreatest.csSup_eq

end PrimeFactorOscillations.PrimeClassDeletion

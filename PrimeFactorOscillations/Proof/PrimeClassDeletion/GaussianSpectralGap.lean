/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Proof.PrimeClassDeletion.GaussianExposure

/-!
# A uniform exponent gap below a uniquely exposed actual zero

Only finitely many zeros have score at least B-1. Their largest
remaining score supplies one positive gap for the entire infinite
zero set, including every lower-score zero.
-/

set_option autoImplicit false
set_option Elab.async false

namespace PrimeFactorOscillations.PrimeClassDeletion

theorem gaussianZeroExponent_uniform_gap
    (c tau : Real) (hc : 0 < c) (w : ZetaDistinctZero)
    (hUnique : forall z : ZetaDistinctZero, Not (z = w) ->
      gaussianZeroExponent c z.val.re z.val.im tau <
        gaussianZeroExponent c w.val.re w.val.im tau) :
    Exists fun delta : Real => And (0 < delta) (And (delta <= 1)
      (forall z : ZetaDistinctZero, Not (z = w) ->
        gaussianZeroExponent c z.val.re z.val.im tau <=
          gaussianZeroExponent c w.val.re w.val.im tau - delta)) := by
  classical
  let B : Real := gaussianZeroExponent c w.val.re w.val.im tau
  let S : Set ZetaDistinctZero := {z | And (Not (z = w))
    (B - 1 <= gaussianZeroExponent c z.val.re z.val.im tau)}
  have hFinite : S.Finite := by
    apply (gaussianZeroExponent_uniform_candidates_finite c (abs tau) (B - 1) hc).subset
    intro z hz
    exact Exists.intro tau (And.intro (le_refl _) hz.2)
  by_cases hNonempty : S.Nonempty
  . cases hNonempty with
    | intro v hv =>
      have hMax := Finset.exists_max_image hFinite.toFinset
        (fun z : ZetaDistinctZero => gaussianZeroExponent c z.val.re z.val.im tau)
        (Exists.intro v (hFinite.mem_toFinset.mpr hv))
      cases hMax with
      | intro v2 hv2 =>
        have hMem : Membership.mem S v2 := hFinite.mem_toFinset.mp hv2.1
        let delta : Real := min 1 (B - gaussianZeroExponent c v2.val.re v2.val.im tau)
        have hDelta : 0 < delta :=
          lt_min (by norm_num) (sub_pos.mpr (hUnique v2 hMem.1))
        refine Exists.intro delta (And.intro hDelta (And.intro (min_le_left _ _) ?_))
        intro z hNe
        change gaussianZeroExponent c z.val.re z.val.im tau <= B - delta
        by_cases hScore : B - 1 <= gaussianZeroExponent c z.val.re z.val.im tau
        . have hBound := hv2.2 z (hFinite.mem_toFinset.mpr (And.intro hNe hScore))
          have hDeltaLe := min_le_right (1 : Real)
            (B - gaussianZeroExponent c v2.val.re v2.val.im tau)
          dsimp only [delta]
          linarith only [hBound, hDeltaLe]
        . have hLess := lt_of_not_ge hScore
          have hDeltaLe := min_le_left (1 : Real)
            (B - gaussianZeroExponent c v2.val.re v2.val.im tau)
          dsimp only [delta]
          linarith only [hLess, hDeltaLe]
  . refine Exists.intro 1 (And.intro (by norm_num) (And.intro (le_refl _) ?_))
    intro z hNe
    have hNot : Not (B - 1 <= gaussianZeroExponent c z.val.re z.val.im tau) := by
      intro hScore
      exact hNonempty (Exists.intro z (And.intro hNe hScore))
    exact (lt_of_not_ge hNot).le

end PrimeFactorOscillations.PrimeClassDeletion

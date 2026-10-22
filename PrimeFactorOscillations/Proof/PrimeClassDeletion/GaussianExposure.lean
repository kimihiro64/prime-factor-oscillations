/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Proof.PrimeClassDeletion.GaussianCrossings
import PrimeFactorOscillations.Proof.PrimeClassDeletion.GaussianShiftGain

/-!
# Unconditional exposure of a unique dominant zeta zero

The complete actual zero set has an attained maximum. A positive shift
with the strict gain is perturbed outside its finite crossing set.
The analytic multiplicity coefficient is retained and is nonzero.
-/

set_option autoImplicit false
set_option Elab.async false

namespace PrimeFactorOscillations.PrimeClassDeletion

private theorem exists_shift_outside_finite
    (F : Real -> Real) (M tau0 : Real) (E : Set Real)
    (hF : Continuous F) (hTau0 : 0 < tau0) (hGap : M < F tau0) (hE : E.Finite) :
    Exists fun tau : Real => And (0 < tau)
      (And (M < F tau) (And (abs tau <= abs tau0 + 1) (Not (Membership.mem E tau)))) := by
  classical
  have hPositiveOpen : IsOpen {t : Real | 0 < t} := isOpen_lt continuous_const continuous_id
  have hGapOpen : IsOpen {t : Real | M < F t} := isOpen_lt continuous_const hF
  have hNhd := (hPositiveOpen.inter hGapOpen).mem_nhds (And.intro hTau0 hGap)
  cases Metric.mem_nhds_iff.mp hNhd with
  | intro epsilon hEpsilon =>
    let d : Real := min epsilon 1
    have hD : 0 < d := lt_min hEpsilon.1 (by norm_num)
    have hInterval : (Set.Ioo (tau0 - d) (tau0 + d)).Infinite :=
      Set.Ioo_infinite (by linarith only [hD])
    have hExists : Exists fun tau : Real =>
        And (Membership.mem (Set.Ioo (tau0 - d) (tau0 + d)) tau)
          (Not (Membership.mem E tau)) := by
      by_contra hNone
      apply hInterval
      apply hE.subset
      intro tau ht
      by_contra hNot
      exact hNone (Exists.intro tau (And.intro ht hNot))
    cases hExists with
    | intro tau ht =>
      have hDist : dist tau tau0 < d := by
        rw [dist_eq_norm, Real.norm_eq_abs]
        exact abs_lt.mpr (And.intro
          (by linarith only [ht.1.1]) (by linarith only [ht.1.2]))
      have hBall : Membership.mem (Metric.ball tau0 epsilon) tau :=
        lt_of_lt_of_le hDist (min_le_left epsilon 1)
      have hProperties := hEpsilon.2 hBall
      have hAbsDiff : abs (tau - tau0) < 1 := by
        rw [dist_eq_norm, Real.norm_eq_abs] at hDist
        exact lt_of_lt_of_le hDist (min_le_right epsilon 1)
      have hAbs : abs tau <= abs tau0 + 1 := by
        calc
          abs tau = abs ((tau - tau0) + tau0) := by congr 1; ring
          _ <= abs (tau - tau0) + abs tau0 := by
            simpa only [Real.norm_eq_abs] using norm_add_le (tau - tau0) tau0
          _ <= 1 + abs tau0 := add_le_add hAbsDiff.le (le_refl _)
          _ = _ := add_comm _ _
      exact Exists.intro tau (And.intro hProperties.1
        (And.intro hProperties.2 (And.intro hAbs ht.2)))

theorem gaussianZetaEnvelope_unique_exposure
    (c : Real) (hc : 0 < c) (z0 : ZetaDistinctZero)
    (hBeta : (1 / 2 : Real) < z0.val.re) :
    Exists fun tau : Real => And (0 < tau) (Exists fun w : ZetaDistinctZero =>
      And (gaussianZetaEnvelope c tau = gaussianZeroExponent c w.val.re w.val.im tau)
        (And (Not ((((analyticOrderAt riemannZeta w.val).toNat : Complex) / w.val) = 0))
          (And (forall z : ZetaDistinctZero, Not (z = w) ->
              gaussianZeroExponent c z.val.re z.val.im tau <
                gaussianZeroExponent c w.val.re w.val.im tau)
            (max (gaussianZetaEnvelope c 0) (max ((1 / 2 : Real) + c / 8) z0.val.re) <
              gaussianZetaEnvelope c tau)))) := by
  classical
  cases gaussianZeroExponent_strict_shift_gain c hc z0 hBeta with
  | intro tau0 hWitness =>
    cases hWitness with
    | intro z1 hGain =>
      let M : Real := max (gaussianZetaEnvelope c 0)
        (max ((1 / 2 : Real) + c / 8) z0.val.re)
      let T : Real := abs tau0 + 1
      let S : Set ZetaDistinctZero := {z | Exists fun t : Real =>
        And (abs t <= T) (M <= gaussianZeroExponent c z.val.re z.val.im t)}
      let E : Set Real := gaussianCrossingSet c S
      have hFinite : S.Finite := gaussianZeroExponent_uniform_candidates_finite c T M hc
      have hE : E.Finite := gaussianCrossingSet_finite c S hFinite
      have hStrict : M < gaussianZeroExponent c z1.val.re z1.val.im tau0 :=
        max_lt_iff.mpr (And.intro hGain.2.1 (max_lt_iff.mpr hGain.2.2))
      have hContinuous : Continuous
          (fun t : Real => gaussianZeroExponent c z1.val.re z1.val.im t) := by
        unfold gaussianZeroExponent
        exact continuous_const.add (continuous_const.mul
          (continuous_const.sub ((continuous_const.sub continuous_id).pow 2)))
      cases exists_shift_outside_finite
          (fun t : Real => gaussianZeroExponent c z1.val.re z1.val.im t)
          M tau0 E hContinuous hGain.1 hStrict hE with
      | intro tau ht =>
        cases gaussianZetaEnvelope_attained c tau hc z0 with
        | intro w hw =>
          have hWin : M < gaussianZeroExponent c w.val.re w.val.im tau :=
            ht.2.1.trans_le (hw.2 z1)
          have hMemW : Membership.mem S w :=
            Exists.intro tau (And.intro ht.2.2.1 hWin.le)
          have hInj := gaussianZeroExponent_injOn_outside_crossings c tau hc S ht.2.2.2
          have hUnique : forall z : ZetaDistinctZero, Not (z = w) ->
              gaussianZeroExponent c z.val.re z.val.im tau <
                gaussianZeroExponent c w.val.re w.val.im tau := by
            intro z hNe
            apply lt_of_le_of_ne (hw.2 z)
            intro hEq
            have hMemZ : Membership.mem S z := by
              refine Exists.intro tau (And.intro ht.2.2.1 ?_)
              rw [hEq]
              exact hWin.le
            exact hNe (hInj hMemZ hMemW hEq)
          refine Exists.intro tau (And.intro ht.1 (Exists.intro w
            (And.intro hw.1 (And.intro (zetaDistinctZero_coefficient_ne_zero w)
              (And.intro hUnique ?_)))))
          rw [hw.1]
          exact hWin

end PrimeFactorOscillations.PrimeClassDeletion

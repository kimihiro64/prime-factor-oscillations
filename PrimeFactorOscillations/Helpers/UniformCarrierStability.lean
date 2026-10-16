/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.UniformCarrierBounds

/-!
# Uniform Carrier Stability

A localized inverse theorem with global-band uniqueness from a negative derivative bound.
-/

set_option autoImplicit false
set_option Elab.async false

noncomputable section
namespace PrimeFactorOscillations.UniformCarrier

theorem root_stability (g : Real -> Real) (l u B R d h E : Real)
    (hd : 0 < d) (hh : 0 < h)
    (hl : l <= B - h) (hu : B + h <= u)
    (hDiff : forall x : Real, Membership.mem (Set.Icc l u) x -> DifferentiableAt Real g x)
    (hSlope : forall x : Real, Membership.mem (Set.Icc l u) x -> deriv g x <= -d)
    (hError : abs (R - g B) <= E) (hMargin : E < d * h) :
    exists U : Real, abs (U - B) < h /\ g U = R /\
      forall V : Real, Membership.mem (Set.Icc l u) V -> g V = R -> V = U := by
  have hlB : B - h < B := by linarith
  have hBu : B < B + h := by linarith
  have hglobal (x : Real) (hx : Membership.mem (Set.Icc (B - h) (B + h)) x) :
      Membership.mem (Set.Icc l u) x :=
    And.intro (hl.trans hx.1) (hx.2.trans hu)
  have hc : ContinuousOn g (Set.Icc l u) := fun x hx =>
    (hDiff x hx).continuousAt.continuousWithinAt
  have hleft : R < g (B - h) := by
    have hi (x : Real) (hx : Membership.mem (Set.Icc (B - h) B) x) :
        Membership.mem (Set.Icc l u) x :=
      hglobal x (And.intro hx.1 (hx.2.trans hBu.le))
    choose x hx heq using exists_deriv_eq_slope g hlB
      (fun x hx => (hDiff x (hi x hx)).continuousAt.continuousWithinAt)
      (fun x hx => (hDiff x (hi x (And.intro hx.1.le hx.2.le))).differentiableWithinAt)
    have hs := hSlope x (hi x (And.intro hx.1.le hx.2.le))
    have hm := mul_le_mul_of_nonneg_right hs hh.le
    have he : deriv g x * h = g B - g (B - h) := by
      rw [heq]
      have hcanc : B - (B - h) = h := by ring
      rw [hcanc]
      field_simp [hh.ne']
    have hb := (abs_le.mp hError).2
    linarith only [hm, he, hb, hMargin]
  have hright : g (B + h) < R := by
    have hi (x : Real) (hx : Membership.mem (Set.Icc B (B + h)) x) :
        Membership.mem (Set.Icc l u) x :=
      hglobal x (And.intro (hlB.le.trans hx.1) hx.2)
    choose x hx heq using exists_deriv_eq_slope g hBu
      (fun x hx => (hDiff x (hi x hx)).continuousAt.continuousWithinAt)
      (fun x hx => (hDiff x (hi x (And.intro hx.1.le hx.2.le))).differentiableWithinAt)
    have hs := hSlope x (hi x (And.intro hx.1.le hx.2.le))
    have hm := mul_le_mul_of_nonneg_right hs hh.le
    have he : deriv g x * h = g (B + h) - g B := by
      rw [heq]
      have hcanc : B + h - B = h := by ring
      rw [hcanc]
      field_simp [hh.ne']
    have hb := (abs_le.mp hError).1
    linarith only [hm, he, hb, hMargin]
  have hContSmall : ContinuousOn g (Set.Icc (B - h) (B + h)) :=
    fun x hx => (hDiff x (hglobal x hx)).continuousAt.continuousWithinAt
  have hends : B - h <= B + h := by linarith
  choose U hUI hU using intermediate_value_Icc' hends hContSmall
    (And.intro hright.le hleft.le)
  have hsmall : abs (U - B) < h := by
    apply abs_lt.mpr
    constructor
    . have hn : Not (B - h = U) := by
        intro he
        rw [<- he] at hU
        exact hleft.ne' hU
      have hlt := lt_of_le_of_ne hUI.1 hn
      linarith
    . have hn : Not (U = B + h) := by
        intro he
        rw [he] at hU
        exact hright.ne hU
      have hlt := lt_of_le_of_ne hUI.2 hn
      linarith
  have hAnti : StrictAntiOn g (Set.Icc l u) := by
    apply strictAntiOn_of_deriv_neg (convex_Icc _ _) hc
    intro x hx
    exact (hSlope x (interior_subset hx)).trans_lt (by linarith)
  refine Exists.intro U (And.intro hsmall (And.intro hU ?_))
  intro V hV hVR
  exact hAnti.injOn hV (hglobal U hUI) (hVR.trans hU.symm)

end PrimeFactorOscillations.UniformCarrier

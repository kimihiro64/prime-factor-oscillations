/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-! # One-sided second-derivative control without an absolute Hessian bound -/

set_option autoImplicit false
set_option Elab.async false

noncomputable section

namespace PrimeFactorOscillations

theorem hamiltonian_one_sided_taylor
    (f f1 f2 : Real -> Real) (B : Real)
    (hf : forall t, Membership.mem (Set.Icc (0 : Real) 1) t ->
      HasDerivAt f (f1 t) t)
    (hf1 : forall t, Membership.mem (Set.Icc (0 : Real) 1) t ->
      HasDerivAt f1 (f2 t) t)
    (hB : forall t, Membership.mem (Set.Icc (0 : Real) 1) t -> f2 t <= B) :
    f 1 <= f 0 + f1 0 + B / 2 := by
  let G : Real -> Real := fun t => f1 t - B * t
  have hG (t : Real) (ht : Membership.mem (Set.Icc (0 : Real) 1) t) :
      HasDerivAt G (f2 t - B) t := by
    dsimp [G]
    simpa only [mul_one] using!
      (hf1 t ht).sub ((hasDerivAt_id t).const_mul B)
  have hGCont : ContinuousOn G (Set.Icc (0 : Real) 1) :=
    fun t ht => (hG t ht).continuousAt.continuousWithinAt
  have hGMono : AntitoneOn G (Set.Icc (0 : Real) 1) :=
    antitoneOn_of_hasDerivWithinAt_nonpos (convex_Icc _ _) hGCont
      (fun t ht => (hG t (interior_subset ht)).hasDerivWithinAt)
      (fun t ht => sub_nonpos.mpr (hB t (interior_subset ht)))
  have hz : Membership.mem (Set.Icc (0 : Real) 1) (0 : Real) :=
    And.intro le_rfl zero_le_one
  have ho : Membership.mem (Set.Icc (0 : Real) 1) (1 : Real) :=
    And.intro zero_le_one le_rfl
  have hSlope (t : Real) (ht : Membership.mem (Set.Icc (0 : Real) 1) t) :
      f1 t <= f1 0 + B * t := by
    have h := hGMono hz ht ht.1
    dsimp [G] at h
    nlinarith only [h]
  let F : Real -> Real := fun t => f t - f1 0 * t - (B / 2) * t ^ 2
  have hF (t : Real) (ht : Membership.mem (Set.Icc (0 : Real) 1) t) :
      HasDerivAt F (f1 t - f1 0 - B * t) t := by
    have h := ((hf t ht).sub ((hasDerivAt_id t).const_mul (f1 0))).sub
      (((hasDerivAt_id t).pow 2).const_mul (B / 2))
    change HasDerivAt F
      (f1 t - f1 0 * 1 - (B / 2) * ((2 : Real) * t ^ (2 - 1) * 1)) t at h
    have hD : f1 t - f1 0 * 1 - (B / 2) * ((2 : Real) * t ^ (2 - 1) * 1) =
        f1 t - f1 0 - B * t := by ring
    rw [hD] at h
    exact h
  have hFCont : ContinuousOn F (Set.Icc (0 : Real) 1) :=
    fun t ht => (hF t ht).continuousAt.continuousWithinAt
  have hFMono : AntitoneOn F (Set.Icc (0 : Real) 1) :=
    antitoneOn_of_hasDerivWithinAt_nonpos (convex_Icc _ _) hFCont
      (fun t ht => (hF t (interior_subset ht)).hasDerivWithinAt)
      (fun t ht => by
        have h := hSlope t (interior_subset ht)
        linarith)
  have h := hFMono hz ho zero_le_one
  dsimp [F] at h
  nlinarith only [h]

theorem hamiltonian_nonpositive_direction_taylor
    (f f1 f2 : Real -> Real) (B : Real)
    (hf : forall t, Membership.mem (Set.Icc (0 : Real) 1) t ->
      HasDerivAt f (f1 t) t)
    (hf1 : forall t, Membership.mem (Set.Icc (0 : Real) 1) t ->
      HasDerivAt f1 (f2 t) t)
    (hB : forall t, Membership.mem (Set.Icc (0 : Real) 1) t -> f2 t <= B)
    (hDirection : f1 0 <= 0) :
    f 1 <= f 0 + B / 2 := by
  have h := hamiltonian_one_sided_taylor f f1 f2 B hf hf1 hB
  linarith

end PrimeFactorOscillations

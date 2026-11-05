/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Topology.Algebra.Group.Basic

/-!
# Character gluing for a dense covariant profile

This supplies the local-to-global character step for the normalized
semi-Whittaker carrier. No automorphic or zero-free theorem is assumed.
-/

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1000000

namespace Metaplectic.DenseCharacter

variable {G A : Type*} [Group G] [TopologicalSpace G]

theorem nonzero_at_one (i : A -> G) (hi : DenseRange i) (f : G -> Complex)
    (hf : Continuous f) (rho : A -> Complex)
    (hc : forall a x, f (i a * x) = rho a * f x)
    (hn : exists x, Not (f x = 0)) : Not (f 1 = 0) := by
  intro hz
  have he : f = fun _ => (0 : Complex) := by
    apply hi.equalizer hf continuous_const
    funext a
    change f (i a) = 0
    simpa only [mul_one, hz, mul_zero] using hc a 1
  cases hn with
  | intro x hx => exact hx (congrFun he x)

variable [ContinuousMul G]

theorem cross_multiplicative (i : A -> G) (hi : DenseRange i) (f : G -> Complex)
    (hf : Continuous f) (rho : A -> Complex)
    (hc : forall a x, f (i a * x) = rho a * f x) (x y : G) :
    f (x * y) * f 1 = f x * f y := by
  have he : (fun z => f (z * y) * f 1) = fun z => f z * f y := by
    apply hi.equalizer
      ((hf.comp (continuous_id.mul continuous_const)).mul continuous_const)
      (hf.mul continuous_const)
    funext a
    change f (i a * y) * f 1 = f (i a) * f y
    have ha : f (i a) = rho a * f 1 := by
      simpa only [mul_one] using hc a 1
    rw [hc a y, ha]
    exact mul_right_comm _ _ _
  exact congrFun he x

/-- A nonzero continuous dense-covariant profile is exactly a character times f(1). -/
theorem character_exists (i : A -> G) (hi : DenseRange i) (f : G -> Complex)
    (hf : Continuous f) (rho : A -> Complex)
    (hc : forall a x, f (i a * x) = rho a * f x)
    (hn : exists x, Not (f x = 0)) :
    Not (f 1 = 0) /\
      exists chi : MonoidHom G Complex, Continuous chi /\
        (forall x, f x = f 1 * chi x) /\ (forall a, chi (i a) = rho a) := by
  have h0 := nonzero_at_one i hi f hf rho hc hn
  let chi : MonoidHom G Complex :=
    { toFun := fun x => f x / f 1
      map_one' := div_self h0
      map_mul' := by
        intro x y
        change f (x * y) / f 1 = f x / f 1 * (f y / f 1)
        field_simp [h0]
        exact cross_multiplicative i hi f hf rho hc x y }
  refine And.intro h0 (Exists.intro chi (And.intro (hf.div_const (f 1)) ?_))
  refine And.intro ?_ ?_
  . intro x
    change f x = f 1 * (f x / f 1)
    field_simp [h0]
  . intro a
    change f (i a) / f 1 = rho a
    have ha : f (i a) = rho a * f 1 := by
      simpa only [mul_one] using hc a 1
    rw [ha]
    field_simp [h0]

/-- Quadratic covariance remains quadratic after the dense extension. -/
theorem square_character_exists (i : A -> G) (hi : DenseRange i) (f : G -> Complex)
    (hf : Continuous f) (rho : A -> Complex)
    (hc : forall a x, f (i a * x) = rho a * f x)
    (hn : exists x, Not (f x = 0)) (hr : forall a, rho a ^ 2 = 1) :
    exists chi : MonoidHom G Complex, Continuous chi /\
      (forall x, f x = f 1 * chi x) /\
      (forall a, chi (i a) = rho a) /\ (forall x, chi x ^ 2 = 1) := by
  have he := character_exists i hi f hf rho hc hn
  cases he.2 with
  | intro chi hchi =>
    have hs : (fun x => chi x ^ 2) = fun _ => (1 : Complex) := by
      apply hi.equalizer (hchi.1.pow 2) continuous_const
      funext a
      change chi (i a) ^ 2 = 1
      rw [hchi.2.2 a]
      exact hr a
    exact Exists.intro chi (And.intro hchi.1
      (And.intro hchi.2.1 (And.intro hchi.2.2 (fun x => congrFun hs x))))

end Metaplectic.DenseCharacter

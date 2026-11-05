/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-!
# The complete fourfold Sp4 rational scattering calculation

These are the three-root intertwining product and all four surviving
Whittaker Weyl-cell terms in Gao, Documenta Math. 26 (2021), Section 6.4.
The root coordinates are x, q*x and q^2*x. No automorphic realization,
Euler-product continuation, or zero-free estimate is asserted here.
-/

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 2000000

namespace Metaplectic.Sp4FourInverse

variable {K : Type*} [Field K]

theorem scattering_telescope (q x : K)
    (h1 : Not (1 - x = 0)) (h2 : Not (1 - q * x = 0)) :
    (1 - q ^ (-1 : Int) * x) / (1 - x) *
      ((1 - x) / (1 - q * x)) *
      ((1 - q * x) / (1 - q ^ 2 * x)) =
        (1 - q ^ (-1 : Int) * x) / (1 - q ^ 2 * x) := by
  calc
    _ = ((1 - x) / (1 - x)) * ((1 - q * x) / (1 - q * x)) *
        ((1 - q ^ (-1 : Int) * x) / (1 - q ^ 2 * x)) := by
      simp only [div_eq_mul_inv]
      ring
    _ = _ := by rw [div_self h1, div_self h2, one_mul, one_mul]

theorem whittaker_weyl_sum (q x : K)
    (hq : Not (q = 0)) (hx : Not (x = 0))
    (h1 : Not (1 - x = 0)) (h2 : Not (1 - q * x = 0))
    (h3 : Not (1 - q ^ 2 * x = 0)) :
    (1 - q ^ (-1 : Int) * x) / (1 - q ^ 2 * x) +
      (1 - q ^ (-1 : Int) * x) / (1 - q * x) *
        ((1 - q ^ (-1 : Int)) / (1 - (q ^ 2 * x) ^ (-1 : Int))) +
      (1 - q ^ (-1 : Int) * x) / (1 - x) *
        ((1 - q ^ (-1 : Int)) / (1 - (q * x) ^ (-1 : Int))) +
      ((1 - q ^ (-1 : Int)) / (1 - (q * x) ^ (-1 : Int)) *
        ((1 - q ^ (-1 : Int)) / (1 - x ^ (-1 : Int))) +
        q ^ (-1 : Int) *
          ((1 - x) / (1 - (q * x) ^ (-1 : Int)))) =
      1 - q ^ (-1 : Int) * x := by
  have hi (z : K) (hz : Not (z = 0)) :
      1 - z ^ (-1 : Int) = -(1 - z) / z := by
    simp only [zpow_neg_one]
    field_simp
    ring
  rw [hi (q ^ 2 * x) (mul_ne_zero (pow_ne_zero 2 hq) hx),
    hi (q * x) (mul_ne_zero hq hx), hi x hx]
  simp only [zpow_neg_one]
  field_simp
  ring

/-! The abstract power-section criterion used for the split central torus. -/

section PowerSection

variable {A C E : Type*} [CommMonoid A] [CommMonoid C] [Monoid E]

theorem power_pair (B : MonoidHom A (MonoidHom A C)) (m : Nat) (a b : A) :
    B (a ^ m) (b ^ m) = (B a b) ^ (m * m) := by
  simp only [map_pow, MonoidHom.pow_apply, pow_mul]

theorem power_section_exists (B : MonoidHom A (MonoidHom A C)) (n m : Nat)
    (hdiv : Dvd.dvd n (m * m))
    (horder : forall a b : A, (B a b) ^ n = 1)
    (i : MonoidHom C E) (s : A -> E) (hs : s 1 = 1)
    (hdefect : forall a b : A, s a * s b = i (B a b) * s (a * b)) :
    exists f : MonoidHom A E, forall a : A, f a = s (a ^ m) := by
  have htrivial (a b : A) : B (a ^ m) (b ^ m) = 1 := by
    rw [power_pair]
    cases hdiv with
    | intro r hr =>
      rw [hr, pow_mul, horder]
      exact one_pow r
  let f : MonoidHom A E :=
    { toFun := fun a => s (a ^ m)
      map_one' := by simpa only [one_pow] using hs
      map_mul' := by
        intro a b
        rw [hdefect, htrivial, map_one, one_mul, mul_pow] }
  exact Exists.intro f (fun _ => rfl)

end PowerSection

end Metaplectic.Sp4FourInverse

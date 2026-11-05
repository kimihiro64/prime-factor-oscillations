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

end Metaplectic.Sp4FourInverse

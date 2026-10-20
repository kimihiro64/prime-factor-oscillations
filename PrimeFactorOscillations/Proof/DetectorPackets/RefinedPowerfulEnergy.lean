/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/

import PrimeFactorOscillations.Helpers.PowerPolynomialLaw

/-!
# RefinedPowerfulEnergy

Maintained extraction of completed detector/packet proof components.
All original theorem hypotheses and retained proof bodies are preserved.
This module alone asserts no improved zero-free boundary.
-/

set_option autoImplicit false
set_option Elab.async false

/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/

/-!
# The full reflected energy with a refined powerful-row count

The count exponent c is bounded both by O/2 and by (O+A)/3.
The latter comes from separating primes of valuation exactly two from
the 3-full remainder. This file proves the energy inequality with all
lengths, the cube variable, diagonal kernel, and an explicit offset.
The arithmetic ideal-count theorem and the high-side analytic adapter
are not declarations of this private prototype.
-/


noncomputable section
namespace PrimeFactorOscillations.RefinedPowerfulEnergy

theorem hybrid_min_cases (v z : Real) (hv : 0 <= v) :
    Or (min v (min z ((v + z) / 3)) = z)
      (v <= 2 * min v (min z ((v + z) / 3))) := by
  by_cases h : v <= min z ((v + z) / 3)
  . rw [min_eq_left h]
    exact Or.inr (by linarith)
  . have h' : min z ((v + z) / 3) <= v :=
      le_of_lt (lt_of_not_ge h)
    rw [min_eq_right h']
    by_cases hz : z <= (v + z) / 3
    . rw [min_eq_left hz]
      exact Or.inl rfl
    . have hz' : (v + z) / 3 <= z := le_of_lt (lt_of_not_ge hz)
      rw [min_eq_right hz']
      exact Or.inr (by linarith)

def energy (Ocount H S B z v l e T : Real) : Real :=
  Ocount + max H (v + l) - S - B + z -
    min v (min z ((v + z) / 3)) - l - 2 * e / 3 -
    max 0 (T - v - 3 * l - e) / 2

theorem complete_energy_bound
    (M ell O A N S B H z v l e c eps : Real)
    (heps : 0 <= eps) (hO : 0 <= O) (hN : 0 <= N)
    (hS : 0 <= S) (hB : 0 <= B)
    (hv : 0 <= v) (hl : 0 <= l) (he : -eps <= e)
    (htotal : M + ell <= 1)
    (hrow : H + O <= M + eps)
    (hactive : 2 * A <= O + eps)
    (hz : z <= ell + eps) (hNA : N <= A)
    (hcount2 : 2 * c <= O + 2 * eps)
    (hcount3 : 3 * c <= O + A + eps)
    (hretain : v + 3 * l + e <=
      2 * H + 2 * A + 2 * z - 1 - ell - N - 3 * B + eps) :
    energy c H S B z v l e
        (2 * H + 2 * A + 2 * z - 1 - ell - N - 3 * B) <=
      M + max 0 ((1 + 2 * ell - 2 * M) / 3) + 10 * eps := by
  let T := 2 * H + 2 * A + 2 * z - 1 - ell - N - 3 * B
  let u := min v (min z ((v + z) / 3))
  have ht : T <= H + 4 * eps := by
    dsimp [T]
    linarith
  have hyr : v + 3 * l + e <= T + eps := hretain
  have hvl : v + l <= H + 6 * eps := by linarith
  have hmax : max H (v + l) <= H + 6 * eps :=
    max_le (by linarith) hvl
  have hk0 : 0 <= max 0 (T - v - 3 * l - e) := le_max_left _ _
  have hk : T - v - 3 * l - e <= max 0 (T - v - 3 * l - e) :=
    le_max_right _ _
  have hg0 : 0 <= max 0 ((1 + 2 * ell - 2 * M) / 3) := le_max_left _ _
  have hg : (1 + 2 * ell - 2 * M) / 3 <=
      max 0 ((1 + 2 * ell - 2 * M) / 3) := le_max_right _ _
  have hcases : Or (u = z) (v <= 2 * u) := hybrid_min_cases v z hv
  change c + max H (v + l) - S - B + z - u - l - 2 * e / 3 -
      max 0 (T - v - 3 * l - e) / 2 <=
    M + max 0 ((1 + 2 * ell - 2 * M) / 3) + 10 * eps
  rcases hcases with hu | hu
  . rw [hu]
    linarith
  . have hsave : T / 3 - eps / 3 <=
        u + l + 2 * e / 3 + max 0 (T - v - 3 * l - e) / 2 := by
      linarith
    have hmain :
        c + H - S - B + z - T / 3 <=
          (M + 1 + 2 * ell) / 3 + eps := by
      dsimp [T]
      linarith
    linarith

theorem quarter_slot_consumer (d : Real) (hd : 0 <= d) :
    -d + max 0 ((1 + 2 * ((1 : Real) / 4 - d) -
      2 * ((3 : Real) / 4 - 2 * d)) / 3) / 2 = -2 * d / 3 := by
  have h : 0 <= (1 + 2 * ((1 : Real) / 4 - d) -
      2 * ((3 : Real) / 4 - 2 * d)) / 3 := by linarith
  rw [max_eq_right h]
  ring

def highExponent
    (a sigma h ly ell q d R delta z0 : Real) : Real :=
  a - sigma + h * (z0 - 1 / 6) - a * ly - ell / 2 +
    q * ell + d * (R + delta / 2 - z0)

theorem quarter_geometry_floor (q : Real) :
    highExponent (51 / 100) (41 / 48) (7 / 8) (3 / 8)
      (1 / 4) q (7 / 8) 1 (1 / 50) (17 / 50) =
        31 / 400 + q / 4 := by
  dsimp [highExponent]
  ring

/-- This refutes the old pointwise floor-bin consumer at the new geometry.
It is not an obstruction to a bound retaining the signed row phases. -/
theorem quarter_geometry_floor_gap (q beta : Real)
    (hq : 0 <= q) (hb : beta <= 7 / 8) :
    17 / 300 <=
      highExponent (51 / 100) (41 / 48) (7 / 8) (3 / 8)
        (1 / 4) q (7 / 8) 1 (1 / 50) (17 / 50) -
      (beta - 41 / 48) := by
  rw [quarter_geometry_floor]
  linarith

end PrimeFactorOscillations.RefinedPowerfulEnergy

/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/

import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import PrimeFactorOscillations.Assembly.DetectorPackets.QuarticPrimitiveTransfer

/-!
# QuarticTypeICompletion

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
# The local main term for arbitrary outer moduli

The primitive quartic residue has fourth-power periodicity before its
prime-density factor is inserted. Completing a fourth power therefore
changes the main density at p^(4*t+j) to v(p)/Np^(3*t+j), rather than
v(p)/Np^(4*t+j). This module proves the local rational identities and
their exact valuation consumer. The progression Voronoi estimate and
the analytic Type I bound are not asserted here.
-/


noncomputable section

namespace PrimeFactorOscillations.QuarticTypeICompletion

def primitiveDensity (q : Real) : Real := q / (q + 1)

def correction (q : Real) : Real := q ^ 2 / (q ^ 2 + q - 1)

def localPole (q : Real) (e : Nat) : Real :=
  if e = 0 then 1 else correction q / q ^ (e - e / 4)

theorem denominator_pos {q : Real} (hq : 2 <= q) :
    0 < q ^ 2 + q - 1 := by
  nlinarith [sq_nonneg q]

theorem density_existing_prime {q : Real} (hq : 2 <= q) :
    primitiveDensity q * (1 + 1 / q) = 1 := by
  have hq0 : Not (q = 0) := by linarith
  have hq1 : Not (q + 1 = 0) := by linarith
  dsimp [primitiveDensity]
  field_simp [hq0, hq1]

theorem density_new_prime {q : Real} (hq : 2 <= q) :
    primitiveDensity q * (1 + correction q / q ^ 2) =
      correction q := by
  have hq0 : Not (q = 0) := by linarith
  have hq1 : Not (q + 1 = 0) := by linarith
  have hd : Not (q ^ 2 + q - 1 = 0) :=
    ne_of_gt (denominator_pos hq)
  dsimp [primitiveDensity, correction]
  field_simp [hq0, hq1, hd]
  have hi := div_self hd
  ring_nf at hi
  ring_nf
  nlinarith only [hi]

theorem fourth_power_exponent (t j : Nat) (hj : j < 4) :
    (4 * t + j) - (4 * t + j) / 4 = 3 * t + j := by
  omega

theorem localPole_fourth_power (q : Real) (t j : Nat)
    (hj : j < 4) (he : 0 < 4 * t + j) :
    localPole q (4 * t + j) =
      correction q / q ^ (3 * t + j) := by
  unfold localPole
  rw [ite_eq_right (Nat.ne_of_gt he), fourth_power_exponent t j hj]

theorem localPole_small (q : Real) (j : Nat)
    (hj : j < 4) (hj0 : 0 < j) :
    localPole q j = correction q / q ^ j := by
  unfold localPole
  have hdiv : j / 4 = 0 := Nat.div_eq_of_lt hj
  simp only [ite_eq_right (Nat.ne_of_gt hj0), hdiv, Nat.sub_zero]

/-- The local main term from fourth-power completion, including the
extra divisibility correction at a new prime. -/
theorem localPole_completion {q : Real} (hq : 2 <= q)
    (t j : Nat) (ht : 0 < t) (hj : j < 4) :
    primitiveDensity q / q ^ (3 * t) *
        (localPole q j + localPole q (max j 1) / q) =
      localPole q (4 * t + j) := by
  have hq0 : Not (q = 0) := by linarith
  have hqt : Not (q ^ (3 * t) = 0) := pow_ne_zero _ hq0
  have he : 0 < 4 * t + j := by omega
  rw [localPole_fourth_power q t j hj he]
  by_cases hj0 : j = 0
  case pos =>
    subst j
    have hzero : localPole q 0 = 1 := rfl
    have hone : localPole q 1 = correction q / q := by
      unfold localPole
      norm_num
    rw [hzero, show max 0 1 = 1 from rfl, hone, Nat.add_zero]
    calc
      _ = (primitiveDensity q * (1 + correction q / q ^ 2)) /
          q ^ (3 * t) := by
        field_simp [hq0, hqt]
      _ = _ := by rw [density_new_prime hq]
  case neg =>
    have hjp : 0 < j := Nat.pos_of_ne_zero hj0
    have hmax : max j 1 = j := max_eq_left (by omega)
    rw [hmax, localPole_small q j hj hjp, pow_add]
    have hold := density_existing_prime hq
    have hqj : Not (q ^ j = 0) := pow_ne_zero _ hq0
    calc
      _ = (primitiveDensity q * (1 + 1 / q)) *
          (correction q / (q ^ (3 * t) * q ^ j)) := by
        field_simp [hq0, hqt, hqj]
      _ = _ := by rw [hold, one_mul]

end PrimeFactorOscillations.QuarticTypeICompletion


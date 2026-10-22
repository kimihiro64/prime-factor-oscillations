/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Complete historical and one-period bounds for a discounted cosine

The earlier-wave tail follows from sin(t)<=t and 1+k*t<=exp(k*t).
The one-period maximum follows from the exact signed derivative.
-/

set_option autoImplicit false
set_option Elab.async false

namespace PrimeFactorOscillations.PrimeClassDeletion

theorem cosine_tangent_exponential_bound (k a t : Real) (hk : 0 <= k)
    (hcos : 0 <= Real.cos a) (hsin : Real.sin a = k * Real.cos a) (ht : 0 <= t) :
    Real.cos (a - t) <= Real.cos a * Real.exp (k * t) := by
  rw [Real.cos_sub, hsin]
  have hsinle := mul_le_mul_of_nonneg_left (Real.sin_le ht) hk
  have hcosle := Real.cos_le_one t
  have hlinear : Real.cos t + k * Real.sin t <= 1 + k * t :=
    _root_.add_le_add hcosle hsinle
  have h := mul_le_mul_of_nonneg_left hlinear hcos
  have he := mul_le_mul_of_nonneg_left (Real.add_one_le_exp (k * t)) hcos
  nlinarith only [h, he]

theorem growingCosine_hasDerivAt (k a r : Real)
    (hsin : Real.sin a = k * Real.cos a) :
    HasDerivAt (fun x : Real => Real.exp (k * x) * Real.cos (a + x))
      (-(Real.exp (k * r) * Real.cos a * (k * k + 1)) * Real.sin r) r := by
  have h := (((hasDerivAt_id r).const_mul k).exp).mul
    (((hasDerivAt_id r).const_add a).cos)
  change HasDerivAt (fun x : Real => Real.exp (k * x) * Real.cos (a + x))
    (Real.exp (k * r) * (k * 1) * Real.cos (a + r) +
      Real.exp (k * r) * (-Real.sin (a + r) * 1)) r at h
  have hid : -(Real.exp (k * r) * Real.cos a * (k * k + 1)) * Real.sin r =
      Real.exp (k * r) * (k * 1) * Real.cos (a + r) +
        Real.exp (k * r) * (-Real.sin (a + r) * 1) := by
    rw [Real.cos_add, Real.sin_add, hsin]
    ring
  rw [hid]
  exact h

theorem growingCosine_antitone (k a : Real) (hcos : 0 <= Real.cos a)
    (hsin : Real.sin a = k * Real.cos a) :
    AntitoneOn (fun r : Real => Real.exp (k * r) * Real.cos (a + r))
      (Set.Icc 0 Real.pi) := by
  have hc : Continuous (fun r : Real => Real.exp (k * r) * Real.cos (a + r)) :=
    continuous_iff_continuousAt.mpr (fun r => (growingCosine_hasDerivAt k a r hsin).continuousAt)
  apply antitoneOn_of_hasDerivWithinAt_nonpos (convex_Icc _ _) hc.continuousOn
    (fun r _ => (growingCosine_hasDerivAt k a r hsin).hasDerivWithinAt)
  intro r hr
  have hin := interior_subset hr
  have hsinr := Real.sin_nonneg_of_nonneg_of_le_pi hin.1 hin.2
  have hp : 0 <= Real.exp (k * r) * Real.cos a * (k * k + 1) :=
    mul_nonneg (mul_nonneg (Real.exp_pos _).le hcos) (by nlinarith only [sq_nonneg k])
  exact mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hp) hsinr

theorem growingCosine_monotone (k a : Real) (hcos : 0 <= Real.cos a)
    (hsin : Real.sin a = k * Real.cos a) :
    MonotoneOn (fun r : Real => Real.exp (k * r) * Real.cos (a + r))
      (Set.Icc Real.pi (2 * Real.pi)) := by
  have hc : Continuous (fun r : Real => Real.exp (k * r) * Real.cos (a + r)) :=
    continuous_iff_continuousAt.mpr (fun r => (growingCosine_hasDerivAt k a r hsin).continuousAt)
  apply monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc _ _) hc.continuousOn
    (fun r _ => (growingCosine_hasDerivAt k a r hsin).hasDerivWithinAt)
  intro r hr
  have hin := interior_subset hr
  have hsinr : Real.sin r <= 0 := by
    have h := Real.sin_nonpos_of_nonpos_of_neg_pi_le
      (show r - 2 * Real.pi <= 0 by linarith only [hin.2])
      (show -Real.pi <= r - 2 * Real.pi by linarith only [hin.1])
    simpa only [Real.sin_sub_two_pi] using h
  have hp : 0 <= Real.exp (k * r) * Real.cos a * (k * k + 1) :=
    mul_nonneg (mul_nonneg (Real.exp_pos _).le hcos) (by nlinarith only [sq_nonneg k])
  exact mul_nonneg_of_nonpos_of_nonpos (neg_nonpos.mpr hp) hsinr

theorem growingCosine_historical_bound (k a r : Real) (hk : 0 <= k)
    (hcos : 0 <= Real.cos a) (hsin : Real.sin a = k * Real.cos a) (hr : r <= 0) :
    Real.exp (k * r) * Real.cos (a + r) <= Real.cos a := by
  have h := cosine_tangent_exponential_bound k a (-r) hk hcos hsin (neg_nonneg.mpr hr)
  rw [sub_neg_eq_add] at h
  calc
    Real.exp (k * r) * Real.cos (a + r) <=
        Real.exp (k * r) * (Real.cos a * Real.exp (k * -r)) :=
      mul_le_mul_of_nonneg_left h (Real.exp_pos _).le
    _ = Real.cos a := by
      rw [mul_left_comm, <- Real.exp_add]
      ring_nf
      rw [Real.exp_zero, mul_one]

theorem growingCosine_full_prefix_bound (k a d r : Real) (hk : 0 <= k)
    (hcos : 0 <= Real.cos a) (hsin : Real.sin a = k * Real.cos a)
    (hd : 0 <= d) (hd2 : d <= 2 * Real.pi) (hrd : r <= d) :
    Real.exp (k * r) * Real.cos (a + r) <=
      max (Real.cos a) (Real.exp (k * d) * Real.cos (a + d)) := by
  by_cases hr : r <= 0
  case pos =>
    exact (growingCosine_historical_bound k a r hk hcos hsin hr).trans (le_max_left _ _)
  case neg =>
    have hr0 : 0 <= r := (lt_of_not_ge hr).le
    by_cases hrpi : r <= Real.pi
    case pos =>
      have h := growingCosine_antitone k a hcos hsin
        (And.intro (le_refl 0) Real.pi_pos.le) (And.intro hr0 hrpi) hr0
      simp only [mul_zero, Real.exp_zero, add_zero, one_mul] at h
      exact h.trans (le_max_left _ _)
    case neg =>
      have hpi : Real.pi <= r := (lt_of_not_ge hrpi).le
      have h := growingCosine_monotone k a hcos hsin
        (And.intro hpi (hrd.trans hd2)) (And.intro (hpi.trans hrd) hd2) hrd
      exact h.trans (le_max_right _ _)

end PrimeFactorOscillations.PrimeClassDeletion

/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.LogGaussianRealTilt

/-!
# A complete physical upper-tail bound

Exponential tilting controls the actual supported tail, with no
discarded large-input term. Its later logarithmic specialization
has exponent -1+c/2 after multiplying by the physical factor X.
-/

set_option autoImplicit false
set_option Elab.async false

open MeasureTheory

namespace PrimeFactorOscillations.PrimeClassDeletion

theorem logGaussianDensity_weighted_real_tilt_integrable
    (V t L : Real) (hV : 0 < V) :
    Integrable (fun u : Real =>
      Real.exp (t * u) * (L + abs u) * logGaussianDensity V u) := by
  have h := ((logGaussianDensity_real_tilt_integrable V t hV).const_mul L).add
    (logGaussianDensity_real_abs_tilt_integrable V t hV)
  apply h.congr
  filter_upwards with u
  dsimp only [Pi.add_apply]
  ring

theorem logGaussianDensity_weighted_real_tilt_integral_bound
    (V t L : Real) (hV : 0 < V) :
    (integral volume fun u : Real =>
      Real.exp (t * u) * (L + abs u) * logGaussianDensity V u) <=
        Real.exp (V * t ^ 2 / 2) *
          (L + abs (V * t) + Real.sqrt (2 * V / Real.pi)) := by
  have hMass := logGaussianDensity_real_tilt_integrable V t hV
  have hAbs := logGaussianDensity_real_abs_tilt_integrable V t hV
  have hPoint : (fun u : Real =>
      Real.exp (t * u) * (L + abs u) * logGaussianDensity V u) =
    (fun u : Real => L * (Real.exp (t * u) * logGaussianDensity V u) +
      Real.exp (t * u) * abs u * logGaussianDensity V u) := by
    funext u
    ring
  rw [hPoint, integral_add (hMass.const_mul L) hAbs, integral_const_mul,
    logGaussianDensity_real_tilt_integral V t hV]
  have hBound := logGaussianDensity_real_abs_tilt_integral_bound V t hV
  nlinarith only [hBound]

theorem logGaussianDensity_chernoff_tail_bound
    (V L h lambda : Real) (hV : 0 < V) (hL : 0 <= L) (hLambda : 0 <= lambda) :
    (integral volume ((Set.Ioi h).indicator (fun u : Real =>
      Real.exp u * (L + abs u) * logGaussianDensity V u))) <=
        Real.exp (-lambda * h + V * (1 + lambda) ^ 2 / 2) *
          (L + abs (V * (1 + lambda)) + Real.sqrt (2 * V / Real.pi)) := by
  classical
  let F : Real -> Real := fun u =>
    Real.exp u * (L + abs u) * logGaussianDensity V u
  let M : Real -> Real := fun u =>
    Real.exp (-lambda * h) *
      (Real.exp ((1 + lambda) * u) * (L + abs u) * logGaussianDensity V u)
  have hF : Integrable F := by
    simpa only [one_mul] using logGaussianDensity_weighted_real_tilt_integrable V 1 L hV
  have hM : Integrable M :=
    (logGaussianDensity_weighted_real_tilt_integrable V (1 + lambda) L hV).const_mul _
  have hPoint : forall u : Real, (Set.Ioi h).indicator F u <= M u := by
    intro u
    have hDensity := (logGaussianDensity_pos V u hV).le
    have hWeight : 0 <= L + abs u := add_nonneg hL (abs_nonneg _)
    by_cases hu : h < u
    . have huSet : Membership.mem (Set.Ioi h) u := hu
      rw [Set.indicator_of_mem huSet]
      have hExp : Real.exp u <= Real.exp (-lambda * h) * Real.exp ((1 + lambda) * u) := by
        rw [<- Real.exp_add]
        apply Real.exp_le_exp.mpr
        have hProduct := mul_nonneg hLambda (sub_nonneg.mpr hu.le)
        nlinarith only [hProduct]
      calc
        _ <= (Real.exp (-lambda * h) * Real.exp ((1 + lambda) * u)) *
            (L + abs u) * logGaussianDensity V u :=
          mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_right hExp hWeight) hDensity
        _ = M u := by dsimp only [M]; ring
    . have huSet : Not (Membership.mem (Set.Ioi h) u) := hu
      rw [Set.indicator_of_notMem huSet]
      dsimp only [M]
      exact mul_nonneg (Real.exp_pos _).le
        (mul_nonneg (mul_nonneg (Real.exp_pos _).le hWeight) hDensity)
  calc
    _ <= integral volume M :=
      integral_mono_ae (hF.indicator measurableSet_Ioi) hM
        (Filter.Eventually.of_forall hPoint)
    _ = Real.exp (-lambda * h) *
        (integral volume fun u : Real =>
          Real.exp ((1 + lambda) * u) * (L + abs u) * logGaussianDensity V u) :=
      integral_const_mul _ _
    _ <= Real.exp (-lambda * h) *
        (Real.exp (V * (1 + lambda) ^ 2 / 2) *
          (L + abs (V * (1 + lambda)) + Real.sqrt (2 * V / Real.pi))) :=
      mul_le_mul_of_nonneg_left
        (logGaussianDensity_weighted_real_tilt_integral_bound V (1 + lambda) L hV)
        (Real.exp_pos _).le
    _ = _ := by rw [Real.exp_add]; ring

end PrimeFactorOscillations.PrimeClassDeletion

import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Reference triple integral budget

The ordered three-factor comparison region reduces, by ordinary integration,
to the integral of log(u)/(1+u) from 1 to 2. This module bounds that
one-dimensional integral by 59/400 using a rational polynomial majorant.
It also verifies its fractional-linear change of variables.

The resulting reference coefficient is greater than 141/200. This controls
only a comparison term: it supplies no prime-pair or ascent positivity.
-/

set_option autoImplicit false

noncomputable section

namespace PrimeFactorOscillations.ReferenceTriple

private def logMajorant (t : Real) : Real :=
  2 * (t + t ^ 3 / 3 + t ^ 5 / 5 + (9 / 8 : Real) * t ^ 7)

private def geometricMajorant (t : Real) : Real :=
  1 + t + t ^ 2 + t ^ 3 + t ^ 4 + t ^ 5 + (3 / 2 : Real) * t ^ 6

private def integralMajorant (t : Real) : Real := logMajorant t * geometricMajorant t

private theorem log_ratio_le_majorant (t : Real) (ht : 0 <= t) (htop : t <= 1 / 3) :
    Real.log ((1 + t) / (1 - t)) <= logMajorant t := by
  have hsq : t ^ 2 <= (1 / 9 : Real) := by nlinarith
  have htail : t ^ 7 / (1 - t ^ 2) <= (9 / 8 : Real) * t ^ 7 := by
    have h := div_le_div_of_nonneg_left (pow_nonneg ht 7)
      (by norm_num : (0 : Real) < 8 / 9) (by linarith : (8 / 9 : Real) <= 1 - t ^ 2)
    convert h using 1
    ring
  have h := Real.log_div_le_sum_range_add ht (by linarith : t < 1) 3
  norm_num [Finset.sum_range_succ] at h
  dsimp [logMajorant]
  linarith

private theorem reciprocal_le_majorant (t : Real) (ht : 0 <= t) (htop : t <= 1 / 3) :
    1 / (1 - t) <= geometricMajorant t := by
  have hden : Not (1 - t = 0) := by linarith
  have heq : geometricMajorant t - 1 / (1 - t) =
      t ^ 6 * (1 - 3 * t) / (2 * (1 - t)) := by
    dsimp [geometricMajorant]
    field_simp
    ring
  have h := div_nonneg
    (mul_nonneg (pow_nonneg ht 6) (show (0 : Real) <= 1 - 3 * t by linarith))
    (show (0 : Real) <= 2 * (1 - t) by linarith)
  linarith

private theorem integrand_le_majorant (t : Real) (ht : 0 <= t) (htop : t <= 1 / 3) :
    Real.log ((1 + t) / (1 - t)) / (1 - t) <= integralMajorant t := by
  have hden : 0 <= 1 / (1 - t) := div_nonneg zero_le_one (by linarith)
  have hlog : 0 <= logMajorant t := by dsimp [logMajorant]; positivity
  calc
    Real.log ((1 + t) / (1 - t)) / (1 - t) =
        Real.log ((1 + t) / (1 - t)) * (1 / (1 - t)) := by ring
    _ <= logMajorant t * (1 / (1 - t)) :=
      mul_le_mul_of_nonneg_right (log_ratio_le_majorant t ht htop) hden
    _ <= integralMajorant t :=
      mul_le_mul_of_nonneg_left (reciprocal_le_majorant t ht htop) hlog

private theorem integral_majorant_value :
    intervalIntegral integralMajorant 0 (1 / 3) MeasureTheory.volume =
      (62677569433 / 425577952800 : Real) := by
  let coeff : Nat -> Real
    | 1 => 2 / 1
    | 2 => 2 / 1
    | 3 => 8 / 3
    | 4 => 8 / 3
    | 5 => 46 / 15
    | 6 => 46 / 15
    | 7 => 758 / 120
    | 8 => 398 / 120
    | 9 => 146 / 40
    | 10 => 106 / 40
    | 11 => 114 / 40
    | 12 => 18 / 8
    | 13 => 54 / 16
    | _ => 0
  have hpoly : integralMajorant = fun t : Real =>
      (Finset.range 14).sum (fun n => coeff n * t ^ n) := by
    funext t
    norm_num [Finset.sum_range_succ, coeff, integralMajorant, logMajorant,
      geometricMajorant]
    ring
  rw [hpoly]
  rw [intervalIntegral.integral_finsetSum
    (s := Finset.range 14) (f := fun n t => coeff n * t ^ n)
    (fun n _ => (continuous_const.mul (continuous_id.pow n)).intervalIntegrable 0 (1 / 3))]
  simp only [intervalIntegral.integral_const_mul, integral_pow]
  norm_num [Finset.sum_range_succ, coeff]

private theorem transformed_reference_integral_lt :
    intervalIntegral (fun t : Real => Real.log ((1 + t) / (1 - t)) / (1 - t))
        0 (1 / 3) MeasureTheory.volume < (59 / 400 : Real) := by
  have hden : forall t : Real, Set.Icc (0 : Real) (1 / 3) t -> Not (1 - t = 0) := by
    intro t ht
    linarith [ht.2]
  have hid : ContinuousOn (fun t : Real => t) (Set.Icc (0 : Real) (1 / 3)) :=
    continuous_id.continuousOn
  have hc : ContinuousOn (fun t : Real => (1 + t) / (1 - t))
      (Set.Icc (0 : Real) (1 / 3)) :=
    (continuous_const.continuousOn.add hid).div (continuous_const.continuousOn.sub hid) hden
  have hf : ContinuousOn
      (fun t : Real => Real.log ((1 + t) / (1 - t)) / (1 - t))
      (Set.Icc (0 : Real) (1 / 3)) := by
    refine (hc.log ?_).div (continuous_const.continuousOn.sub hid) hden
    intro t ht
    exact div_ne_zero (by linarith [ht.1]) (hden t ht)
  have hfi : IntervalIntegrable
      (fun t : Real => Real.log ((1 + t) / (1 - t)) / (1 - t))
      MeasureTheory.volume 0 (1 / 3) := by
    apply ContinuousOn.intervalIntegrable
    simpa only [Set.uIcc_of_le (by norm_num : (0 : Real) <= 1 / 3)] using hf
  have hp : Continuous integralMajorant := by
    change Continuous (fun t : Real =>
      2 * (t + t ^ 3 / 3 + t ^ 5 / 5 + (9 / 8 : Real) * t ^ 7) *
        (1 + t + t ^ 2 + t ^ 3 + t ^ 4 + t ^ 5 + (3 / 2 : Real) * t ^ 6))
    fun_prop
  have h := intervalIntegral.integral_mono_on (by norm_num : (0 : Real) <= 1 / 3)
    hfi (hp.intervalIntegrable 0 (1 / 3))
    (fun t ht => integrand_le_majorant t ht.1 ht.2)
  rw [integral_majorant_value] at h
  linarith

private theorem reference_integral_eq_transformed :
    intervalIntegral (fun u : Real => Real.log u / (1 + u))
        1 2 MeasureTheory.volume =
      intervalIntegral (fun t : Real => Real.log ((1 + t) / (1 - t)) / (1 - t))
        0 (1 / 3) MeasureTheory.volume := by
  have hden : forall t : Real, Set.Icc (0 : Real) (1 / 3) t -> Not (1 - t = 0) := by
    intro t ht
    linarith [ht.2]
  have hid : ContinuousOn (fun t : Real => t) (Set.Icc (0 : Real) (1 / 3)) :=
    continuous_id.continuousOn
  have hc : ContinuousOn (fun t : Real => (1 + t) / (1 - t))
      (Set.uIcc (0 : Real) (1 / 3)) := by
    rw [Set.uIcc_of_le (by norm_num : (0 : Real) <= 1 / 3)]
    exact (continuous_const.continuousOn.add hid).div
      (continuous_const.continuousOn.sub hid) hden
  have hd : forall t : Real, Set.Icc (0 : Real) (1 / 3) t ->
      HasDerivAt (fun t : Real => (1 + t) / (1 - t)) (2 / (1 - t) ^ 2) t := by
    intro t ht
    have h := ((hasDerivAt_id t).const_add 1).div
      ((hasDerivAt_id t).const_sub 1) (hden t ht)
    convert h using 1
    next => rfl
    next => dsimp; ring
  have hi : forall t : Real,
      Set.Ioo (min (0 : Real) (1 / 3)) (max (0 : Real) (1 / 3)) t ->
      HasDerivAt (fun t : Real => (1 + t) / (1 - t)) (2 / (1 - t) ^ 2) t := by
    intro t ht
    norm_num only [min_eq_left (by norm_num : (0 : Real) <= 1 / 3),
      max_eq_right (by norm_num : (0 : Real) <= 1 / 3)] at ht
    exact hd t (And.intro ht.1.le ht.2.le)
  have hsub := intervalIntegral.integral_comp_mul_deriv_of_deriv_nonneg
    (g := fun u : Real => Real.log u / (1 + u)) hc hi
    (fun t _ => div_nonneg (by norm_num : (0 : Real) <= 2) (sq_nonneg (1 - t)))
  norm_num at hsub
  rw [<- hsub]
  apply intervalIntegral.integral_congr
  intro t ht
  have ht' : (0 : Real) <= t /\ t <= (1 / 3 : Real) := by
    simpa [Set.uIcc_of_le (by norm_num : (0 : Real) <= 1 / 3)] using ht
  have hn : Not (1 - t = 0) := by linarith [ht'.2]
  dsimp [Function.comp_apply]
  field_simp
  ring

/-- The comparison-triple integral has a strict rational upper bound. -/
theorem reference_integral_lt :
    intervalIntegral (fun u : Real => Real.log u / (1 + u))
        1 2 MeasureTheory.volume < (59 / 400 : Real) := by
  rw [reference_integral_eq_transformed]
  exact transformed_reference_integral_lt

/-- Removing twice the comparison integral leaves more than 141/200. -/
theorem reference_supply_coefficient_gt :
    (141 / 200 : Real) <
      1 - 2 * intervalIntegral (fun u : Real => Real.log u / (1 + u))
        1 2 MeasureTheory.volume := by
  linarith [reference_integral_lt]


end PrimeFactorOscillations.ReferenceTriple

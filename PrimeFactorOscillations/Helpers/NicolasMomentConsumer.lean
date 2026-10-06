/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.NicolasPositiveArea
import PrimeFactorOscillations.Helpers.NicolasPrimePowerAsymptotic

/-!
# Conditional growing-moment implication for RH

The unconditional prime-square bias gives the pointwise signed allowance.
A moment of order 2*ceil(log(x)/(8*log(2))) then bounds the positive area at
quarter-power scale. The uniform growing-moment bound remains an explicit
hypothesis: this module proves its RH consumer, not the missing estimate.
-/

set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace PrimeFactorOscillations
open Filter MeasureTheory Set Robin1984

def nicolasMomentWave (x : Real) : Real :=
  (x ^ (1 / 2 : Real) * Real.log x) * nicolasJ x

def nicolasMomentOrder (x : Real) : Nat :=
  2 * Nat.ceil (Real.log x / (8 * Real.log 2))

theorem eventually_nicolasLog_le_moment_wave :
    Filter.Eventually (fun x : Real =>
      nicolasLogMertensOscillation x <=
        (nicolasMomentWave x - 1) / (x ^ (1 / 2 : Real) * Real.log x)) atTop := by
  have hTail := tendsto_nicolasPrimePowerTail_scaled.eventually
    (Ioi_mem_nhds (by norm_num : (3 / 2 : Real) < 2))
  have hSmall : Tendsto (fun x : Real =>
      4 * (Real.log x / x ^ (1 / 2 : Real))) atTop (nhds 0) := by
    simpa only [mul_zero] using
      ((isLittleO_log_rpow_atTop (by norm_num : (0 : Real) < 1 / 2)).tendsto_div_nhds_zero).const_mul 4
  filter_upwards [hTail, hSmall.eventually_lt_const (by norm_num : (0 : Real) < 1 / 2),
    eventually_ge_atTop (3 : Real)] with x ht he hx
  have hx0 : 0 < x := by linarith
  have hx1 : 1 < x := by linarith
  have hp : 0 < x ^ (1 / 2 : Real) := Real.rpow_pos_of_pos hx0 _
  have hl : 0 < Real.log x := Real.log_pos hx1
  have hs : 0 < x ^ (1 / 2 : Real) * Real.log x := mul_pos hp hl
  have hsquare : x ^ (1 / 2 : Real) * x ^ (1 / 2 : Real) = x := by
    rw [<- Real.rpow_add hx0]
    norm_num
  have hFour : 4 / x * (x ^ (1 / 2 : Real) * Real.log x) =
      4 * (Real.log x / x ^ (1 / 2 : Real)) := by
    field_simp
    nlinarith only [hsquare]
  have hKInt := nicolasThetaTail_integrableOn_Ioi_two.mono_set
    (Ioi_subset_Ioi (le_trans (by norm_num) hx))
  have hJInt := nicolasPsiTail_integrableOn_Ioi_three.mono_set (Ioi_subset_Ioi hx)
  have hIdentity := nicolasJ_eq_K_add_primePowerTail hKInt hJInt
  have hLog := mul_le_mul_of_nonneg_right
    (nicolasLogMertensOscillation_le_K_add_four_div hx) hs.le
  rw [add_mul, hFour] at hLog
  have hc : ((nicolasMomentWave x - 1) /
      (x ^ (1 / 2 : Real) * Real.log x)) *
      (x ^ (1 / 2 : Real) * Real.log x) = nicolasMomentWave x - 1 := by field_simp
  by_contra hn
  have hh := mul_lt_mul_of_pos_right (lt_of_not_ge hn) hs
  rw [hc] at hh
  dsimp [nicolasMomentWave] at hh
  nlinarith

theorem momentOrder_decay (x : Real) (hx : 1 < x) :
    1 <= nicolasMomentOrder x /\
      (2 : Real) ^ (-((nicolasMomentOrder x : Nat) : Real)) <= x ^ (-(1 / 4 : Real)) := by
  have hlog : 0 < Real.log x := Real.log_pos hx
  have htwo : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hCeil : 0 < Nat.ceil (Real.log x / (8 * Real.log 2)) :=
    Nat.ceil_pos.mpr (by positivity)
  refine And.intro (by dsimp [nicolasMomentOrder]; omega) ?_
  rw [Real.rpow_def_of_pos (by norm_num : (0 : Real) < 2),
    Real.rpow_def_of_pos (zero_lt_one.trans hx)]
  apply Real.exp_le_exp.mpr
  have h := Nat.le_ceil (Real.log x / (8 * Real.log 2))
  have hh := mul_le_mul_of_nonneg_right h (by positivity : 0 <= 8 * Real.log 2)
  have hcancel : Real.log x / (8 * Real.log 2) * (8 * Real.log 2) = Real.log x := by field_simp
  rw [hcancel] at hh
  dsimp [nicolasMomentOrder]
  rw [Nat.cast_mul, Nat.cast_ofNat]
  nlinarith

theorem positive_part_le_abs_pow (z : Real) (q : Nat) (hq : 1 <= q) :
    max (z - 1) 0 <= abs z ^ q := by
  by_cases hz : z <= 1
  . rw [max_eq_right (by linarith)]
    positivity
  . have hz1 : 1 <= z := (lt_of_not_ge hz).le
    have hz0 : 0 <= z := by linarith
    rw [abs_of_nonneg hz0, max_eq_left (by linarith)]
    have allPowers (k : Nat) : 1 <= z ^ k := by
      induction k with
      | zero => simp
      | succ k ih =>
        rw [pow_succ]
        nlinarith
    have hp : 1 <= z ^ (q - 1) := allPowers (q - 1)
    have he : q - 1 + 1 = q := by omega
    have hm := mul_le_mul_of_nonneg_right hp hz0
    rw [one_mul, <- pow_succ, he] at hm
    linarith


theorem nicolasPositiveArea_le_moment
    (q : Nat) (hq : 1 <= q) (x : Real) (hx : 1 < x)
    (hPoint : forall y : Real, x <= y -> y <= 2 * x ->
      nicolasLogMertensOscillation y <=
        (nicolasMomentWave y - 1) / (y ^ (1 / 2 : Real) * Real.log y)) :
    nicolasPositiveArea x <= ENNReal.ofReal (1 / (x ^ (1 / 2 : Real) * Real.log x)) *
      lintegral (volume.restrict (Icc x (2 * x)))
        (fun y : Real => ENNReal.ofReal (abs (nicolasMomentWave y) ^ q)) := by
  have hx0 : 0 < x := zero_lt_one.trans hx
  have hs : 0 < x ^ (1 / 2 : Real) * Real.log x :=
    mul_pos (Real.rpow_pos_of_pos hx0 _) (Real.log_pos hx)
  have hEvent : Filter.Eventually (fun y : Real =>
      ENNReal.ofReal (nicolasLogMertensOscillation y) <=
        ENNReal.ofReal (1 / (x ^ (1 / 2 : Real) * Real.log x)) *
          ENNReal.ofReal (abs (nicolasMomentWave y) ^ q))
      (ae (volume.restrict (Icc x (2 * x)))) := by
    filter_upwards [ae_restrict_mem measurableSet_Icc] with y hy
    have hy1 : 1 < y := hx.trans_le hy.1
    have hy0 : 0 < y := zero_lt_one.trans hy1
    have hScale : x ^ (1 / 2 : Real) * Real.log x <=
        y ^ (1 / 2 : Real) * Real.log y :=
      mul_le_mul (Real.rpow_le_rpow hx0.le hy.1 (by norm_num))
        (Real.log_le_log hx0 hy.1) (Real.log_pos hx).le
        (Real.rpow_nonneg hy0.le _)
    have hyScale : 0 < y ^ (1 / 2 : Real) * Real.log y := hs.trans_le hScale
    have hPow : nicolasMomentWave y - 1 <=
        abs (nicolasMomentWave y) ^ q :=
      (le_max_left _ _).trans (positive_part_le_abs_pow _ _ hq)
    have hBound := (hPoint y hy.1 hy.2).trans
      ((div_le_div_of_nonneg_right hPow hyScale.le).trans
        (div_le_div_of_nonneg_left (by positivity) hs hScale))
    calc
      _ <= ENNReal.ofReal (abs (nicolasMomentWave y) ^ q /
          (x ^ (1 / 2 : Real) * Real.log x)) := ENNReal.ofReal_le_ofReal hBound
      _ = _ := by
        rw [show abs (nicolasMomentWave y) ^ q /
          (x ^ (1 / 2 : Real) * Real.log x) =
          (1 / (x ^ (1 / 2 : Real) * Real.log x)) *
            abs (nicolasMomentWave y) ^ q by ring,
          ENNReal.ofReal_mul (by positivity)]
  have h := lintegral_mono_ae hEvent
  rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top] at h
  exact h

theorem nicolasPositiveArea_le_growing_moment
    (x : Real) (hx : 1 < x)
    (hPoint : forall y : Real, x <= y -> y <= 2 * x ->
      nicolasLogMertensOscillation y <=
        (nicolasMomentWave y - 1) / (y ^ (1 / 2 : Real) * Real.log y)) :
    nicolasPositiveArea x <= ENNReal.ofReal (1 / (x ^ (1 / 2 : Real) * Real.log x)) *
      lintegral (volume.restrict (Icc x (2 * x)))
        (fun y : Real => ENNReal.ofReal (abs (nicolasMomentWave y) ^ nicolasMomentOrder x)) :=
  nicolasPositiveArea_le_moment (nicolasMomentOrder x) (momentOrder_decay x hx).1 x hx hPoint

theorem moment_decay_scaled (x C : Real) (hx : 1 < x) (hC : 0 <= C) :
    (1 / (x ^ (1 / 2 : Real) * Real.log x)) *
        (C * x * (2 : Real) ^ (-((nicolasMomentOrder x : Nat) : Real))) <=
      C * x ^ (1 / 4 : Real) / Real.log x := by
  have hx0 : 0 < x := zero_lt_one.trans hx
  have hl : 0 < Real.log x := Real.log_pos hx
  have hp : 0 < x ^ (1 / 2 : Real) := Real.rpow_pos_of_pos hx0 _
  have hDecay := (momentOrder_decay x hx).2
  have h := mul_le_mul_of_nonneg_left hDecay
    (show 0 <= (1 / (x ^ (1 / 2 : Real) * Real.log x)) * (C * x) by positivity)
  have hPowers : x ^ (1 / 4 : Real) * x ^ (1 / 2 : Real) =
      x * x ^ (-(1 / 4 : Real)) := by
    calc
      _ = x ^ (3 / 4 : Real) := by rw [<- Real.rpow_add hx0]; norm_num
      _ = x ^ (1 : Real) * x ^ (-(1 / 4 : Real)) := by
        rw [<- Real.rpow_add hx0]; norm_num
      _ = _ := by rw [Real.rpow_one]
  have he : (1 / (x ^ (1 / 2 : Real) * Real.log x)) *
      (C * x * x ^ (-(1 / 4 : Real))) =
      C * x ^ (1 / 4 : Real) / Real.log x := by
    field_simp
    nlinarith only [congrArg (fun t : Real => C * t) hPowers]
  calc
    _ <= (1 / (x ^ (1 / 2 : Real) * Real.log x)) *
        (C * x * x ^ (-(1 / 4 : Real))) := by simpa only [mul_assoc] using h
    _ = _ := he

/-- The growing-order moment estimate is an explicit unproved hypothesis. -/
theorem riemannHypothesis_of_growing_nicolas_moments
    (C : Real) (hC : 0 < C)
    (hMoment : Filter.Eventually (fun x : Real =>
      lintegral (volume.restrict (Icc x (2 * x)))
        (fun y : Real => ENNReal.ofReal (abs (nicolasMomentWave y) ^ nicolasMomentOrder x)) <=
      ENNReal.ofReal (C * x * (2 : Real) ^ (-((nicolasMomentOrder x : Nat) : Real)))) atTop) :
    RiemannHypothesis := by
  choose Y hY using eventually_atTop.mp eventually_nicolasLog_le_moment_wave
  have hArea : Filter.Eventually (fun x : Real =>
      nicolasPositiveArea x <= ENNReal.ofReal (C * x ^ (1 / 4 : Real))) atTop := by
    filter_upwards [hMoment, eventually_ge_atTop Y, eventually_ge_atTop (3 : Real)]
      with x hm hxY hxThree
    have hx : 1 < x := by linarith
    have hlog : 1 <= Real.log x :=
      ((Real.lt_log_iff_exp_lt (by linarith : 0 < x)).mpr
        (Real.exp_one_lt_three.trans_le hxThree)).le
    have hp := nicolasPositiveArea_le_growing_moment x hx
      (fun y hxy _ => hY y (hxY.trans hxy))
    calc
      _ <= ENNReal.ofReal (1 / (x ^ (1 / 2 : Real) * Real.log x)) *
          ENNReal.ofReal (C * x * (2 : Real) ^ (-((nicolasMomentOrder x : Nat) : Real))) :=
        hp.trans (mul_le_mul_of_nonneg_left hm (by positivity))
      _ = ENNReal.ofReal ((1 / (x ^ (1 / 2 : Real) * Real.log x)) *
          (C * x * (2 : Real) ^ (-((nicolasMomentOrder x : Nat) : Real)))) := by
        exact (ENNReal.ofReal_mul
          (by positivity : 0 <= 1 / (x ^ (1 / 2 : Real) * Real.log x))).symm
      _ <= ENNReal.ofReal (C * x ^ (1 / 4 : Real) / Real.log x) :=
        ENNReal.ofReal_le_ofReal (moment_decay_scaled x C hx hC.le)
      _ <= ENNReal.ofReal (C * x ^ (1 / 4 : Real)) := by
        apply ENNReal.ofReal_le_ofReal
        have hh := div_le_div_of_nonneg_left (show 0 <= C * x ^ (1 / 4 : Real) by positivity)
          (by norm_num : (0 : Real) < 1) hlog
        simpa only [div_one] using hh
  choose X hX using eventually_atTop.mp hArea
  apply riemannHypothesis_iff_nicolasPositiveArea_bound.mpr
  refine Exists.intro C (Exists.intro 0 (Exists.intro X (And.intro hC ?_)))
  intro x hx
  simpa only [Real.rpow_zero, mul_one] using hX x hx


end PrimeFactorOscillations



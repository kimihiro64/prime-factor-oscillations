/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.NicolasQuantitativeClock
import PrimeFactorOscillations.Helpers.ThetaPolylogDecay

/-!
# Unconditional logarithmic decay of the complete Nicolas expression

The theta-error integral and nonlinear endpoint correction are both retained.
Every fixed logarithmic power times the signed Nicolas logarithm tends to zero.
-/

set_option autoImplicit false
set_option Elab.async false

noncomputable section
namespace PrimeFactorOscillations
open Filter MeasureTheory Set Robin1984

theorem exists_nicolasK_polylogarithmic_bound (m : Nat) :
    exists C : Real, 0 <= C /\
      Filter.Eventually (fun x : Real =>
        abs (nicolasK x) <= C *
          (1 / Real.log x + 1 / Real.log x ^ (2 : Nat)) /
          Real.log x ^ (m + 1)) atTop := by
  choose C hC hTheta using
    (Asymptotics.isBigO_iff'.mp (thetaError_isBigO_div_log_pow (m + 2)))
  choose X hX using eventually_atTop.mp hTheta
  refine Exists.intro C (And.intro hC.le ?_)
  filter_upwards [eventually_ge_atTop (max X 3)] with x hx
  have hxThree : 3 <= x := (le_max_right X 3).trans hx
  have hxX : X <= x := (le_max_left X 3).trans hx
  have hxOne : 1 < x := by linarith
  have hx0 : 0 < x := by linarith
  have hl : 0 < Real.log x := Real.log_pos hxOne
  let A : Real := C * (1 / Real.log x + 1 / Real.log x ^ (2 : Nat)) /
    Real.log x ^ m
  let f : Real -> Real := fun t => (Chebyshev.theta t - t) *
    ((1 / Real.log t + 1 / Real.log t ^ (2 : Nat)) / t ^ (2 : Nat))
  have hF : IntegrableOn f (Ioi x) :=
    nicolasThetaTail_integrableOn_Ioi_two.mono_set (Ioi_subset_Ioi (by linarith))
  have hG : IntegrableOn
      (fun t : Real => A * (Inv.inv t / Real.log t ^ (2 : Nat))) (Ioi x) :=
    (integrableOn_inv_div_log_sq_Ioi hxOne).const_mul A
  have hPoint : Filter.Eventually (fun t : Real =>
      norm (f t) <= A * (Inv.inv t / Real.log t ^ (2 : Nat)))
      (ae (volume.restrict (Ioi x))) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    have hxt : x < t := ht
    have ht0 : 0 < t := hx0.trans hxt
    have htOne : 1 < t := hxOne.trans hxt
    have hlt : 0 < Real.log t := Real.log_pos htOne
    have hError : abs (Chebyshev.theta t - t) <=
        C * t / Real.log t ^ (m + 2) := by
      have h := hX t (hxX.trans hxt.le)
      simpa only [Real.norm_eq_abs, norm_div, norm_pow, abs_of_pos ht0,
        abs_of_pos hlt, mul_div] using h
    have hLogs : Real.log x <= Real.log t := Real.log_le_log hx0 hxt.le
    have hInv : 1 / Real.log t <= 1 / Real.log x :=
      one_div_le_one_div_of_le hl hLogs
    have hInvSq : 1 / Real.log t ^ (2 : Nat) <= 1 / Real.log x ^ (2 : Nat) :=
      one_div_le_one_div_of_le (sq_pos_of_pos hl) (by nlinarith)
    have hInvM : 1 / Real.log t ^ m <= 1 / Real.log x ^ m :=
      one_div_le_one_div_of_le (pow_pos hl m) (by gcongr)
    have hCoeff : C * (1 / Real.log t + 1 / Real.log t ^ (2 : Nat)) /
        Real.log t ^ m <= A := by
      dsimp only [A]
      have h := mul_le_mul
        (mul_le_mul_of_nonneg_left (add_le_add hInv hInvSq) hC.le)
        hInvM (by positivity) (by positivity)
      simpa only [div_eq_mul_inv, one_mul] using h
    have hk : 0 <=
        (1 / Real.log t + 1 / Real.log t ^ (2 : Nat)) / t ^ (2 : Nat) := by
      positivity
    dsimp only [f]
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg hk]
    calc
      _ <= (C * t / Real.log t ^ (m + 2)) *
          ((1 / Real.log t + 1 / Real.log t ^ (2 : Nat)) / t ^ (2 : Nat)) :=
        mul_le_mul_of_nonneg_right hError hk
      _ = (C * (1 / Real.log t + 1 / Real.log t ^ (2 : Nat)) / Real.log t ^ m) *
          (Inv.inv t / Real.log t ^ (2 : Nat)) := by
        rw [pow_add]
        field_simp <;> ring
      _ <= _ := mul_le_mul_of_nonneg_right hCoeff (by positivity)
  have hInt : abs (nicolasK x) <= A / Real.log x := by
    change abs (integral (volume.restrict (Ioi x)) f) <= A / Real.log x
    calc
      _ = norm (integral (volume.restrict (Ioi x)) f) := (Real.norm_eq_abs _).symm
      _ <= integral (volume.restrict (Ioi x)) (fun t => norm (f t)) :=
        norm_integral_le_integral_norm _
      _ <= integral (volume.restrict (Ioi x))
          (fun t : Real => A * (Inv.inv t / Real.log t ^ (2 : Nat))) :=
        integral_mono_ae hF.norm hG hPoint
      _ = A / Real.log x := by
        rw [integral_const_mul, integral_inv_div_log_sq_Ioi hxOne]
        rfl
  convert hInt using 1
  dsimp only [A]
  rw [pow_succ]
  ring

theorem tendsto_nicolasK_mul_log_pow_zero_unconditionally (m : Nat) :
    Tendsto (fun x : Real => nicolasK x * Real.log x ^ (m + 1))
      atTop (nhds 0) := by
  choose C hC hBound using exists_nicolasK_polylogarithmic_bound m
  have hInv : Tendsto (fun x : Real => 1 / Real.log x) atTop (nhds 0) := by
    simpa only [one_div, Function.comp_def] using
      tendsto_inv_atTop_zero.comp Real.tendsto_log_atTop
  have hLimit : Tendsto
      (fun x : Real => C * (1 / Real.log x + 1 / Real.log x ^ (2 : Nat)))
      atTop (nhds 0) := by
    simpa only [one_div, inv_pow, zero_pow (by norm_num : Not ((2 : Nat) = 0)),
      add_zero, mul_zero] using (hInv.add (hInv.pow 2)).const_mul C
  apply squeeze_zero_norm' (a := fun x : Real =>
    C * (1 / Real.log x + 1 / Real.log x ^ (2 : Nat))) ?_ hLimit
  filter_upwards [hBound, eventually_gt_atTop (1 : Real)] with x hx hxOne
  have hl : 0 < Real.log x := Real.log_pos hxOne
  rw [Real.norm_eq_abs, abs_mul, abs_of_pos (pow_pos hl _)]
  calc
    _ <= (C * (1 / Real.log x + 1 / Real.log x ^ (2 : Nat)) /
          Real.log x ^ (m + 1)) * Real.log x ^ (m + 1) :=
      mul_le_mul_of_nonneg_right hx (pow_nonneg hl.le _)
    _ = _ := by field_simp

theorem tendsto_log_pow_div_self (m : Nat) :
    Tendsto (fun x : Real => Real.log x ^ (m + 1) / x) atTop (nhds 0) := by
  have hInv : Tendsto (fun x : Real => 1 / (x ^ (1 / 2 : Real)))
      atTop (nhds 0) := by
    simpa only [one_div, Function.comp_def] using
      (tendsto_inv_atTop_zero : Tendsto (fun x : Real => Inv.inv x)
        atTop (nhds 0)).comp
      (tendsto_rpow_atTop (by norm_num : (0 : Real) < 1 / 2))
  have h := (tendsto_log_pow_div_sqrt m).mul hInv
  simp only [mul_zero] at h
  apply h.congr'
  filter_upwards [eventually_gt_atTop (0 : Real)] with x hx
  rw [<- Real.sqrt_eq_rpow]
  have hs : Not (Real.sqrt x = 0) := (Real.sqrt_pos.mpr hx).ne'
  field_simp
  rw [Real.sq_sqrt hx.le]

theorem tendsto_nicolasLog_mul_log_pow_zero_unconditionally (m : Nat) :
    Tendsto (fun x : Real => nicolasLogMertensOscillation x *
      Real.log x ^ (m + 1)) atTop (nhds 0) := by
  choose C hC hTheta using
    (Asymptotics.isBigO_iff'.mp (thetaError_isBigO_div_log_pow (m + 2)))
  have hLoLimit : Tendsto (fun x : Real => 6 * C ^ (2 : Nat) /
      Real.log x ^ (m + 4)) atTop (nhds 0) :=
    ((tendsto_pow_atTop (by omega : Not (m + 4 = 0))).comp
      Real.tendsto_log_atTop).const_div_atTop _
  have hHiLimit : Tendsto (fun x : Real => 4 * Real.log x ^ (m + 1) / x)
      atTop (nhds 0) := by
    simpa only [mul_zero, mul_div_assoc] using (tendsto_log_pow_div_self m).const_mul 4
  have hDiff : Tendsto (fun x : Real =>
      (nicolasLogMertensOscillation x - nicolasK x) * Real.log x ^ (m + 1))
      atTop (nhds 0) := by
    have hLimit := hLoLimit.add hHiLimit
    simp only [add_zero] at hLimit
    apply squeeze_zero_norm' (a := fun x : Real =>
      6 * C ^ (2 : Nat) / Real.log x ^ (m + 4) +
        4 * Real.log x ^ (m + 1) / x) ?_ hLimit
    have hLarge := ((tendsto_pow_atTop (by omega : Not (m + 2 = 0))).comp
      Real.tendsto_log_atTop).eventually_ge_atTop (2 * C)
    filter_upwards [hTheta, hLarge, eventually_ge_atTop (6 : Real)] with
      x hThetaX hLargeX hx
    have hx0 : 0 < x := by linarith
    have hl : 0 < Real.log x := Real.log_pos (by linarith)
    have hError : abs (Chebyshev.theta x - x) <= C * x / Real.log x ^ (m + 2) := by
      simpa only [Real.norm_eq_abs, norm_div, norm_pow, abs_of_pos hx0,
        abs_of_pos hl, mul_div] using hThetaX
    have hLogHalf : 1 <= Real.log (x / 2) := by
      apply le_of_lt
      apply (Real.lt_log_iff_exp_lt (by positivity : 0 < x / 2)).mpr
      exact Real.exp_one_lt_three.trans_le (by linarith)
    let M : Real := C * x / Real.log x ^ (m + 2)
    have hM : 0 <= M := by dsimp only [M]; positivity
    have hSmall : M <= x / 2 := by
      change 2 * C <= Real.log x ^ (m + 2) at hLargeX
      calc
        _ <= ((Real.log x ^ (m + 2) / 2) * x) / Real.log x ^ (m + 2) :=
          div_le_div_of_nonneg_right
            (mul_le_mul_of_nonneg_right (by linarith : C <= Real.log x ^ (m + 2) / 2)
              hx0.le) (pow_nonneg hl.le _)
        _ = _ := by field_simp
    have hLower := nicolasLog_interval_lower_bound x x M (by linarith)
      hLogHalf le_rfl hM hSmall (by
        intro t hxt htx
        have heq : t = x := le_antisymm htx hxt
        subst t
        exact hError)
    simp only [sub_self, mul_zero, zero_add] at hLower
    have hLowerScaled := mul_le_mul_of_nonneg_right hLower
      (pow_nonneg hl.le (m + 1))
    rw [sub_mul] at hLowerScaled
    have hLoss : (6 * M ^ (2 : Nat) / (x ^ (2 : Nat) * Real.log x)) *
        Real.log x ^ (m + 1) = 6 * C ^ (2 : Nat) / Real.log x ^ (m + 4) := by
      dsimp only [M]
      simp only [pow_add, pow_one]
      field_simp <;> ring
    rw [hLoss] at hLowerScaled
    have hUpperScaled := mul_le_mul_of_nonneg_right
      (nicolasLogMertensOscillation_le_K_add_four_div (by linarith : (3 : Real) <= x))
      (pow_nonneg hl.le (m + 1))
    rw [add_mul, show 4 / x * Real.log x ^ (m + 1) =
      4 * Real.log x ^ (m + 1) / x by ring] at hUpperScaled
    have hloNon : 0 <= 6 * C ^ (2 : Nat) / Real.log x ^ (m + 4) := by positivity
    have hhiNon : 0 <= 4 * Real.log x ^ (m + 1) / x := by positivity
    rw [Real.norm_eq_abs]
    apply abs_le.mpr
    constructor <;> nlinarith only [hLowerScaled, hUpperScaled, hloNon, hhiNon]
  have h := hDiff.add (tendsto_nicolasK_mul_log_pow_zero_unconditionally m)
  convert h using 1
  . funext x
    ring
  . norm_num

end PrimeFactorOscillations

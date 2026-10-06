/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.NicolasIntervalPersistence
import PrimeFactorOscillations.Helpers.NicolasSpatialClock
import PrimeFactorOscillations.Helpers.ThetaErrorIntegrability

/-!
# Unconditional precision of the Nicolas spatial clock

The cached quantitative prime number theorem gives F(x) log x tending to
zero. This controls the exponent before converting the exact clock identity
to the physical asymptotic C(x)/x tending to one.
-/

set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace PrimeFactorOscillations
open Filter MeasureTheory Set Robin1984

theorem exists_nicolasK_logarithmic_bound :
    exists C : Real, 0 <= C /\ forall x : Real, 3 <= x ->
      abs (nicolasK x) <= C * (1 / Real.log x + 1 / (Real.log x) ^ (2 : Nat)) /
        Real.log x := by
  choose C hC hError using exists_thetaError_bound_div_log_sq
  refine Exists.intro C (And.intro hC ?_)
  intro x hx
  have hx1 : 1 < x := by linarith
  have hx0 : 0 < x := by linarith
  have hl : 0 < Real.log x := Real.log_pos hx1
  let A : Real := C * (1 / Real.log x + 1 / (Real.log x) ^ (2 : Nat))
  let f : Real -> Real := fun t => (Chebyshev.theta t - t) *
    ((1 / Real.log t + 1 / (Real.log t) ^ (2 : Nat)) / t ^ (2 : Nat))
  have hF : IntegrableOn f (Ioi x) :=
    nicolasThetaTail_integrableOn_Ioi_two.mono_set (Ioi_subset_Ioi (by linarith))
  have hG : IntegrableOn (fun t : Real => A * (Inv.inv t / (Real.log t) ^ (2 : Nat)))
      (Ioi x) := (integrableOn_inv_div_log_sq_Ioi hx1).const_mul A
  have hPoint : Filter.Eventually (fun t : Real =>
      norm (f t) <= A * (Inv.inv t / (Real.log t) ^ (2 : Nat)))
      (ae (volume.restrict (Ioi x))) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    have hxt : x < t := ht
    have ht0 : 0 < t := hx0.trans hxt
    have hlt : 0 < Real.log t := Real.log_pos (hx1.trans hxt)
    have hLogs : Real.log x <= Real.log t := Real.log_le_log hx0 hxt.le
    have hInv : 1 / Real.log t <= 1 / Real.log x :=
      one_div_le_one_div_of_le hl hLogs
    have hInvSq : 1 / (Real.log t) ^ (2 : Nat) <= 1 / (Real.log x) ^ (2 : Nat) :=
      one_div_le_one_div_of_le (sq_pos_of_pos hl) (by nlinarith)
    have hk : 0 <= (1 / Real.log t + 1 / (Real.log t) ^ (2 : Nat)) / t ^ (2 : Nat) := by positivity
    dsimp only [f]
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg hk]
    calc
      _ <= (C * t / (Real.log t) ^ (2 : Nat)) *
          ((1 / Real.log t + 1 / (Real.log t) ^ (2 : Nat)) / t ^ (2 : Nat)) :=
        mul_le_mul_of_nonneg_right (hError t (by linarith)) hk
      _ = C * (1 / Real.log t + 1 / (Real.log t) ^ (2 : Nat)) *
          (Inv.inv t / (Real.log t) ^ (2 : Nat)) := by field_simp
      _ <= A * (Inv.inv t / (Real.log t) ^ (2 : Nat)) :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left (add_le_add hInv hInvSq) hC) (by positivity)
  change abs (integral (volume.restrict (Ioi x)) f) <= A / Real.log x
  calc
    _ = norm (integral (volume.restrict (Ioi x)) f) := (Real.norm_eq_abs _).symm
    _ <= integral (volume.restrict (Ioi x)) (fun t => norm (f t)) :=
      norm_integral_le_integral_norm _
    _ <= integral (volume.restrict (Ioi x))
        (fun t : Real => A * (Inv.inv t / (Real.log t) ^ (2 : Nat))) :=
      integral_mono_ae hF.norm hG hPoint
    _ = A / Real.log x := by
      rw [integral_const_mul, integral_inv_div_log_sq_Ioi hx1]
      rfl

theorem tendsto_nicolasK_mul_log_zero_unconditionally :
    Tendsto (fun x : Real => nicolasK x * Real.log x) atTop (nhds 0) := by
  choose C hC hBound using exists_nicolasK_logarithmic_bound
  have hInv : Tendsto (fun x : Real => 1 / Real.log x) atTop (nhds 0) := by
    simpa only [one_div, Function.comp_def] using tendsto_inv_atTop_zero.comp Real.tendsto_log_atTop
  have hLimit : Tendsto (fun x : Real =>
      C * (1 / Real.log x + 1 / (Real.log x) ^ (2 : Nat))) atTop (nhds 0) := by
    simpa only [one_div, inv_pow, zero_pow (by norm_num : Not ((2 : Nat) = 0)),
      add_zero, mul_zero] using (hInv.add (hInv.pow 2)).const_mul C
  apply squeeze_zero_norm' (a := fun x : Real =>
    C * (1 / Real.log x + 1 / (Real.log x) ^ (2 : Nat))) ?_ hLimit
  filter_upwards [eventually_ge_atTop (3 : Real)] with x hx
  have hl : 0 < Real.log x := Real.log_pos (by linarith)
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg hl.le]
  calc
    _ <= (C * (1 / Real.log x + 1 / (Real.log x) ^ (2 : Nat)) / Real.log x) * Real.log x :=
      mul_le_mul_of_nonneg_right (hBound x hx) hl.le
    _ = _ := by field_simp


theorem tendsto_nicolasLog_mul_log_zero_unconditionally :
    Tendsto (fun x : Real => nicolasLogMertensOscillation x * Real.log x)
      atTop (nhds 0) := by
  choose C hC hBound using exists_thetaError_bound_div_log_sq
  have hLoLimit : Tendsto (fun x : Real => 6 * C ^ (2 : Nat) /
      (Real.log x) ^ (4 : Nat)) atTop (nhds 0) :=
    ((tendsto_pow_atTop (by norm_num : Not ((4 : Nat) = 0))).comp
      Real.tendsto_log_atTop).const_div_atTop (6 * C ^ (2 : Nat))
  have hHiLimit : Tendsto (fun x : Real => 4 * Real.log x / x) atTop (nhds 0) := by
    have ht := ((isLittleO_log_rpow_atTop
      (by norm_num : (0 : Real) < 1)).tendsto_div_nhds_zero).const_mul 4
    simpa only [Real.rpow_one, mul_zero, mul_div_assoc] using ht
  have hDiffLimit : Tendsto (fun x : Real =>
      (nicolasLogMertensOscillation x - nicolasK x) * Real.log x)
      atTop (nhds 0) := by
    have hLimit := hLoLimit.add hHiLimit
    simp only [add_zero] at hLimit
    apply squeeze_zero_norm' (a := fun x : Real =>
      6 * C ^ (2 : Nat) / (Real.log x) ^ (4 : Nat) + 4 * Real.log x / x) ?_ hLimit
    have hLarge := ((tendsto_pow_atTop (by norm_num : Not ((2 : Nat) = 0))).comp
      Real.tendsto_log_atTop).eventually_ge_atTop (2 * C)
    filter_upwards [hLarge, eventually_ge_atTop (6 : Real)] with x hLargeX hx
    change 2 * C <= (Real.log x) ^ (2 : Nat) at hLargeX
    have hx0 : 0 < x := by linarith
    have hl : 0 < Real.log x := Real.log_pos (by linarith)
    have hLogHalf : 1 <= Real.log (x / 2) := by
      apply le_of_lt
      apply (Real.lt_log_iff_exp_lt (by positivity : 0 < x / 2)).mpr
      exact Real.exp_one_lt_three.trans_le (by linarith)
    let M : Real := C * x / (Real.log x) ^ (2 : Nat)
    have hM : 0 <= M := by dsimp [M]; positivity
    have hSmall : M <= x / 2 := by
      calc
        _ <= (((Real.log x) ^ (2 : Nat) / 2) * x) /
            (Real.log x) ^ (2 : Nat) := div_le_div_of_nonneg_right
          (mul_le_mul_of_nonneg_right (by linarith : C <= (Real.log x) ^ (2 : Nat) / 2)
            hx0.le) (sq_nonneg _)
        _ = _ := by field_simp
    have hLower := nicolasLog_interval_lower_bound x x M (by linarith)
      hLogHalf le_rfl hM hSmall (by
        intro t hxt htx
        have heq : t = x := le_antisymm htx hxt
        subst t
        exact hBound x (by linarith))
    simp only [sub_self, mul_zero, zero_add] at hLower
    have hLowerScaled := mul_le_mul_of_nonneg_right hLower hl.le
    rw [sub_mul] at hLowerScaled
    have hLoss : (6 * M ^ (2 : Nat) / (x ^ (2 : Nat) * Real.log x)) * Real.log x =
        6 * C ^ (2 : Nat) / (Real.log x) ^ (4 : Nat) := by
      dsimp [M]
      field_simp
    rw [hLoss] at hLowerScaled
    have hUpperScaled := mul_le_mul_of_nonneg_right
      (nicolasLogMertensOscillation_le_K_add_four_div (by linarith : (3 : Real) <= x)) hl.le
    rw [add_mul, show 4 / x * Real.log x = 4 * Real.log x / x by ring] at hUpperScaled
    have hloNon : 0 <= 6 * C ^ (2 : Nat) / (Real.log x) ^ (4 : Nat) := by positivity
    have hhiNon : 0 <= 4 * Real.log x / x := by positivity
    rw [Real.norm_eq_abs]
    apply abs_le.mpr
    constructor <;> nlinarith only [hLowerScaled, hUpperScaled, hloNon, hhiNon]
  have hTotal := hDiffLimit.add tendsto_nicolasK_mul_log_zero_unconditionally
  convert hTotal using 1
  . funext x
    ring
  . norm_num



private theorem clock_abs_exp_sub_one_le (u : Real) (hu : abs u <= 1) :
    abs (Real.exp u - 1) <= Real.exp 1 * abs u := by
  have hExp : 1 <= Real.exp (1 : Real) := by linarith [Real.add_one_le_exp (1 : Real)]
  have hScale : abs u <= Real.exp 1 * abs u := by
    simpa only [one_mul] using mul_le_mul_of_nonneg_right hExp (abs_nonneg u)
  have hNeg := mul_le_mul_of_nonneg_right (Real.add_one_le_exp (-abs u))
    (Real.exp_nonneg (abs u))
  rw [<- Real.exp_add, neg_add_cancel, Real.exp_zero] at hNeg
  have hAtU := Real.exp_le_exp.mpr (le_abs_self u)
  have hAtOne := mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hu) (abs_nonneg u)
  have hLin := Real.add_one_le_exp u
  have hAbs := neg_le_abs u
  apply abs_le.mpr
  constructor <;> nlinarith

theorem tendsto_nicolasPrimeProductClock_div_self :
    Tendsto (fun x : Real => nicolasPrimeProductClock x / x) atTop (nhds 1) := by
  have hFLog := tendsto_nicolasLog_mul_log_zero_unconditionally
  have hInv : Tendsto (fun x : Real => 1 / Real.log x) atTop (nhds 0) := by
    simpa only [one_div, Function.comp_def] using
      tendsto_inv_atTop_zero.comp Real.tendsto_log_atTop
  have hFZero : Tendsto nicolasLogMertensOscillation atTop (nhds 0) := by
    have ht : Tendsto (fun x : Real =>
        (nicolasLogMertensOscillation x * Real.log x) * (1 / Real.log x))
        atTop (nhds 0) := by simpa only [mul_zero] using hFLog.mul hInv
    apply ht.congr'
    filter_upwards [eventually_gt_atTop (1 : Real)] with x hx
    have hl : Not (Real.log x = 0) := (Real.log_pos hx).ne'
    field_simp
  have hAbs : Tendsto (fun x : Real => abs (nicolasLogMertensOscillation x))
      atTop (nhds 0) := by
    simpa only [Real.norm_eq_abs, norm_zero] using hFZero.norm
  have hRatio : Tendsto (fun x : Real => Chebyshev.theta x / x) atTop (nhds (1 : Real)) :=
    (Asymptotics.isEquivalent_iff_tendsto_one
      (eventually_ne_atTop (0 : Real))).mp primeProfile_theta_isEquivalent_id
  have hTheta : Tendsto Chebyshev.theta atTop atTop :=
    primeProfile_theta_isEquivalent_id.symm.tendsto_atTop tendsto_id
  let E : Real -> Real := fun x => Real.log (Chebyshev.theta x) *
    (Real.exp (-nicolasLogMertensOscillation x) - 1)
  have hE : Tendsto E atTop (nhds 0) := by
    have hMajor : Tendsto (fun x : Real =>
        (2 * Real.exp 1) * norm (nicolasLogMertensOscillation x * Real.log x))
        atTop (nhds 0) := by
      simpa only [norm_zero, mul_zero] using hFLog.norm.const_mul (2 * Real.exp 1)
    apply squeeze_zero_norm' (a := fun x : Real =>
      (2 * Real.exp 1) * norm (nicolasLogMertensOscillation x * Real.log x)) ?_ hMajor
    filter_upwards [hAbs.eventually_lt_const (by norm_num : (0 : Real) < 1),
      hRatio.eventually_lt_const (by norm_num : (1 : Real) < 2),
      hTheta.eventually_gt_atTop 1, eventually_ge_atTop (2 : Real)] with
      x hf hr ht hx
    have hx0 : 0 < x := by linarith
    have hl : 0 < Real.log x := Real.log_pos (by linarith)
    have ht0 : 0 < Chebyshev.theta x := by linarith
    have hlt : 0 < Real.log (Chebyshev.theta x) := Real.log_pos ht
    have hMul := mul_lt_mul_of_pos_right hr hx0
    have hCancel : Chebyshev.theta x / x * x = Chebyshev.theta x := by field_simp
    rw [hCancel] at hMul
    have hLog := Real.log_le_log ht0 hMul.le
    rw [Real.log_mul (by norm_num : Not ((2 : Real) = 0)) hx0.ne'] at hLog
    have hLogTwo := Real.log_le_log (by norm_num : (0 : Real) < 2) hx
    have hLogUpper : Real.log (Chebyshev.theta x) <= 2 * Real.log x := by linarith
    have hExp := clock_abs_exp_sub_one_le (-nicolasLogMertensOscillation x)
      (by simpa only [abs_neg] using hf.le)
    rw [abs_neg] at hExp
    dsimp only [E]
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg hlt.le, Real.norm_eq_abs]
    calc
      _ <= Real.log (Chebyshev.theta x) *
          (Real.exp 1 * abs (nicolasLogMertensOscillation x)) :=
        mul_le_mul_of_nonneg_left hExp hlt.le
      _ <= (2 * Real.log x) * (Real.exp 1 * abs (nicolasLogMertensOscillation x)) :=
        mul_le_mul_of_nonneg_right hLogUpper (by positivity)
      _ = _ := by rw [abs_mul, abs_of_nonneg hl.le]; ring
  have hLimit : Tendsto (fun x : Real => (Chebyshev.theta x / x) * Real.exp (E x))
      atTop (nhds 1) := by
    have hExp : Tendsto (fun x : Real => Real.exp (E x)) atTop (nhds 1) := by
      simpa only [Real.exp_zero, Function.comp_def] using
        (Real.continuous_exp.tendsto 0).comp hE
    simpa only [mul_one] using hRatio.mul hExp
  apply hLimit.congr'
  filter_upwards [hTheta.eventually_gt_atTop 1] with x hx
  rw [nicolasPrimeProductClock_eq_theta_mul_exp hx]
  dsimp only [E]
  ring


end PrimeFactorOscillations

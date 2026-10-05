/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.NicolasRHCriterion

/-!
# Exact prime-product clock and the RH sign criterion

The clock uses the actual finite Mertens product. Its spatial comparison
with theta is exactly the Nicolas sign, with all positivity premises explicit.
These are formulations of the proved criterion, not prime-gap supply results.
-/

set_option autoImplicit false
set_option Elab.async false

namespace PrimeFactorOscillations

open Filter Robin1984

noncomputable section

theorem nicolasFunction_pos_of_theta_gt_one {x : Real}
    (hx : 1 < Chebyshev.theta x) : 0 < nicolasFunction x :=
  mul_pos (mul_pos (Real.exp_pos _) (Real.log_pos hx))
    (Robin1984.nicolasMertensProduct_pos x)

def nicolasPrimeProductClock (x : Real) : Real :=
  Real.exp (Real.exp (-Real.eulerMascheroniConstant) / nicolasMertensProduct x)

theorem loglog_nicolasPrimeProductClock (x : Real) :
    Real.log (Real.log (nicolasPrimeProductClock x)) =
      -Real.eulerMascheroniConstant - Real.log (nicolasMertensProduct x) := by
  unfold nicolasPrimeProductClock
  rw [Real.log_exp, Real.log_div (Real.exp_pos _).ne'
    (Robin1984.nicolasMertensProduct_pos x).ne', Real.log_exp]

theorem nicolasPrimeProductClock_eq_theta_rpow {x : Real}
    (hx : 1 < Chebyshev.theta x) :
    nicolasPrimeProductClock x =
      Chebyshev.theta x ^ (1 / nicolasFunction x) := by
  have hThetaPos : 0 < Chebyshev.theta x := lt_trans Real.zero_lt_one hx
  have hLogPos := Real.log_pos hx
  have hM := Robin1984.nicolasMertensProduct_pos x
  unfold nicolasPrimeProductClock
  rw [Real.rpow_def_of_pos hThetaPos]
  congr 1
  unfold nicolasFunction
  rw [Real.exp_neg]
  field_simp [hM.ne', hLogPos.ne', (Real.exp_pos Real.eulerMascheroniConstant).ne']
  <;> ring

theorem theta_lt_nicolasPrimeProductClock_iff {x : Real}
    (hx : 1 < Chebyshev.theta x) :
    Chebyshev.theta x < nicolasPrimeProductClock x <->
      nicolasLogMertensOscillation x < 0 := by
  have hThetaPos : 0 < Chebyshev.theta x := lt_trans Real.zero_lt_one hx
  have hM := Robin1984.nicolasMertensProduct_pos x
  have hf := nicolasFunction_pos_of_theta_gt_one hx
  have hScale : 0 < Real.exp Real.eulerMascheroniConstant * nicolasMertensProduct x :=
    mul_pos (Real.exp_pos _) hM
  have hThreshold : Real.exp (-Real.eulerMascheroniConstant) / nicolasMertensProduct x =
      1 / (Real.exp Real.eulerMascheroniConstant * nicolasMertensProduct x) := by
    rw [Real.exp_neg]
    field_simp [hM.ne', (Real.exp_pos Real.eulerMascheroniConstant).ne']
  have hProduct : Real.log (Chebyshev.theta x) *
      (Real.exp Real.eulerMascheroniConstant * nicolasMertensProduct x) =
      nicolasFunction x := by
    unfold nicolasFunction
    ring
  change Chebyshev.theta x < nicolasPrimeProductClock x <->
    Real.log (nicolasFunction x) < 0
  calc
    Chebyshev.theta x < nicolasPrimeProductClock x <->
        Real.exp (Real.log (Chebyshev.theta x)) <
          Real.exp (Real.exp (-Real.eulerMascheroniConstant) / nicolasMertensProduct x) := by
      rw [Real.exp_log hThetaPos]
      rfl
    _ <-> Real.log (Chebyshev.theta x) <
        Real.exp (-Real.eulerMascheroniConstant) / nicolasMertensProduct x :=
      Real.exp_lt_exp
    _ <-> nicolasFunction x < 1 := by
      rw [hThreshold]
      constructor
      . intro h
        have hMul := mul_lt_mul_of_pos_right h hScale
        have hCancel : (1 / (Real.exp Real.eulerMascheroniConstant *
            nicolasMertensProduct x)) * (Real.exp Real.eulerMascheroniConstant *
            nicolasMertensProduct x) = 1 := by field_simp [hScale.ne']
        rw [hProduct, hCancel] at hMul
        exact hMul
      . intro h
        by_contra hNot
        have hMul := mul_le_mul_of_nonneg_right (le_of_not_gt hNot) hScale.le
        have hCancel : (1 / (Real.exp Real.eulerMascheroniConstant *
            nicolasMertensProduct x)) * (Real.exp Real.eulerMascheroniConstant *
            nicolasMertensProduct x) = 1 := by field_simp [hScale.ne']
        rw [hProduct, hCancel] at hMul
        exact (not_lt_of_ge hMul) h
    _ <-> Real.exp (Real.log (nicolasFunction x)) < Real.exp 0 := by
      rw [Real.exp_log hf, Real.exp_zero]
    _ <-> Real.log (nicolasFunction x) < 0 := Real.exp_lt_exp

theorem riemannHypothesis_iff_eventually_nicolasLog_nat_neg :
    RiemannHypothesis <-> Filter.Eventually (fun N : Nat =>
      nicolasLogMertensOscillation (N : Real) < 0) atTop := by
  constructor
  . intro hRH
    simpa only [neg_zero, zero_div] using eventually_nicolasLog_nat_lt_neg_div_of_RH hRH 0
  . intro hEvent
    by_contra hNotRH
    choose N0 hN0 using eventually_atTop.mp hEvent
    choose N hN hPositive using nicolasLog_scaled_unbounded_of_not_RH hNotRH 0 N0
    have hNonpos := mul_nonpos_of_nonneg_of_nonpos
      (Nat.cast_nonneg N : (0 : Real) <= (N : Real)) (hN0 N hN).le
    exact (not_lt_of_ge hNonpos) hPositive

theorem riemannHypothesis_iff_eventually_nicolasLog_neg :
    RiemannHypothesis <-> Filter.Eventually (fun x : Real =>
      nicolasLogMertensOscillation x < 0) atTop := by
  constructor
  . intro hRH
    simpa only [neg_zero, zero_div] using eventually_nicolasLog_lt_neg_div_of_RH hRH 0
  . intro hEvent
    apply riemannHypothesis_iff_eventually_nicolasLog_nat_neg.mpr
    exact (tendsto_natCast_atTop_atTop :
      Tendsto (fun N : Nat => (N : Real)) atTop atTop).eventually hEvent

theorem riemannHypothesis_iff_eventually_theta_lt_primeProductClock :
    RiemannHypothesis <-> Filter.Eventually (fun x : Real =>
      Chebyshev.theta x < nicolasPrimeProductClock x) atTop := by
  have hTheta : Filter.Eventually (fun x : Real => 1 < Chebyshev.theta x) atTop :=
    (primeProfile_theta_isEquivalent_id.symm.tendsto_atTop tendsto_id).eventually_gt_atTop 1
  constructor
  . intro hRH
    have hLog := riemannHypothesis_iff_eventually_nicolasLog_neg.mp hRH
    filter_upwards [hLog, hTheta] with x hNegative hx
    exact (theta_lt_nicolasPrimeProductClock_iff hx).mpr hNegative
  . intro hEvent
    apply riemannHypothesis_iff_eventually_nicolasLog_neg.mpr
    filter_upwards [hEvent, hTheta] with x hClock hx
    exact (theta_lt_nicolasPrimeProductClock_iff hx).mp hClock

end

end PrimeFactorOscillations

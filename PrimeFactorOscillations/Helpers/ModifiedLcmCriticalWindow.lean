/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.ModifiedLcmNegativeSupply
import PrimeFactorOscillations.Helpers.ModifiedLcmRHWindow

/-!
# The unconditional modified-LCM critical window

The same explicit integer family works in both logical cases. Its growth
turns the unbounded cutoff supply into arbitrarily large actual integer
counterexamples for every fixed parameter between one and three halves.
-/

set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace PrimeFactorOscillations

open Filter Robin1984

theorem exists_modifiedLcm_window_of_not_RH
    (hNotRH : Not RiemannHypothesis) (X : Nat) :
    exists N : Nat, X < N /\ 8 <= N /\
      forall k : Real, forall hk : 1 < k,
        k <= lcmMovingExponent (2 / 5) N ->
          1 / (100 * Real.sqrt (N : Real) * Real.log (N : Real)) <
            Real.log (lcmRobinRatio k (zero_lt_one.trans hk) (modifiedLcm N)) := by
  have hLimit : (1 / 100 : Real) < lcmRHWindowLimit := by
    linarith only [lcmRHWindowLimit_gt]
  have hBudget := tendsto_lcmRHWindowBudget.eventually_const_lt hLimit
  have hTwo := (tendsto_lcmMovingExponent (2 / 5)).eventually_lt_const
    (by norm_num : (3 / 2 : Real) < 2)
  choose Y hY using eventually_atTop.mp
    (hBudget.and (hTwo.and (eventually_ge_atTop (8 : Nat))))
  choose N hN hNegative using modifiedLcm_negative_signed_supply_of_not_RH hNotRH (max Y (X + 1))
  have hNY : Y <= N := (le_max_left Y (X + 1)).trans hN
  have hNX : X < N := lt_of_lt_of_le (Nat.lt_succ_self X)
    ((le_max_right Y (X + 1)).trans hN)
  have hBounds := hY N hNY
  refine Exists.intro N (And.intro hNX (And.intro hBounds.2.2 ?_))
  intro k hk hLe
  have hScaled := hBounds.1.trans_le
    (lcmRHWindowBudget_le_scaled_logRatio N hBounds.2.2 (Or.inr hNegative.le)
      k hk hLe hBounds.2.1.le)
  have hNat : (1 : Real) < N := by
    exact_mod_cast (show 1 < N by omega)
  have hRoot := Real.sqrt_pos.2 (zero_lt_one.trans hNat)
  have hLog := Real.log_pos hNat
  have hScale := mul_pos hRoot hLog
  have hCancel :
      (1 / (100 * Real.sqrt (N : Real) * Real.log (N : Real))) *
        (Real.sqrt (N : Real) * Real.log (N : Real)) = (1 / 100 : Real) := by
    field_simp [hRoot.ne', hLog.ne']
  by_contra hNot
  have hUpper := mul_le_mul_of_nonneg_right (le_of_not_gt hNot) hScale.le
  rw [hCancel] at hUpper
  rw [mul_assoc] at hScaled
  exact (not_lt_of_ge hUpper) hScaled

theorem exists_modifiedLcm_window (X : Nat) :
    exists N : Nat, X < N /\ 8 <= N /\
      forall k : Real, forall hk : 1 < k,
        k <= lcmMovingExponent (2 / 5) N ->
          1 / (100 * Real.sqrt (N : Real) * Real.log (N : Real)) <
            Real.log (lcmRobinRatio k (zero_lt_one.trans hk) (modifiedLcm N)) := by
  classical
  by_cases hRH : RiemannHypothesis
  . choose Y hY using eventually_atTop.mp (eventually_modifiedLcm_window_of_RH hRH)
    let N := max Y (max (X + 1) 8)
    have hNY : Y <= N := le_max_left _ _
    have hNX : X < N := lt_of_lt_of_le (Nat.lt_succ_self X)
      ((le_max_left (X + 1) 8).trans (le_max_right Y _))
    have hEight : 8 <= N := (le_max_right (X + 1) 8).trans (le_max_right Y _)
    exact Exists.intro N (And.intro hNX (And.intro hEight (hY N hNY)))
  . exact exists_modifiedLcm_window_of_not_RH hRH X

theorem lcmMovingExponent_gt_three_halves (N : Nat) (hN : 3 <= N) :
    (3 / 2 : Real) < lcmMovingExponent (2 / 5) N := by
  have hLog := modifiedLcm_loglog_pos N hN
  have hPositive := div_pos (by norm_num : (0 : Real) < 2 / 5) hLog
  unfold lcmMovingExponent
  linarith only [hPositive]

theorem exists_modifiedLcm_fixed_window_violation (X : Nat) :
    exists N : Nat, X < N /\ 8 <= N /\
      forall k : Real, forall hk : 1 < k, k <= 3 / 2 ->
        1 < lcmRobinRatio k (zero_lt_one.trans hk) (modifiedLcm N) := by
  choose N hNX hN hWindow using exists_modifiedLcm_window X
  refine Exists.intro N (And.intro hNX (And.intro hN ?_))
  intro k hk hLe
  have hK := lcmMovingExponent_gt_three_halves N (by omega)
  have hLogBound := hWindow k hk (hLe.trans hK.le)
  have hNat : (1 : Real) < N := by exact_mod_cast (show 1 < N by omega)
  have hPositive :
      0 < 1 / (100 * Real.sqrt (N : Real) * Real.log (N : Real)) := by
    have hRoot := Real.sqrt_pos.2 (zero_lt_one.trans hNat)
    have hLog := Real.log_pos hNat
    positivity
  have hRatio := lcmRobinRatio_pos k (zero_lt_one.trans hk) hk (modifiedLcm N)
    (modifiedLcm_pos N).ne' (modifiedLcm_loglog_pos N (by omega))
  have hExp := Real.exp_lt_exp.mpr (hPositive.trans hLogBound)
  simpa only [Real.exp_zero, Real.exp_log hRatio] using hExp

theorem eventually_modifiedLcm_gt (X : Nat) :
    Filter.Eventually (fun N : Nat => X < modifiedLcm N) atTop := by
  have hTheta := tendsto_primeProfile_theta_atTop.eventually
    (eventually_gt_atTop (Real.log ((X : Real) + 1)))
  filter_upwards [hTheta] with N hN
  have hLogs := hN.trans_le (modifiedLcm_theta_le_log N)
  have hExp := Real.exp_lt_exp.mpr hLogs
  have hM : (0 : Real) < modifiedLcm N := by exact_mod_cast modifiedLcm_pos N
  rw [Real.exp_log (by positivity : (0 : Real) < (X : Real) + 1),
    Real.exp_log hM] at hExp
  have hBound : (X : Real) < modifiedLcm N := by linarith only [hExp]
  exact_mod_cast hBound

theorem exists_lcmRobinRatio_gt_one
    (k : Real) (hk : 1 < k) (hLe : k <= 3 / 2) (X : Nat) :
    exists n : Nat, X < n /\ 1 < lcmRobinRatio k (zero_lt_one.trans hk) n := by
  choose Y hY using eventually_atTop.mp (eventually_modifiedLcm_gt X)
  choose N hNY hEight hWindow using exists_modifiedLcm_fixed_window_violation Y
  exact Exists.intro (modifiedLcm N) (And.intro (hY N hNY.le) (hWindow k hk hLe))

end PrimeFactorOscillations

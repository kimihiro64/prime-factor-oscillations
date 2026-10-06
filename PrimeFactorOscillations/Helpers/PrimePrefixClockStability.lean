/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.PrimePrefixClockContinuity

/-!
# Stability of the physical prime-product clock

An inner-clock error of order one over the cutoff yields only a
logarithmic physical displacement, without assuming spatial closeness.
-/

set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace PrimeFactorOscillations
open Filter

private theorem exp_difference_right (u v : Real) :
    Real.exp u - Real.exp v <= Real.exp u * (u - v) := by
  have h := mul_le_mul_of_nonneg_left (Real.add_one_le_exp (v - u)) (Real.exp_nonneg u)
  rw [<- Real.exp_add, show u + (v - u) = v by ring] at h
  nlinarith

private theorem abs_exp_difference_bound (u v E : Real)
    (hu : Real.exp u <= E) (hv : Real.exp v <= E) :
    abs (Real.exp u - Real.exp v) <= E * abs (u - v) := by
  rcases le_total u v with huv | hvu
  . rw [abs_of_nonpos (sub_nonpos.mpr (Real.exp_le_exp.mpr huv)),
      abs_of_nonpos (sub_nonpos.mpr huv)]
    have h := (exp_difference_right v u).trans
      (mul_le_mul_of_nonneg_right hv (sub_nonneg.mpr huv))
    linarith
  . rw [abs_of_nonneg (sub_nonneg.mpr (Real.exp_le_exp.mpr hvu)),
      abs_of_nonneg (sub_nonneg.mpr hvu)]
    exact (exp_difference_right u v).trans
      (mul_le_mul_of_nonneg_right hu (sub_nonneg.mpr hvu))

/-- A cutoff-scale additive error in the inner logarithmic clock gives
only a logarithmic physical displacement. No spatial closeness is assumed. -/
theorem eventually_primePrefixClock_stability (K : Real) (hK : 0 <= K) :
    exists N0 : Nat, 2 <= N0 /\ forall N : Nat, N0 <= N -> forall u : Real,
      abs (u - primePrefixLogSum N) <= K / (N : Real) ->
      abs (Real.exp (Real.exp (u - Real.eulerMascheroniConstant)) -
        nicolasPrimeProductClock (N : Real)) <= 36 * K * Real.log (N : Real) := by
  have hn : Tendsto (fun N : Nat => (N : Real)) atTop atTop := tendsto_natCast_atTop_atTop
  have hClock := (tendsto_nicolasPrimeProductClock_div_self.comp hn).eventually_lt_const
    (by norm_num : (1 : Real) < 2)
  have hSlow : Tendsto (fun N : Nat => 6 * K * Real.log (N : Real) / (N : Real))
      atTop (nhds 0) := by
    have h := ((isLittleO_log_rpow_atTop (by norm_num : (0 : Real) < 1)).tendsto_div_nhds_zero).comp hn
    simpa only [Real.rpow_one, Function.comp_def, mul_div_assoc, mul_zero] using h.const_mul (6 * K)
  have hSmall := hSlow.eventually_lt_const (by norm_num : (0 : Real) < 1)
  choose N1 hN1 using (hClock.and hSmall).exists_forall_of_atTop
  refine Exists.intro (max N1 (max 2 (Nat.ceil K))) (And.intro
    ((le_max_left _ _).trans (le_max_right _ _)) ?_)
  intro N hN u hu
  have hN1' : N1 <= N := (le_max_left _ _).trans hN
  have hN2 : 2 <= N := (le_max_left _ _).trans ((le_max_right _ _).trans hN)
  have hCeil : Nat.ceil K <= N := (le_max_right _ _).trans ((le_max_right _ _).trans hN)
  have hKN : K <= (N : Real) := (Nat.le_ceil K).trans (by exact_mod_cast hCeil)
  have hNr : (0 : Real) < N := by exact_mod_cast (show 0 < N by omega)
  have hl : 0 < Real.log (N : Real) := Real.log_pos (by exact_mod_cast (show 1 < N by omega))
  let B := primePrefixLogSum N
  let g := Real.eulerMascheroniConstant
  let C := nicolasPrimeProductClock (N : Real)
  let A := Real.exp (B - g)
  let V := Real.exp (u - g)
  have hCId : C = Real.exp A := nicolasPrimeProductClock_nat_eq_prefix_clock N
  have hCPos : 0 < C := by rw [hCId]; positivity
  have hClockN := (hN1 N hN1').1
  change C / (N : Real) < 2 at hClockN
  have hCU : C <= 2 * (N : Real) := by
    have h := mul_lt_mul_of_pos_right hClockN hNr
    have hid : C / (N : Real) * N = C := by field_simp
    rw [hid] at h
    exact h.le
  have hA : A = Real.log C := by rw [hCId, Real.log_exp]
  have hAPos : 0 < A := Real.exp_pos _
  have hAU : A <= 2 * Real.log (N : Real) := by
    rw [hA]
    have h := Real.log_le_log hCPos hCU
    rw [Real.log_mul (by norm_num : Not ((2 : Real) = 0)) hNr.ne'] at h
    have h2 := Real.log_le_log (by norm_num : (0 : Real) < 2)
      (show (2 : Real) <= N by exact_mod_cast hN2)
    linarith
  have hdelta : K / (N : Real) <= 1 := (div_le_one hNr).mpr hKN
  have hUB : u <= B + 1 := by
    have h := (abs_le.mp hu).2
    dsimp [B] at *
    linarith
  have hVU : V <= Real.exp 1 * A := by
    calc
      _ <= Real.exp (B - g + 1) := Real.exp_le_exp.mpr (by linarith)
      _ = _ := by rw [Real.exp_add]; dsimp [A]; ring
  have hEU : A <= Real.exp 1 * A := by
    have hOne : 1 <= Real.exp (1 : Real) := by linarith [Real.add_one_le_exp (1 : Real)]
    simpa only [one_mul] using mul_le_mul_of_nonneg_right hOne hAPos.le
  have hExp : abs (V - A) <= Real.exp 1 * A * abs (u - B) := by
    have h := abs_exp_difference_bound (u - g) (B - g) (Real.exp 1 * A) hVU hEU
    simpa only [sub_sub_sub_cancel_right] using h
  have hDiff : abs (V - A) <= 6 * K * Real.log (N : Real) / (N : Real) := by
    calc
      _ <= Real.exp 1 * A * (K / (N : Real)) :=
        hExp.trans (mul_le_mul_of_nonneg_left hu (by positivity))
      _ <= (3 * (2 * Real.log (N : Real))) * (K / (N : Real)) :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul Real.exp_one_lt_three.le hAU hAPos.le (by norm_num)) (div_nonneg hK hNr.le)
      _ = _ := by ring
  have hVdiff : V <= A + 1 := by
    have h := (hN1 N hN1').2
    have hab := (le_abs_self (V - A)).trans hDiff
    linarith
  have hT : Real.exp V <= 6 * (N : Real) := by
    calc
      _ <= Real.exp (A + 1) := Real.exp_le_exp.mpr hVdiff
      _ = C * Real.exp 1 := by rw [Real.exp_add, hCId]
      _ <= (2 * (N : Real)) * 3 := mul_le_mul hCU Real.exp_one_lt_three.le
        (Real.exp_nonneg _) (by positivity)
      _ = _ := by ring
  have hC6 : C <= 6 * (N : Real) := hCU.trans (by linarith)
  have hPhysical := abs_exp_difference_bound V A (6 * (N : Real)) hT
    (by rwa [<- hCId])
  change abs (Real.exp V - C) <= _
  rw [hCId]
  calc
    _ <= 6 * (N : Real) * abs (V - A) := hPhysical
    _ <= 6 * (N : Real) * (6 * K * Real.log (N : Real) / (N : Real)) :=
      mul_le_mul_of_nonneg_left hDiff (by positivity)
    _ = _ := by field_simp; ring

end PrimeFactorOscillations

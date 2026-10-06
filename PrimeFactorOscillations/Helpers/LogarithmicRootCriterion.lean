/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.ConsecutiveRootCriterion
import PrimeFactorOscillations.Helpers.NicolasPolylogDecay

/-!
# An unconditional signed bound with logarithmically reduced degree

For each fixed natural m, use the actual consecutive-root-plus-prime law of
degree 1 + floor(N / log(N)^(m+1)). Its complete profile error, multiplied by
log(N)^(m+2), tends to -1. The family varies with N; this is not a fixed-family
RH criterion, an RH proof, or a new prime-gap supply theorem.
-/

set_option autoImplicit false
set_option Elab.async false

noncomputable section
namespace PrimeFactorOscillations
open Filter Robin1984

def logarithmicRootDegree (m N : Nat) : Nat :=
  1 + Nat.floor ((N : Real) / Real.log N ^ (m + 1))

theorem logarithmicRootDegree_pos (m N : Nat) : 1 <= logarithmicRootDegree m N := by
  unfold logarithmicRootDegree
  omega

private theorem root_log_pow_ge (m : Nat) {L : Real} (hL : 1 <= L) :
    L <= L ^ (m + 1) := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [pow_succ]
    have hp : 0 <= L ^ (m + 1) := pow_nonneg (by linarith) _
    nlinarith

theorem logarithmicRootDegree_le (m N : Nat) (hN : 2 <= N)
    (hLog : 2 <= Real.log N) : logarithmicRootDegree m N <= N := by
  have hn : (2 : Real) <= N := by exact_mod_cast hN
  have hPow : 2 <= Real.log N ^ (m + 1) :=
    hLog.trans (root_log_pow_ge m (by linarith))
  have hA : (N : Real) / Real.log N ^ (m + 1) <= (N : Real) / 2 :=
    div_le_div_of_nonneg_left (by positivity) (by norm_num) hPow
  have hf := Nat.floor_le (show 0 <= (N : Real) / Real.log N ^ (m + 1) by positivity)
  have hd : (logarithmicRootDegree m N : Real) <= (N : Real) := by
    simp only [logarithmicRootDegree, Nat.cast_add, Nat.cast_one]
    linarith
  exact_mod_cast hd

theorem tendsto_logarithmicRootTail_scaled (m : Nat) :
    Tendsto (fun N : Nat =>
      primeAddedRootTail N ((logarithmicRootDegree m N : Real) - 1) *
        Real.log N ^ (m + 2)) atTop (nhds 1) := by
  have hA : Tendsto (fun N : Nat => Real.log N ^ (m + 1) / (N : Real))
      atTop (nhds 0) :=
    (tendsto_log_pow_div_self m).comp tendsto_natCast_atTop_atTop
  have hLo := ((tendsto_const_nhds (x := (1 : Real))).sub
    (hA.const_mul (3 / 2 : Real))).mul tendsto_primeProfileQuadraticTail_scaled
  have hHi := tendsto_primeProfileQuadraticTail_scaled
  have hLogLarge := (Real.tendsto_log_atTop.comp
    (tendsto_natCast_atTop_atTop : Tendsto (fun N : Nat => (N : Real)) atTop atTop)).eventually_ge_atTop 2
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le'
    (show Tendsto (fun N : Nat =>
      (1 - (3 / 2 : Real) * (Real.log N ^ (m + 1) / (N : Real))) *
        (primeProfileQuadraticTail N * ((N : Real) * Real.log N)))
      atTop (nhds 1) from by simpa only [mul_zero, sub_zero, one_mul] using hLo)
    hHi
  all_goals
    filter_upwards [eventually_ge_atTop (2 : Nat), hLogLarge] with N hN hLog
    change 2 <= Real.log (N : Real) at hLog
    have hn : (0 : Real) < N := by exact_mod_cast (show 0 < N by omega)
    have hL : 0 < Real.log N := by linarith
    let b : Real := Nat.floor ((N : Real) / Real.log N ^ (m + 1))
    have hb : 0 <= b := by dsimp only [b]; positivity
    have hbHi : b <= (N : Real) / Real.log N ^ (m + 1) :=
      Nat.floor_le (by positivity)
    have hbLo : (N : Real) / Real.log N ^ (m + 1) - 1 <= b := by
      have h := Nat.lt_floor_add_one ((N : Real) / Real.log N ^ (m + 1))
      dsimp only [b]
      linarith
    have hPow : 1 <= Real.log N ^ (m + 1) :=
      (show (1 : Real) <= Real.log N by linarith).trans
        (root_log_pow_ge m (by linarith))
    have hbN : b <= (N : Real) := by
      calc
        b <= (N : Real) / Real.log N ^ (m + 1) := hbHi
        _ <= (N : Real) / 1 := div_le_div_of_nonneg_left hn.le (by norm_num) hPow
        _ = _ := div_one _
    have hdEq : (logarithmicRootDegree m N : Real) - 1 = b := by
      simp only [logarithmicRootDegree, Nat.cast_add, Nat.cast_one]
      dsimp only [b]
      ring
    rw [hdEq]
    have hTail := primeAddedRootTail_bounds N (by omega) b hb
    have hQ := (primeProfileQuadraticTail_bounds N (by omega)).1
    have hScale : 0 <= Real.log N ^ (m + 2) := pow_nonneg hL.le _
    have hPower : Real.log N ^ (m + 2) =
        Real.log N ^ (m + 1) * Real.log N := by
      rw [show m + 2 = (m + 1) + 1 by omega, pow_succ]
  . have hSquare : b ^ (2 : Nat) / (2 * (N : Real) ^ (2 : Nat)) <= 1 / 2 := by
      calc
        _ <= (N : Real) ^ (2 : Nat) / (2 * (N : Real) ^ (2 : Nat)) :=
          div_le_div_of_nonneg_right (by nlinarith) (by positivity)
        _ = _ := by field_simp
    have hLower :
        ((N : Real) / Real.log N ^ (m + 1) - 3 / 2) *
          primeProfileQuadraticTail N <= primeAddedRootTail N b := by
      exact (mul_le_mul_of_nonneg_right (by linarith) hQ).trans hTail.1
    have hEq :
        (1 - (3 / 2 : Real) * (Real.log N ^ (m + 1) / (N : Real))) *
          (primeProfileQuadraticTail N * ((N : Real) * Real.log N)) =
        (((N : Real) / Real.log N ^ (m + 1) - 3 / 2) *
          primeProfileQuadraticTail N) * Real.log N ^ (m + 2) := by
      rw [hPower]
      field_simp <;> ring
    rw [hEq]
    exact mul_le_mul_of_nonneg_right hLower hScale
  . have hUpper : primeAddedRootTail N b <=
        ((N : Real) / Real.log N ^ (m + 1)) * primeProfileQuadraticTail N :=
      hTail.2.trans (mul_le_mul_of_nonneg_right hbHi hQ)
    have hEq : (((N : Real) / Real.log N ^ (m + 1)) *
        primeProfileQuadraticTail N) * Real.log N ^ (m + 2) =
        primeProfileQuadraticTail N * ((N : Real) * Real.log N) := by
      rw [hPower]
      field_simp
    rw [<- hEq]
    exact mul_le_mul_of_nonneg_right hUpper hScale

def logarithmicRootLogError (m N : Nat) : Real :=
  (consecutiveRootLaw (logarithmicRootDegree m N)
    (logarithmicRootDegree_pos m N)).logError N 1

theorem tendsto_logarithmicRootLogError_scaled (m : Nat) :
    Tendsto (fun N : Nat => logarithmicRootLogError m N * Real.log N ^ (m + 2))
      atTop (nhds (-1)) := by
  have hF := (tendsto_nicolasLog_mul_log_pow_zero_unconditionally (m + 1)).comp
    (tendsto_natCast_atTop_atTop : Tendsto (fun N : Nat => (N : Real)) atTop atTop)
  have h := hF.sub (tendsto_logarithmicRootTail_scaled m)
  simp only [zero_sub] at h
  apply h.congr'
  have hLogLarge := (Real.tendsto_log_atTop.comp
    (tendsto_natCast_atTop_atTop : Tendsto (fun N : Nat => (N : Real)) atTop atTop)).eventually_ge_atTop 2
  filter_upwards [eventually_ge_atTop (2 : Nat), hLogLarge,
    tendsto_primeProfile_theta_atTop.eventually_gt_atTop 1] with N hN hLog hTheta
  rw [logarithmicRootLogError, consecutiveRootLaw_logError_exact _ _ N
    (logarithmicRootDegree_le m N hN hLog) hTheta]
  dsimp only [Function.comp_def]
  rw [show m + 1 + 1 = m + 2 by omega]
  ring

theorem eventually_logarithmicRootLogError_neg (m : Nat) :
    Filter.Eventually (fun N : Nat => logarithmicRootLogError m N < 0) atTop := by
  have h := (tendsto_logarithmicRootLogError_scaled m).eventually_lt_const
    (by norm_num : (-1 : Real) < 0)
  filter_upwards [h, eventually_ge_atTop (2 : Nat)] with N hN hTwo
  have hLog : 0 < Real.log (N : Real) :=
    Real.log_pos (by exact_mod_cast (show 1 < N by omega))
  by_contra hNon
  have hPos := mul_nonneg (le_of_not_gt hNon) (pow_nonneg hLog.le (m + 2))
  linarith

/-- The actual growing-degree family has a complete negative signed profile
without RH, for every fixed logarithmic degree reduction. -/
theorem publicLogarithmicRootSignedBound (m : Nat) :
    Filter.Tendsto
      (fun N : Nat => logarithmicRootLogError m N * Real.log N ^ (m + 2))
      Filter.atTop (nhds (-1)) /\
    Filter.Eventually (fun N : Nat => logarithmicRootLogError m N < 0) Filter.atTop := by
  exact And.intro (tendsto_logarithmicRootLogError_scaled m)
    (eventually_logarithmicRootLogError_neg m)

end PrimeFactorOscillations

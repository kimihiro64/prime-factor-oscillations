/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.NicolasQuantitativeClock
import PrimeFactorOscillations.Helpers.PrimeReciprocalSquareTail

/-!
# A sharp root-budget correction and an unconditional signed estimate

The exact logarithmic prime tail produced by consecutive-root polynomial
families is squeezed between explicit quadratic-tail bounds. With budget
N - 1, the full Nicolas error minus that tail has logarithmically scaled
limit -1, without RH. The arithmetic polynomial counting interpretation is
proved separately in the research note; this module proves the analytic
signed-tail statement. The growing budget lies outside the established
RH-sensitive correction-width range.
-/

set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace PrimeFactorOscillations
open Filter Robin1984

def primeAddedRootTail (N : Nat) (b : Real) : Real :=
  tsum (fun p : {p : Nat.Primes // N < (p : Nat)} =>
    Real.log (1 + b * (primeProfileWeight (p.val : Nat)) ^ (2 : Nat)))

theorem primeAddedRootTail_bounds (N : Nat) (hN : 1 <= N)
    (b : Real) (hb : 0 <= b) :
    (b - b ^ (2 : Nat) / (2 * (N : Real) ^ (2 : Nat))) *
        primeProfileQuadraticTail N <= primeAddedRootTail N b /\
      primeAddedRootTail N b <= b * primeProfileQuadraticTail N := by
  let T := {p : Nat.Primes // N < (p : Nat)}
  let w : T -> Real := fun p => primeProfileWeight (p.val : Nat)
  let f : T -> Real := fun p => Real.log (1 + b * (w p) ^ (2 : Nat))
  have hs : Summable (fun p : T => (w p) ^ (2 : Nat)) :=
    summable_primeProfileWeight_sq.subtype _
  have hp (p : T) : 0 <= f p /\ f p <= b * (w p) ^ (2 : Nat) := by
    have ht : 0 <= b * (w p) ^ (2 : Nat) := mul_nonneg hb (sq_nonneg _)
    refine And.intro (Real.log_nonneg (by linarith)) ?_
    have h := Real.log_le_sub_one_of_pos (by positivity : 0 < 1 + b * (w p) ^ (2 : Nat))
    dsimp [f]
    linarith
  have hf : Summable f := Summable.of_nonneg_of_le (fun p => (hp p).1)
    (fun p => (hp p).2) (hs.mul_left b)
  have hn : (0 : Real) < N := by exact_mod_cast (show 0 < N by omega)
  have hLow (p : T) :
      (b - b ^ (2 : Nat) / (2 * (N : Real) ^ (2 : Nat))) * (w p) ^ (2 : Nat) <= f p := by
    have hw0 : 0 <= w p := primeProfileWeight_nonneg _
    have hwp : N <= (p.val : Nat) - 1 := by omega
    have hw : w p <= 1 / (N : Real) := by
      dsimp [w, primeProfileWeight]
      exact one_div_le_one_div_of_le hn (by exact_mod_cast hwp)
    have hw2 : (w p) ^ (2 : Nat) <= 1 / (N : Real) ^ (2 : Nat) := by
      calc
        _ <= (1 / (N : Real)) ^ (2 : Nat) := by nlinarith
        _ = _ := by rw [div_pow]; norm_num
    have hr := (Real.log_one_add_cubic_remainder_bounds
      (b * (w p) ^ (2 : Nat)) (mul_nonneg hb (sq_nonneg _))).1
    have hErr := mul_le_mul_of_nonneg_left hw2
      (show 0 <= b ^ (2 : Nat) / 2 * (w p) ^ (2 : Nat) by positivity)
    have hErr' : (b * (w p) ^ (2 : Nat)) ^ (2 : Nat) / 2 <=
        b ^ (2 : Nat) / (2 * (N : Real) ^ (2 : Nat)) * (w p) ^ (2 : Nat) := by
      convert hErr using 1 <;> ring
    dsimp [f]
    nlinarith only [hr, hErr']
  refine And.intro ?_ ?_
  . calc
      _ = tsum (fun p : T =>
          (b - b ^ (2 : Nat) / (2 * (N : Real) ^ (2 : Nat))) * (w p) ^ (2 : Nat)) := by
        rw [tsum_mul_left]
        rfl
      _ <= tsum f := Summable.tsum_le_tsum hLow (hs.mul_left _) hf
      _ = _ := rfl
  . calc
      _ = tsum f := rfl
      _ <= tsum (fun p : T => b * (w p) ^ (2 : Nat)) :=
        Summable.tsum_le_tsum (fun p => (hp p).2) hf (hs.mul_left b)
      _ = _ := by rw [tsum_mul_left]; rfl

theorem tendsto_primeAddedRootTail_diagonal_scaled :
    Tendsto (fun N : Nat => primeAddedRootTail N ((N : Real) - 1) * Real.log N)
      atTop (nhds 1) := by
  have hInv : Tendsto (fun N : Nat => 1 / (N : Real)) atTop (nhds 0) := by
    simpa only [one_div, Function.comp_def] using
      (tendsto_inv_atTop_zero : Tendsto (fun x : Real => Inv.inv x) atTop (nhds 0)).comp
        tendsto_natCast_atTop_atTop
  have hLo := ((tendsto_const_nhds (x := (1 : Real))).sub
    (hInv.const_mul (3 / 2 : Real))).mul tendsto_primeProfileQuadraticTail_scaled
  have hHi := ((tendsto_const_nhds (x := (1 : Real))).sub hInv).mul
    tendsto_primeProfileQuadraticTail_scaled
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le'
    (show Tendsto (fun N : Nat => (1 - (3 / 2 : Real) * (1 / (N : Real))) *
      (primeProfileQuadraticTail N * ((N : Real) * Real.log N))) atTop (nhds 1) from by
        simpa only [mul_zero, sub_zero, one_mul] using hLo)
    (show Tendsto (fun N : Nat => (1 - 1 / (N : Real)) *
      (primeProfileQuadraticTail N * ((N : Real) * Real.log N))) atTop (nhds 1) from by
        simpa only [sub_zero, one_mul] using hHi)
  . filter_upwards [eventually_ge_atTop (2 : Nat)] with N hN
    have hn : (0 : Real) < N := by exact_mod_cast (show 0 < N by omega)
    have hn2 : (2 : Real) <= N := by exact_mod_cast hN
    have hl : 0 <= Real.log (N : Real) := Real.log_nonneg (by linarith)
    have hb := primeAddedRootTail_bounds N (by omega) ((N : Real) - 1) (by linarith)
    have hq := (primeProfileQuadraticTail_bounds N (by omega)).1
    have he : ((N : Real) - 1) ^ (2 : Nat) / (2 * (N : Real) ^ (2 : Nat)) <= 1 / 2 := by
      calc
        _ <= (N : Real) ^ (2 : Nat) / (2 * (N : Real) ^ (2 : Nat)) :=
          div_le_div_of_nonneg_right (by nlinarith) (by positivity)
        _ = _ := by field_simp
    have hc : ((N : Real) - 3 / 2) * primeProfileQuadraticTail N <=
        primeAddedRootTail N ((N : Real) - 1) := by
      exact (mul_le_mul_of_nonneg_right (by linarith) hq).trans hb.1
    have hEq : (1 - (3 / 2 : Real) * (1 / (N : Real))) *
        (primeProfileQuadraticTail N * ((N : Real) * Real.log N)) =
        (((N : Real) - 3 / 2) * primeProfileQuadraticTail N) * Real.log N := by
      field_simp
    rw [hEq]
    exact mul_le_mul_of_nonneg_right hc hl
  . filter_upwards [eventually_ge_atTop (2 : Nat)] with N hN
    have hn : (0 : Real) < N := by exact_mod_cast (show 0 < N by omega)
    have hn2 : (2 : Real) <= N := by exact_mod_cast hN
    have hl : 0 <= Real.log (N : Real) := Real.log_nonneg (by linarith)
    have hb := primeAddedRootTail_bounds N (by omega) ((N : Real) - 1) (by linarith)
    have hEq : (1 - 1 / (N : Real)) *
        (primeProfileQuadraticTail N * ((N : Real) * Real.log N)) =
        (((N : Real) - 1) * primeProfileQuadraticTail N) * Real.log N := by
      field_simp
    rw [hEq]
    exact mul_le_mul_of_nonneg_right hb.2 hl

def primeAddedRootSignedError (N : Nat) : Real :=
  nicolasLogMertensOscillation (N : Real) - primeAddedRootTail N ((N : Real) - 1)

theorem tendsto_primeAddedRootSignedError_scaled :
    Tendsto (fun N : Nat => primeAddedRootSignedError N * Real.log N)
      atTop (nhds (-1)) := by
  have hF := tendsto_nicolasLog_mul_log_zero_unconditionally.comp
    (tendsto_natCast_atTop_atTop : Tendsto (fun N : Nat => (N : Real)) atTop atTop)
  have h := hF.sub tendsto_primeAddedRootTail_diagonal_scaled
  simpa only [Function.comp_def, zero_sub, primeAddedRootSignedError, sub_mul] using h

theorem eventually_primeAddedRootSignedError_neg :
    Filter.Eventually (fun N : Nat => primeAddedRootSignedError N < 0) atTop := by
  have h := tendsto_primeAddedRootSignedError_scaled.eventually_lt_const
    (by norm_num : (-1 : Real) < 0)
  filter_upwards [h, eventually_ge_atTop (2 : Nat)] with N hN hTwo
  have hLog : 0 < Real.log (N : Real) := Real.log_pos (by exact_mod_cast (show 1 < N by omega))
  by_contra hNon
  have hPos := mul_nonneg (le_of_not_gt hNon) hLog.le
  linarith

end PrimeFactorOscillations

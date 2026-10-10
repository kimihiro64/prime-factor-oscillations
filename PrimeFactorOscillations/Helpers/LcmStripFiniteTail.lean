/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.LcmFiniteTailAsymptotic

/-!
# Finite prime-tail limits at a general strip exponent

The moving endpoint has limit 2-b and the normalization is N^(1-b) log N.
Every dilation and finite summation length is fixed before the cutoff limit.
The proof reuses the exact previous height normalization; it assumes no
zero-free region. The finite lower-tail inequality remains the existing one.
-/

set_option autoImplicit false
set_option Elab.async false

noncomputable section
namespace PrimeFactorOscillations
open Filter

def lcmStripMovingExponent (b c : Real) (N : Nat) : Real :=
  lcmMovingExponent c N + (1 / 2 - b)

theorem tendsto_lcmStripMovingExponent (b c : Real) :
    Tendsto (lcmStripMovingExponent b c) atTop (nhds (2 - b)) := by
  have h := (tendsto_lcmMovingExponent c).add_const (1 / 2 - b)
  rw [show (3 / 2 : Real) + (1 / 2 - b) = 2 - b by ring] at h
  exact h

theorem tendsto_lcmStripMovingExponent_fixed_power
    (a b c : Real) (ha : 0 < a) :
    Tendsto (fun N : Nat => a ^ (2 - lcmStripMovingExponent b c N))
      atTop (nhds (a ^ b)) := by
  have hExponent := (tendsto_const_nhds (x := (2 : Real))).sub
    (tendsto_lcmStripMovingExponent b c)
  rw [show (2 : Real) - (2 - b) = b by ring] at hExponent
  have hLinear := hExponent.const_mul (Real.log a)
  have h := (Real.continuous_exp.tendsto (Real.log a * b)).comp hLinear
  simpa only [Real.rpow_def_of_pos ha, Function.comp_def] using h

theorem lcmStripMovingExponent_reference_scale (b c : Real) (N : Nat) :
    (2 - b) - lcmStripMovingExponent b c N = 3 / 2 - lcmMovingExponent c N := by
  unfold lcmStripMovingExponent
  ring

theorem tendsto_lcmStripMovingExponent_power_scale (b c : Real) :
    Tendsto (fun N : Nat =>
      (N : Real) ^ ((2 - b) - lcmStripMovingExponent b c N))
      atTop (nhds (Real.exp (-c))) := by
  simpa only [lcmStripMovingExponent_reference_scale] using
    tendsto_lcmMovingExponent_power_scale c

theorem tendsto_lcmStripMovingExponent_mixed_tail_scaled
    (a d b c : Real) (ha : 0 < a) (hd : 0 < d) :
    Tendsto (fun N : Nat =>
      (a * (N : Real)) ^ (2 - lcmStripMovingExponent b c N) *
        lcmRealSquareTail (d * (N : Real)) * (N : Real) ^ (1 - b) *
          Real.log (N : Real)) atTop
      (nhds ((a ^ b / d) * Real.exp (-c))) := by
  have hA := tendsto_lcmStripMovingExponent_fixed_power a b c ha
  have hD := tendsto_lcmRealSquareTail_dilated d hd
  have hLog := tendsto_lcm_log_dilation_ratio d hd
  have hPower := tendsto_lcmMovingExponent_power_scale c
  have h := (((hA.mul hD).mul hLog).mul hPower).div_const d
  simp only [mul_one] at h
  have hEnd : a ^ b * Real.exp (-c) / d = (a ^ b / d) * Real.exp (-c) := by ring
  rw [hEnd] at h
  apply h.congr'
  have hn : Tendsto (fun N : Nat => (N : Real)) atTop atTop :=
    tendsto_natCast_atTop_atTop
  filter_upwards [eventually_ge_atTop (1 : Nat), hn.eventually_ge_atTop (2 / d)]
    with N hN hNd
  have hx : (0 : Real) < N := by exact_mod_cast (show 0 < N by omega)
  have hdN : (2 : Real) <= d * (N : Real) := by
    calc
      2 = d * (2 / d) := by field_simp [hd.ne']
      _ <= d * (N : Real) := mul_le_mul_of_nonneg_left hNd hd.le
  have hLogDN : Not (Real.log (d * (N : Real)) = 0) :=
    (Real.log_pos (by linarith)).ne'
  have hExponent : (N : Real) ^ (2 - lcmStripMovingExponent b c N) *
      (N : Real) ^ (1 - b) =
        (N : Real) * (N : Real) ^ (3 / 2 - lcmMovingExponent c N) := by
    rw [<- Real.rpow_add hx]
    calc
      _ = (N : Real) ^ (1 + (3 / 2 - lcmMovingExponent c N)) := by
        congr 1
        unfold lcmStripMovingExponent
        ring
      _ = _ := by rw [Real.rpow_add hx, Real.rpow_one]
  rw [Real.mul_rpow ha.le hx.le]
  calc
    _ = a ^ (2 - lcmStripMovingExponent b c N) * lcmRealSquareTail (d * (N : Real)) *
        ((N : Real) * (N : Real) ^ (3 / 2 - lcmMovingExponent c N)) *
          Real.log (N : Real) := by
      field_simp [hd.ne', hLogDN]
    _ = a ^ (2 - lcmStripMovingExponent b c N) * lcmRealSquareTail (d * (N : Real)) *
        ((N : Real) ^ (2 - lcmStripMovingExponent b c N) * (N : Real) ^ (1 - b)) *
          Real.log (N : Real) := by rw [hExponent]
    _ = _ := by ring

def lcmStripFiniteTailCoefficient (b q : Real) (m : Nat) : Real :=
  1 + (Finset.range m).sum (fun j =>
    ((q ^ (j + 1)) ^ b - (q ^ j) ^ b) / q ^ (j + 1))

theorem tendsto_lcmStripFiniteTailLowerSum_scaled
    (b q c : Real) (hq : 0 < q) (m : Nat) :
    Tendsto (fun N : Nat =>
      lcmFiniteTailLowerSum N m q (lcmStripMovingExponent b c N) *
        (N : Real) ^ (1 - b) * Real.log (N : Real)) atTop
      (nhds (lcmStripFiniteTailCoefficient b q m * Real.exp (-c))) := by
  have hBase : Tendsto (fun N : Nat =>
      (N : Real) ^ (2 - lcmStripMovingExponent b c N) * primeReciprocalSquareTail N *
        (N : Real) ^ (1 - b) * Real.log (N : Real)) atTop (nhds (Real.exp (-c))) := by
    simpa only [one_mul, Real.one_rpow, div_one, lcmRealSquareTail_nat] using
      tendsto_lcmStripMovingExponent_mixed_tail_scaled 1 1 b c (by norm_num) (by norm_num)
  have hTerm (j : Nat) : Tendsto (fun N : Nat =>
      (((N : Real) * q ^ (j + 1)) ^ (2 - lcmStripMovingExponent b c N) -
        ((N : Real) * q ^ j) ^ (2 - lcmStripMovingExponent b c N)) *
          lcmRealSquareTail ((N : Real) * q ^ (j + 1)) *
            (N : Real) ^ (1 - b) * Real.log (N : Real)) atTop
      (nhds ((((q ^ (j + 1)) ^ b - (q ^ j) ^ b) / q ^ (j + 1)) * Real.exp (-c))) := by
    have h1 := tendsto_lcmStripMovingExponent_mixed_tail_scaled
      (q ^ (j + 1)) (q ^ (j + 1)) b c (pow_pos hq _) (pow_pos hq _)
    have h0 := tendsto_lcmStripMovingExponent_mixed_tail_scaled
      (q ^ j) (q ^ (j + 1)) b c (pow_pos hq _) (pow_pos hq _)
    have h := h1.sub h0
    have hEnd :
        ((q ^ (j + 1)) ^ b / q ^ (j + 1)) * Real.exp (-c) -
          ((q ^ j) ^ b / q ^ (j + 1)) * Real.exp (-c) =
        (((q ^ (j + 1)) ^ b - (q ^ j) ^ b) / q ^ (j + 1)) * Real.exp (-c) := by ring
    rw [hEnd] at h
    apply h.congr'
    filter_upwards [] with N
    rw [mul_comm (N : Real) (q ^ (j + 1)), mul_comm (N : Real) (q ^ j)]
    ring
  induction m with
  | zero =>
      simpa only [lcmFiniteTailLowerSum, lcmStripFiniteTailCoefficient,
        Finset.sum_range_zero, add_zero, one_mul] using hBase
  | succ m ih =>
      have h := ih.add (hTerm m)
      have hEnd : lcmStripFiniteTailCoefficient b q m * Real.exp (-c) +
          (((q ^ (m + 1)) ^ b - (q ^ m) ^ b) / q ^ (m + 1)) * Real.exp (-c) =
          lcmStripFiniteTailCoefficient b q (m + 1) * Real.exp (-c) := by
        simp only [lcmStripFiniteTailCoefficient, Finset.sum_range_succ]
        ring
      rw [hEnd] at h
      apply h.congr'
      filter_upwards [] with N
      simp only [lcmFiniteTailLowerSum, Finset.sum_range_succ]
      ring

end PrimeFactorOscillations

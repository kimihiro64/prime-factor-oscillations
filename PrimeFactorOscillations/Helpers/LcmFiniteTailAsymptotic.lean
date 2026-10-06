/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.LcmTailLimit

/-!
# The finite positive tail at the actual moving exponent

Combine fixed-dilation prime-square tails before taking the finite geometric
sum. Every dilation and the number of terms are fixed in these limits.
-/

set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace PrimeFactorOscillations
open Filter

theorem tendsto_lcmMovingExponent_mixed_tail_scaled
    (a b c : Real) (ha : 0 < a) (hb : 0 < b) :
    Tendsto (fun N : Nat =>
      (a * (N : Real)) ^ (2 - lcmMovingExponent c N) *
        lcmRealSquareTail (b * (N : Real)) * Real.sqrt (N : Real) *
          Real.log (N : Real)) atTop
      (nhds ((a ^ (1 / 2 : Real) / b) * Real.exp (-c))) := by
  have hA := tendsto_lcmMovingExponent_fixed_power a c ha
  have hB := tendsto_lcmRealSquareTail_dilated b hb
  have hLog := tendsto_lcm_log_dilation_ratio b hb
  have hPower := tendsto_lcmMovingExponent_power_scale c
  have h := (((hA.mul hB).mul hLog).mul hPower).div_const b
  simp only [mul_one] at h
  have hEnd : a ^ (1 / 2 : Real) * Real.exp (-c) / b =
      (a ^ (1 / 2 : Real) / b) * Real.exp (-c) := by ring
  rw [hEnd] at h
  apply h.congr'
  have hn : Tendsto (fun N : Nat => (N : Real)) atTop atTop :=
    tendsto_natCast_atTop_atTop
  filter_upwards [eventually_ge_atTop (1 : Nat), hn.eventually_ge_atTop (2 / b)] with N hN hNb
  have hx : (0 : Real) < N := by exact_mod_cast (show 0 < N by omega)
  have hbN : (2 : Real) <= b * (N : Real) := by
    calc
      2 = b * (2 / b) := by field_simp [hb.ne']
      _ <= b * (N : Real) := mul_le_mul_of_nonneg_left hNb hb.le
  have hLogBN : Not (Real.log (b * (N : Real)) = 0) :=
    (Real.log_pos (by linarith)).ne'
  have hExponent : (N : Real) ^ (2 - lcmMovingExponent c N) *
      Real.sqrt (N : Real) = (N : Real) *
        (N : Real) ^ (3 / 2 - lcmMovingExponent c N) := by
    rw [Real.sqrt_eq_rpow, <- Real.rpow_add hx]
    calc
      (N : Real) ^ (2 - lcmMovingExponent c N + 1 / 2) =
          (N : Real) ^ (1 + (3 / 2 - lcmMovingExponent c N)) := by
        congr 1
        ring
      _ = _ := by rw [Real.rpow_add hx, Real.rpow_one]
  rw [Real.mul_rpow ha.le hx.le]
  calc
    _ = a ^ (2 - lcmMovingExponent c N) * lcmRealSquareTail (b * (N : Real)) *
        ((N : Real) * (N : Real) ^ (3 / 2 - lcmMovingExponent c N)) *
          Real.log (N : Real) := by
      field_simp [hb.ne', hLogBN]
    _ = a ^ (2 - lcmMovingExponent c N) * lcmRealSquareTail (b * (N : Real)) *
        ((N : Real) ^ (2 - lcmMovingExponent c N) * Real.sqrt (N : Real)) *
          Real.log (N : Real) := by rw [hExponent]
    _ = _ := by ring

def lcmFiniteTailLowerSum (N m : Nat) (q k : Real) : Real :=
  (N : Real) ^ (2 - k) * primeReciprocalSquareTail N +
    (Finset.range m).sum (fun j =>
      (((N : Real) * q ^ (j + 1)) ^ (2 - k) -
        ((N : Real) * q ^ j) ^ (2 - k)) *
          lcmRealSquareTail ((N : Real) * q ^ (j + 1)))

def lcmFiniteTailCoefficient (q : Real) (m : Nat) : Real :=
  1 + (Finset.range m).sum (fun j =>
    ((q ^ (j + 1)) ^ (1 / 2 : Real) - (q ^ j) ^ (1 / 2 : Real)) / q ^ (j + 1))

theorem lcmFiniteTailLowerSum_le
    (N m : Nat) (q k : Real) (hN : 0 < N) (hq : 1 <= q)
    (hk : 1 < k) (hkTwo : k <= 2) :
    lcmFiniteTailLowerSum N m q k <=
      lcmFiniteZetaTail k (primeProfilePrefixSet N) := by
  exact lcmFiniteZetaTail_staircase_lower N m q k hN hq hk hkTwo

theorem tendsto_lcmFiniteTailLowerSum_scaled
    (q c : Real) (hq : 0 < q) (m : Nat) :
    Tendsto (fun N : Nat =>
      lcmFiniteTailLowerSum N m q (lcmMovingExponent c N) *
        Real.sqrt (N : Real) * Real.log (N : Real)) atTop
      (nhds (lcmFiniteTailCoefficient q m * Real.exp (-c))) := by
  have hBase : Tendsto (fun N : Nat =>
      (N : Real) ^ (2 - lcmMovingExponent c N) * primeReciprocalSquareTail N *
        Real.sqrt (N : Real) * Real.log (N : Real)) atTop (nhds (Real.exp (-c))) := by
    simpa only [one_mul, Real.one_rpow, div_one, lcmRealSquareTail_nat] using
      tendsto_lcmMovingExponent_mixed_tail_scaled 1 1 c (by norm_num) (by norm_num)
  have hTerm (j : Nat) : Tendsto (fun N : Nat =>
      (((N : Real) * q ^ (j + 1)) ^ (2 - lcmMovingExponent c N) -
        ((N : Real) * q ^ j) ^ (2 - lcmMovingExponent c N)) *
          lcmRealSquareTail ((N : Real) * q ^ (j + 1)) *
            Real.sqrt (N : Real) * Real.log (N : Real)) atTop
      (nhds ((((q ^ (j + 1)) ^ (1 / 2 : Real) -
        (q ^ j) ^ (1 / 2 : Real)) / q ^ (j + 1)) * Real.exp (-c))) := by
    have h1 := tendsto_lcmMovingExponent_mixed_tail_scaled
      (q ^ (j + 1)) (q ^ (j + 1)) c (pow_pos hq _) (pow_pos hq _)
    have h0 := tendsto_lcmMovingExponent_mixed_tail_scaled
      (q ^ j) (q ^ (j + 1)) c (pow_pos hq _) (pow_pos hq _)
    have h := h1.sub h0
    have hEnd :
        ((q ^ (j + 1)) ^ (1 / 2 : Real) / q ^ (j + 1)) * Real.exp (-c) -
          ((q ^ j) ^ (1 / 2 : Real) / q ^ (j + 1)) * Real.exp (-c) =
        (((q ^ (j + 1)) ^ (1 / 2 : Real) -
          (q ^ j) ^ (1 / 2 : Real)) / q ^ (j + 1)) * Real.exp (-c) := by ring
    rw [hEnd] at h
    apply h.congr'
    filter_upwards [] with N
    rw [mul_comm (N : Real) (q ^ (j + 1)), mul_comm (N : Real) (q ^ j)]
    ring
  induction m with
  | zero =>
      simpa only [lcmFiniteTailLowerSum, lcmFiniteTailCoefficient,
        Finset.sum_range_zero, add_zero, one_mul] using hBase
  | succ m ih =>
      have h := ih.add (hTerm m)
      have hEnd : lcmFiniteTailCoefficient q m * Real.exp (-c) +
          (((q ^ (m + 1)) ^ (1 / 2 : Real) -
            (q ^ m) ^ (1 / 2 : Real)) / q ^ (m + 1)) * Real.exp (-c) =
          lcmFiniteTailCoefficient q (m + 1) * Real.exp (-c) := by
        simp only [lcmFiniteTailCoefficient, Finset.sum_range_succ]
        ring
      rw [hEnd] at h
      apply h.congr'
      filter_upwards [] with N
      simp only [lcmFiniteTailLowerSum, Finset.sum_range_succ]
      ring

theorem lcmFiniteTailCoefficient_sq (s : Real) (hs : 0 < s) (m : Nat) :
    lcmFiniteTailCoefficient (s ^ 2) m = 1 + 1 / s - (1 / s) ^ (m + 1) := by
  have hRoot (j : Nat) : ((s ^ 2) ^ j) ^ (1 / 2 : Real) = s ^ j := by
    rw [<- Real.sqrt_eq_rpow, <- pow_mul, Nat.mul_comm 2 j, pow_mul]
    exact Real.sqrt_sq (pow_nonneg hs.le j)
  have hTerm (j : Nat) :
      (((s ^ 2) ^ (j + 1)) ^ (1 / 2 : Real) -
        ((s ^ 2) ^ j) ^ (1 / 2 : Real)) / (s ^ 2) ^ (j + 1) =
        (1 / s) ^ (j + 1) - (1 / s) ^ (j + 2) := by
    rw [hRoot (j + 1), hRoot j]
    have hDen : (s ^ 2) ^ (j + 1) = (s ^ j) ^ 2 * s ^ 2 := by
      rw [pow_succ, <- pow_mul, Nat.mul_comm 2 j, pow_mul]
    rw [hDen]
    simp only [div_pow, one_pow, pow_succ]
    field_simp [hs.ne', pow_ne_zero _ hs.ne']
  induction m with
  | zero =>
      simp only [lcmFiniteTailCoefficient, Finset.sum_range_zero, add_zero]
      ring
  | succ m ih =>
      have hStep : lcmFiniteTailCoefficient (s ^ 2) (m + 1) =
          lcmFiniteTailCoefficient (s ^ 2) m +
            (((s ^ 2) ^ (m + 1)) ^ (1 / 2 : Real) -
              ((s ^ 2) ^ m) ^ (1 / 2 : Real)) / (s ^ 2) ^ (m + 1) := by
        simp only [lcmFiniteTailCoefficient, Finset.sum_range_succ]
        ring
      rw [hStep, ih, hTerm]
      ring

theorem tendsto_lcmFiniteTailLowerSum_sq_scaled
    (s c : Real) (hs : 0 < s) (m : Nat) :
    Tendsto (fun N : Nat =>
      lcmFiniteTailLowerSum N m (s ^ 2) (lcmMovingExponent c N) *
        Real.sqrt (N : Real) * Real.log (N : Real)) atTop
      (nhds ((1 + 1 / s - (1 / s) ^ (m + 1)) * Real.exp (-c))) := by
  simpa only [lcmFiniteTailCoefficient_sq s hs m] using
    tendsto_lcmFiniteTailLowerSum_scaled (s ^ 2) c (pow_pos hs 2) m

end PrimeFactorOscillations

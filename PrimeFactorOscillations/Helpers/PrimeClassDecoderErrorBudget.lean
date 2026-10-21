/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.PrimeClassSamplingDiscError

/-!
# Explicit conversion of both decoder allowances to a power bound

The arithmetic allowance retains its exponential class constant. The
complete geometric-tail denominator costs at most two after a >= log 2.
-/

set_option autoImplicit false
set_option Elab.async false

namespace PrimeFactorOscillations.PrimeClassDecoder

theorem samplingPowerBudget_le
    (n r sigma eta S : Real) (M : Nat) (hn : 0 < n) (hr : 0 < r)
    (hpower : (M : Real) * Real.log r <= (1 - sigma - eta) * Real.log n) :
    (n ^ (sigma - 1) * Real.exp (2 * S)) * r ^ M <=
      Real.exp (2 * S) * n ^ (-eta) := by
  have hexponent : (sigma - 1) * Real.log n + (M : Real) * Real.log r <=
      (-eta) * Real.log n := by linarith
  have hbound := mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hexponent)
    (Real.exp_nonneg (2 * S))
  have hid : (n ^ (sigma - 1) * Real.exp (2 * S)) * r ^ M =
      Real.exp (2 * S) * Real.exp ((sigma - 1) * Real.log n + (M : Real) * Real.log r) := by
    rw [Real.rpow_def_of_pos hn, Real.exp_add, Real.exp_nat_mul, Real.exp_log hr]
    rw [mul_comm (Real.log n) (sigma - 1)]
    ring
  rw [hid]
  convert hbound using 1
  rw [Real.rpow_def_of_pos hn]
  rw [mul_comm (Real.log n) (-eta)]

theorem geometricTailBudget_le
    (n a eta : Real) (m : Nat) (hn : 0 < n)
    (ha : Real.log 2 <= a) (hpower : eta * Real.log n <= a * (m : Real)) :
    Real.exp (-a * (m : Real)) / (1 - Real.exp (-a)) <= 2 * n ^ (-eta) := by
  have hhalf : Real.exp (-a) <= (1 / 2 : Real) := by
    have h := Real.exp_le_exp.mpr (neg_le_neg ha)
    have hexact : Real.exp (-Real.log 2) = (1 / 2 : Real) := by
      rw [Real.exp_neg, Real.exp_log (by norm_num : (0 : Real) < 2)]
      norm_num
    rwa [hexact] at h
  have hden : (1 / 2 : Real) <= 1 - Real.exp (-a) := by linarith
  have hnum : Real.exp (-a * (m : Real)) <= n ^ (-eta) := by
    rw [Real.rpow_def_of_pos hn]
    apply Real.exp_le_exp.mpr
    nlinarith
  calc
    _ <= Real.exp (-a * (m : Real)) / (1 / 2 : Real) :=
      div_le_div_of_nonneg_left (Real.exp_nonneg _) (by norm_num) hden
    _ <= n ^ (-eta) / (1 / 2 : Real) :=
      div_le_div_of_nonneg_right hnum (by norm_num)
    _ = _ := by ring

end PrimeFactorOscillations.PrimeClassDecoder

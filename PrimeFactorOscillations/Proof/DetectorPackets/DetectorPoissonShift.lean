/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/

import PrimeFactorOscillations.Helpers.PrimeClockComparison

/-!
# DetectorPoissonShift

Maintained extraction of completed detector/packet proof components.
All original theorem hypotheses and retained proof bodies are preserved.
This module alone asserts no improved zero-free boundary.
-/

set_option autoImplicit false
set_option Elab.async false

namespace DetectorPoissonShift

theorem reference_normalization (P : Real -> Real) (B L z : Real) :
    ((P z * Real.exp (-B * z)) * Real.exp (L * z)) /
        ((P 1 * Real.exp (-B)) * Real.exp L) =
      (P z / P 1) * Real.exp ((L - B) * (z - 1)) := by
  have hn : P z * Real.exp (-B * z) * Real.exp (L * z) =
      P z * Real.exp ((L - B) * z) := by
    rw [mul_assoc, <- Real.exp_add]
    congr 1
    ring
  have hd : P 1 * Real.exp (-B) * Real.exp L =
      P 1 * Real.exp (L - B) := by
    rw [mul_assoc, <- Real.exp_add]
    congr 1
    ring
  rw [hn, hd, mul_div_mul_comm, <- Real.exp_sub]
  congr 1
  congr 1
  ring

theorem poisson_shift_coefficients_nonneg (c : Nat -> Real)
    (hc : forall j, 0 <= c j) (r : Nat) (delta : Real) (hd : 0 <= delta) :
    0 <= Nat.factorialConvolution c r delta := by
  unfold Nat.factorialConvolution
  exact Finset.sum_nonneg (fun j _ =>
    div_nonneg (mul_nonneg (hc j) (pow_nonneg hd _)) (Nat.cast_nonneg _))

theorem exp_one_gt_two : (2 : Real) < Real.exp 1 := by
  have hhalf : (3 / 2 : Real) <= Real.exp (1 / 2 : Real) := by
    have h := Real.add_one_le_exp (1 / 2 : Real)
    linarith
  have hsq : (Real.exp (1 / 2 : Real)) ^ 2 = Real.exp 1 := by
    rw [pow_two, <- Real.exp_add]
    norm_num
  nlinarith [Real.exp_pos (1 / 2 : Real)]

theorem normalized_compensated_factor_at_zero_gt_one :
    1 <
      (((1 + (0 : Real)) * Real.exp (-(1 : Real) * 0)) * Real.exp (0 * 0)) /
        (((1 + (1 : Real)) * Real.exp (-(1 : Real))) * Real.exp 0) := by
  rw [reference_normalization (fun z : Real => 1 + z) 1 0 0]
  norm_num
  nlinarith [exp_one_gt_two]

end DetectorPoissonShift

/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/

import Mathlib.Tactic.FieldSimp
import PrimeFactorOscillations.Assembly.DetectorPackets.EisensteinCarrierHighKernel

/-!
# EisensteinHighKernelScales

Maintained extraction of completed detector/packet proof components.
All original theorem hypotheses and retained proof bodies are preserved.
This module alone asserts no improved zero-free boundary.
-/

set_option autoImplicit false
set_option Elab.async false

/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/


noncomputable section
namespace PrimeFactorOscillations.EisensteinHighKernelScales

-- D=T^2,Y=T^3,M=T^8,N=T^5,K=T^2. The column mass is O(T^5).
theorem three_quarters_high_cost (T : Real) (hT : 1 <= T) :
    (T ^ 8 + Real.sqrt (T ^ 8 / T ^ 2) * T ^ 5) * T ^ 5 =
      2 * T ^ 13 := by
  have ht : Not (T = 0) := by linarith
  have hRatio : T ^ 8 / T ^ 2 = (T ^ 3) ^ 2 := by
    field_simp
    <;> ring
  rw [hRatio, Real.sqrt_sq_eq_abs, abs_of_nonneg (by positivity : 0 <= T ^ 3)]
  ring

-- D=T^2,Y=T^4,M=T^8,N=T^6,K=T^4. The column mass is O(T^6).
theorem half_high_cost (T : Real) (hT : 1 <= T) :
    (T ^ 8 + Real.sqrt (T ^ 8 / T ^ 4) * T ^ 6) * T ^ 6 =
      2 * T ^ 14 := by
  have ht : Not (T = 0) := by linarith
  have hRatio : T ^ 8 / T ^ 4 = (T ^ 2) ^ 2 := by
    field_simp
    <;> ring
  rw [hRatio, Real.sqrt_sq_eq_abs, abs_of_nonneg (by positivity : 0 <= T ^ 2)]
  ring

end PrimeFactorOscillations.EisensteinHighKernelScales

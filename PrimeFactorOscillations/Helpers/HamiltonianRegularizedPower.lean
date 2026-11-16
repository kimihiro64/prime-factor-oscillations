/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-! # Regularized real powers with their complete signed second derivative -/

set_option autoImplicit false
set_option Elab.async false

noncomputable section

namespace PrimeFactorOscillations

theorem hamiltonian_regularized_power_hasDerivAt
    (g g1 : Real -> Real) (t e q : Real)
    (hg : HasDerivAt g (g1 t) t) (hPos : 0 < g t + e) :
    HasDerivAt (fun s : Real => (g s + e) ^ q)
      (g1 t * q * (g t + e) ^ (q - 1)) t := by
  exact (hg.add_const e).rpow_const (Or.inl (ne_of_gt hPos))

theorem hamiltonian_regularized_power_second_hasDerivAt
    (g g1 g2 : Real -> Real) (t e q : Real)
    (hg : HasDerivAt g (g1 t) t) (hg1 : HasDerivAt g1 (g2 t) t)
    (hPos : 0 < g t + e) :
    HasDerivAt (fun s : Real => g1 s * q * (g s + e) ^ (q - 1))
      (g2 t * q * (g t + e) ^ (q - 1) +
        (g1 t) ^ 2 * q * (q - 1) * (g t + e) ^ (q - 2)) t := by
  have hPower := (hg.add_const e).rpow_const
    (p := q - 1) (Or.inl (ne_of_gt hPos))
  have h := (hg1.mul_const q).mul hPower
  have hExp : q - 1 - 1 = q - 2 := by ring
  rw [hExp] at h
  have hId :
      g2 t * q * (g t + e) ^ (q - 1) +
        g1 t * q * (g1 t * (q - 1) * (g t + e) ^ (q - 2)) =
      g2 t * q * (g t + e) ^ (q - 1) +
        (g1 t) ^ 2 * q * (q - 1) * (g t + e) ^ (q - 2) := by ring
  rw [hId] at h
  exact h

theorem hamiltonian_regularized_power_curvature
    (g h u v K q : Real) (hg : 0 <= g) (hgh : g <= h)
    (hh : 0 < h) (hK : 0 <= K) (hq0 : 0 <= q) (hq1 : q <= 1)
    (hu : u <= K * g ^ (1 - q)) :
    u * q * h ^ (q - 1) + v ^ 2 * q * (q - 1) * h ^ (q - 2) <= q * K := by
  have hMass : g ^ (1 - q) <= h ^ (1 - q) :=
    Real.rpow_le_rpow hg hgh (sub_nonneg.mpr hq1)
  have hUpper : u <= K * h ^ (1 - q) :=
    hu.trans (mul_le_mul_of_nonneg_left hMass hK)
  have hFac : 0 <= q * h ^ (q - 1) :=
    mul_nonneg hq0 (Real.rpow_nonneg hh.le _)
  have hMain := mul_le_mul_of_nonneg_right hUpper hFac
  have hCancel : K * h ^ (1 - q) * (q * h ^ (q - 1)) = q * K := by
    calc
      _ = q * K * (h ^ (1 - q) * h ^ (q - 1)) := by ring
      _ = q * K := by
        rw [<- Real.rpow_add hh, sub_add_sub_cancel, sub_self, Real.rpow_zero, mul_one]
  rw [hCancel] at hMain
  have hNeg : v ^ 2 * q * (q - 1) * h ^ (q - 2) <= 0 :=
    mul_nonpos_of_nonpos_of_nonneg
      (mul_nonpos_of_nonneg_of_nonpos (mul_nonneg (sq_nonneg v) hq0)
        (sub_nonpos.mpr hq1)) (Real.rpow_nonneg hh.le _)
  nlinarith only [hMain, hNeg]

end PrimeFactorOscillations

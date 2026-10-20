/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/

import PrimeFactorOscillations.Proof.DetectorPackets.UniformCarrierPairedProbe

/-!
# QuarticPowerfulPacket

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

/-!
# Compression for powerful quartic frequency packets

Zero-extended quartic values keep their zeros in the compression.
The scalar budget combines the quadratic and fourth-power-free quartic
mean estimates. Those analytic sieve estimates are external inputs,
not asserted as compiled theorems by this file.
-/


noncomputable section
namespace PrimeFactorOscillations.QuarticPowerfulPacket

def QuarticValue (z : Complex) : Prop :=
  z = 0 \/ z = 1 \/ z = -1 \/ z = Complex.I \/ z = -Complex.I

theorem quartic_value_of_power (z : Complex) (hz : z = 0 \/ z ^ 4 = 1) :
    QuarticValue z := by
  rcases hz with hz | hz
  . exact Or.inl hz
  . have hp : (z ^ 2 - 1) * (z ^ 2 + 1) = 0 := by
      calc
        (z ^ 2 - 1) * (z ^ 2 + 1) = z ^ 4 - 1 := by ring
        _ = 0 := by rw [hz]; ring
    rcases mul_eq_zero.mp hp with hm | hp
    . have hf : (z - 1) * (z + 1) = 0 := by
        calc
          (z - 1) * (z + 1) = z ^ 2 - 1 := by ring
          _ = 0 := hm
      rcases mul_eq_zero.mp hf with h | h
      . have he : z = 1 := sub_eq_zero.mp h
        rw [he]
        simp [QuarticValue]
      . have he : z = -1 := eq_neg_of_add_eq_zero_left h
        rw [he]
        simp [QuarticValue]
    . have hf : (z - Complex.I) * (z + Complex.I) = 0 := by
        calc
          (z - Complex.I) * (z + Complex.I) = z ^ 2 - Complex.I ^ 2 := by ring
          _ = z ^ 2 + 1 := by rw [Complex.I_sq]; ring
          _ = 0 := hp
      rcases mul_eq_zero.mp hf with h | h
      . have he : z = Complex.I := sub_eq_zero.mp h
        rw [he]
        simp [QuarticValue]
      . have he : z = -Complex.I := eq_neg_of_add_eq_zero_left h
        rw [he]
        simp [QuarticValue]

theorem square_fixed (z : Complex) (hz : QuarticValue z) :
    (starRingEnd Complex) (z ^ 2) = z ^ 2 := by
  rcases hz with h | h | h | h | h <;> subst z <;> norm_num [Complex.I_sq]

theorem cube_star (z : Complex) (hz : QuarticValue z) :
    z ^ 3 = (starRingEnd Complex) z := by
  rcases hz with h | h | h | h | h <;> subst z <;> norm_num [pow_succ, Complex.I_sq]

theorem core_compression (x y : Complex) (hx : QuarticValue x) (hy : QuarticValue y) :
    x ^ 2 * y ^ 3 = (starRingEnd Complex) (x ^ 2 * y) := by
  rw [map_mul, square_fixed x hx, <- cube_star y hy]

theorem balanced_budget (E A B C : Real) (hA : 0 <= A) (hB : 0 <= B)
    (hquad : E <= A * C) (hquart : C * (E - A) <= B) :
    E <= A + Real.sqrt (A * B) := by
  by_cases hE : E <= A
  . exact hE.trans (le_add_of_nonneg_right (Real.sqrt_nonneg _))
  . have hpos : 0 < E - A := sub_pos.mpr (lt_of_not_ge hE)
    have hsmall : E - A <= A * C := by linarith
    have hsquare : (E - A) ^ 2 <= A * B := by
      calc
        (E - A) ^ 2 <= (A * C) * (E - A) := by
          nlinarith [mul_le_mul_of_nonneg_right hsmall hpos.le]
        _ = A * (C * (E - A)) := by ring
        _ <= A * B := mul_le_mul_of_nonneg_left hquart hA
    have hroot := Real.sq_sqrt (mul_nonneg hA hB)
    have hnonneg := Real.sqrt_nonneg (A * B)
    nlinarith

theorem half_power_budget (E D C : Real) (hD : 1 <= D)
    (hquad : E <= D ^ 8 * C) (hquart : C * (E - D ^ 8) <= D ^ 9) :
    E <= 2 * D ^ 8 * Real.sqrt D := by
  have hDzero : 0 <= D := le_trans zero_le_one hD
  have hbase := balanced_budget E (D ^ 8) (D ^ 9) C
    (pow_nonneg hDzero _) (pow_nonneg hDzero _) hquad hquart
  have hroot : Real.sqrt (D ^ 8 * D ^ 9) = D ^ 8 * Real.sqrt D := by
    have hsq : (D ^ 8 * Real.sqrt D) ^ 2 = D ^ 8 * D ^ 9 := by
      rw [mul_pow, Real.sq_sqrt hDzero]
      ring
    have hleft := Real.sq_sqrt (mul_nonneg (pow_nonneg hDzero 8) (pow_nonneg hDzero 9))
    have hright : 0 <= D ^ 8 * Real.sqrt D :=
      mul_nonneg (pow_nonneg hDzero _) (Real.sqrt_nonneg _)
    have hleftnon := Real.sqrt_nonneg (D ^ 8 * D ^ 9)
    nlinarith
  have hsqrt : 1 <= Real.sqrt D := by
    have hs := Real.sq_sqrt hDzero
    have hn := Real.sqrt_nonneg D
    nlinarith
  rw [hroot] at hbase
  have hpower := mul_le_mul_of_nonneg_left hsqrt (pow_nonneg hDzero 8)
  nlinarith

end PrimeFactorOscillations.QuarticPowerfulPacket

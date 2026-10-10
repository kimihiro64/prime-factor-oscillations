/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination

/-!
# Exact energy and recovery cost of a rank-one complex block

For the block [[a,b],[c,conj(a)]] with normSq(a)=b*c, the complete
energy identity retains its complementary squares. It gives a sharp
upper energy factor (b+c)^2 and an attained direction, so recovering
that direction requires the reciprocal factor. At the critical quintic
parameter b=z, c=z^2, an upper norm bound therefore does not provide
a uniform inverse bound. No global metaplectic identification is asserted.
-/

set_option autoImplicit false
set_option Elab.async false

namespace Complex

/-- The two coupled rows of a rank-one reflection block. -/
noncomputable def reflectionPair (a : Complex) (b c : Real) (x y : Complex) :
    Prod Complex Complex :=
  (a * x + (b : Complex) * y, (c : Complex) * x + star a * y)

noncomputable def pairEnergy (v : Prod Complex Complex) : Real :=
  normSq v.1 + normSq v.2

/-- The complementary square is retained exactly before taking any estimate. -/
theorem reflectionPair_energy_identity (a : Complex) (b c : Real)
    (ha : normSq a = b * c) (x y : Complex) :
    pairEnergy (reflectionPair a b c x y) +
      normSq ((b : Complex) * x - star a * y) +
      normSq (a * x - (c : Complex) * y) =
      (b + c) ^ 2 * (normSq x + normSq y) := by
  simp only [normSq_apply] at ha
  simp [pairEnergy, reflectionPair, normSq_apply, mul_re, mul_im]
  linear_combination 2 * (x.re ^ 2 + x.im ^ 2 + y.re ^ 2 + y.im ^ 2) * ha

theorem reflectionPair_energy_le (a : Complex) (b c : Real)
    (ha : normSq a = b * c) (x y : Complex) :
    pairEnergy (reflectionPair a b c x y) <=
      (b + c) ^ 2 * (normSq x + normSq y) := by
  have h := reflectionPair_energy_identity a b c ha x y
  nlinarith [normSq_nonneg ((b : Complex) * x - star a * y),
    normSq_nonneg (a * x - (c : Complex) * y)]

/-- A vector attaining the complete block energy bound. -/
theorem reflectionPair_energy_witness (a : Complex) (b c : Real)
    (ha : normSq a = b * c) :
    pairEnergy (reflectionPair a b c (star a) (b : Complex)) =
      (b + c) ^ 2 * (normSq (star a) + normSq (b : Complex)) := by
  have h := reflectionPair_energy_identity a b c ha (star a) (b : Complex)
  have hfirst : (b : Complex) * star a - star a * (b : Complex) = 0 := by ring
  have hsecond : a * star a - (c : Complex) * (b : Complex) = 0 := by
    apply Complex.ext
    . simp [normSq_apply] at ha
      simp [mul_re]
      nlinarith
    . simp [mul_im]
      ring
  simpa only [hfirst, hsecond, normSq_zero, add_zero] using h

/-- Even recovery on this single attained direction needs this inverse cost. -/
theorem reflectionPair_recovery_necessary (a : Complex) (b c C : Real)
    (ha : normSq a = b * c) (hb : 0 < b)
    (hC : normSq (star a) + normSq (b : Complex) <=
      C * pairEnergy (reflectionPair a b c (star a) (b : Complex))) :
    1 <= C * (b + c) ^ 2 := by
  have hpos : 0 < normSq (star a) + normSq (b : Complex) := by
    have hn := normSq_nonneg (star a)
    simp only [normSq_apply, ofReal_re, ofReal_im, mul_zero, add_zero]
    nlinarith [normSq_nonneg (star a), sq_pos_of_pos hb]
  rw [reflectionPair_energy_witness a b c ha] at hC
  nlinarith

/-- Exact necessary recovery factor for the weak quintic channel. -/
theorem quintic_reflectionPair_recovery_necessary (a : Complex) (z C : Real)
    (ha : normSq a = z ^ 3) (hz : 0 < z)
    (hC : normSq (star a) + normSq (z : Complex) <=
      C * pairEnergy (reflectionPair a z (z ^ 2) (star a) (z : Complex))) :
    1 <= C * (z + z ^ 2) ^ 2 := by
  apply reflectionPair_recovery_necessary a z (z ^ 2) C _ hz hC
  rw [ha]
  ring

end Complex

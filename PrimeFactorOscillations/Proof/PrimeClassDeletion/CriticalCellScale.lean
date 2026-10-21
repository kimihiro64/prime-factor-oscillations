/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.Linarith

/-!
# Cell-scale arithmetic for full Euler remainders

The choice theta = 1 - 1 / k makes the full order-k remainder
exponent exactly -sigma. For k >= 4 its cell width stays above
the unconditional two-thirds prime-mesh scale, and both retained
dyadic remainder exponents are negative on every sigma > 0.
No Euler continuation or prime-counting estimate is proved here.
-/

set_option autoImplicit false
set_option Elab.async false

namespace PrimeFactorOscillations.PrimeClassDeletion

noncomputable def criticalCellTheta (k : Real) : Real := 1 - 1 / k

theorem criticalCellTheta_exponent (k sigma : Real)
    (hk : Not (k = 0)) :
    1 - sigma - k * (1 - criticalCellTheta k) = -sigma := by
  have hunit : k * (1 / k) = 1 := by
    rw [<- mul_div_assoc, mul_one, div_self hk]
  unfold criticalCellTheta
  rw [sub_sub_cancel, hunit]
  linarith

theorem criticalCellTheta_range (k : Real) (hk : 4 <= k) :
    0 < 1 / k /\ 1 / k <= 1 / 4 /\
      2 / 3 < criticalCellTheta k /\ criticalCellTheta k < 1 := by
  have hkpos : 0 < k := by linarith
  have hkzero : Not (k = 0) := ne_of_gt hkpos
  have hinv : 0 < 1 / k := one_div_pos.mpr hkpos
  have hunit : k * (1 / k) = 1 := by
    rw [<- mul_div_assoc, mul_one, div_self hkzero]
  have hprod : 0 <= (k - 4) * (1 / k) :=
    mul_nonneg (by linarith) (le_of_lt hinv)
  have hbound : 1 / k <= 1 / 4 := by nlinarith
  refine And.intro hinv (And.intro hbound ?_)
  unfold criticalCellTheta
  constructor <;> linarith

theorem criticalCellTheta_remainder_negative (k sigma : Real)
    (hk : 4 <= k) (hsigma : 0 < sigma) :
    1 - sigma - k * (1 - criticalCellTheta k) < 0 /\
      -3 + 1 / k - sigma < 0 := by
  have hkpos : 0 < k := by linarith
  have hmain := criticalCellTheta_exponent k sigma (ne_of_gt hkpos)
  have hround := (criticalCellTheta_range k hk).2.1
  constructor <;> linarith

end PrimeFactorOscillations.PrimeClassDeletion

/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import Mathlib.Algebra.Order.Floor.Semiring
import PrimeFactorOscillations.Helpers.HamiltonianLogWeightComparison

/-! # Complete finite transfer from prime logarithms to constant edge weights

Every output is retained in the finite sum. The small part is charged
to its actual integer count and the large part to the full Chebyshev
prime mass. The threshold and all denominator signs are explicit.
-/

set_option autoImplicit false
set_option Elab.async false

open scoped Matrix.Norms.L2Operator

noncomputable section

namespace PrimeFactorOscillations.LPF

def hamiltonianPrimeLogWeight (n t : Nat) : Real :=
  if Nat.Prime t then abs (Real.log (n : Real) - Real.log (t : Real)) else 0

def hamiltonianPrimeLogTransferError (n : Nat) : Real :=
  (1 + 4 * Real.log 4 * (2 * Real.log (Real.log (n : Real)) + Real.log 2)) /
    Real.log (n : Real)

theorem hamiltonian_prime_log_weight_nonnegative (n t : Nat) :
    0 <= hamiltonianPrimeLogWeight n t := by
  unfold hamiltonianPrimeLogWeight
  split
  next => exact abs_nonneg _
  next => exact le_refl _

theorem hamiltonian_prime_log_transfer_sum (n : Nat)
    (hn : 1 <= n) (hL : 64 <= Real.log (n : Real)) :
    (Finset.Ioc 0 (2 * n)).sum (hamiltonianPrimeLogWeight n) / (n : Real) <=
      hamiltonianPrimeLogTransferError n := by
  let L := Real.log (n : Real)
  let A := 2 * Real.log L + Real.log 2
  let c := 2 * A / L
  let K := Nat.floor ((n : Real) / L ^ 2)
  have hnOne : (1 : Real) <= (n : Real) := by exact_mod_cast hn
  have hnPos : 0 < (n : Real) := lt_of_lt_of_le zero_lt_one hnOne
  have hLOne : 1 <= L := by dsimp only [L]; linarith only [hL]
  have hLPos : 0 < L := lt_of_lt_of_le zero_lt_one hLOne
  have hL0 : 0 <= L := hLPos.le
  have hLL : 0 <= Real.log L := Real.log_nonneg hLOne
  have hTwo : 0 <= Real.log (2 : Real) := Real.log_nonneg (by norm_num)
  have hA : 0 <= A := by dsimp only [A]; positivity
  have hc : 0 <= c := div_nonneg (mul_nonneg (by norm_num) hA) hL0
  have hCutPos : 0 < (n : Real) / L ^ 2 := div_pos hnPos (sq_pos_of_pos hLPos)
  have hK : (K : Real) <= (n : Real) / L ^ 2 := Nat.floor_le hCutPos.le
  have hSquare : 1 <= L ^ 2 := by nlinarith only [hLOne]
  have hCutUpper : (n : Real) / L ^ 2 <= (n : Real) := by
    simpa only [div_one] using
      div_le_div_of_nonneg_left hnPos.le zero_lt_one hSquare
  have hSmall (t : Nat) (ht : Membership.mem (Finset.Ioc 0 (2 * n)) t) (htK : t <= K) :
      hamiltonianPrimeLogWeight n t <= L := by
    by_cases hp : Nat.Prime t
    . rw [hamiltonianPrimeLogWeight, if_pos hp]
      have htOne : (1 : Real) <= (t : Real) := by
        exact_mod_cast (Nat.le_trans (by norm_num : 1 <= 2) hp.two_le)
      have htUpper : (t : Real) <= (n : Real) :=
        (Nat.cast_le.mpr htK).trans (hK.trans hCutUpper)
      exact hamiltonian_log_weight_small (n : Real) (t : Real) hnOne htOne htUpper
    . simpa only [hamiltonianPrimeLogWeight, if_neg hp] using hL0
  have hLarge (t : Nat) (ht : Membership.mem (Finset.Ioc 0 (2 * n)) t) (htK : K < t) :
      hamiltonianPrimeLogWeight n t <= c * hamiltonianPrimeValue t := by
    by_cases hp : Nat.Prime t
    . rw [hamiltonianPrimeLogWeight, if_pos hp, hamiltonianPrimeValue, if_pos hp]
      have htPos : 0 < (t : Real) := by exact_mod_cast hp.pos
      have hInteger : (K : Real) + 1 <= (t : Real) := by
        exact_mod_cast Nat.succ_le_of_lt htK
      have htLower : (n : Real) / L ^ 2 <= (t : Real) :=
        (Nat.lt_floor_add_one ((n : Real) / L ^ 2)).le.trans hInteger
      have htUpper : (t : Real) <= 2 * (n : Real) := by
        exact_mod_cast (Finset.mem_Ioc.mp ht).2
      exact hamiltonian_log_weight_large (n : Real) (t : Real) hnPos hLOne
        (hamiltonian_four_log_le_self L hL) htPos htLower htUpper
    . simp only [hamiltonianPrimeLogWeight, hamiltonianPrimeValue, if_neg hp, mul_zero, le_refl]
  have hSum := hamiltonian_finite_prime_weight_split (2 * n) K
    (hamiltonianPrimeLogWeight n) L c hL0 hc hSmall hLarge
  have hLow : (K : Real) * L <= (n : Real) / L := by
    have h := mul_le_mul_of_nonneg_right hK hL0
    have hClear : ((n : Real) / L ^ 2) * L = (n : Real) / L := by
      field_simp [ne_of_gt hLPos]
    exact h.trans_eq hClear
  have hTheta : Chebyshev.theta ((2 * n : Nat) : Real) <=
      Real.log 4 * (2 * (n : Real)) := by
    simpa only [Nat.cast_mul, Nat.cast_ofNat] using
      Chebyshev.theta_le_log4_mul_x (by positivity : 0 <= ((2 * n : Nat) : Real))
  have hNumerator : (Finset.Ioc 0 (2 * n)).sum (hamiltonianPrimeLogWeight n) <=
      (n : Real) / L + c * (Real.log 4 * (2 * (n : Real))) :=
    hSum.trans (add_le_add hLow (mul_le_mul_of_nonneg_left hTheta hc))
  have hFormula : ((n : Real) / L + c * (Real.log 4 * (2 * (n : Real)))) / (n : Real) =
      (1 + 4 * Real.log 4 * A) / L := by
    dsimp only [c]
    field_simp [ne_of_gt hnPos, ne_of_gt hLPos] <;> ring
  change _ <= (1 + 4 * Real.log 4 * A) / L
  exact (div_le_div_of_nonneg_right hNumerator hnPos.le).trans_eq hFormula

end PrimeFactorOscillations.LPF

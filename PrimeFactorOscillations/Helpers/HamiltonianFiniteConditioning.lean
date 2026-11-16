/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.HamiltonianColumnPolynomialTail

/-! # Exact finite-event conditioning with all probability costs

The original full-space tail and event cardinality are kept until
the denominator is proved positive. Polynomial event losses are
absorbed by the three retained powers of the dimension.
-/

set_option autoImplicit false
set_option Elab.async false

noncomputable section

namespace PrimeFactorOscillations

theorem hamiltonian_finite_conditioned_count
    {Omega : Type*} [Fintype Omega] [DecidableEq Omega] [Nonempty Omega]
    (B T : Finset Omega) (P K : Real) (hP : 0 <= P)
    (hTail : (B.card : Real) / (Fintype.card Omega : Real) <= P)
    (hEvent : (Fintype.card Omega : Real) <= K * (T.card : Real)) :
    ((Inter.inter B T).card : Real) / (T.card : Real) <= K * P := by
  have hC : (0 : Real) < Fintype.card Omega := Nat.cast_pos.mpr Fintype.card_pos
  have hT0 : (0 : Real) <= T.card := Nat.cast_nonneg _
  have hTne : Not ((T.card : Real) = 0) := by
    intro h
    rw [h, mul_zero] at hEvent
    linarith only [hEvent, hC]
  have hT : (0 : Real) < T.card := lt_of_le_of_ne hT0 (Ne.symm hTne)
  have hB : (B.card : Real) <= P * (Fintype.card Omega : Real) := by
    have h := mul_le_mul_of_nonneg_right hTail hC.le
    convert h using 1 <;> field_simp [ne_of_gt hC]
  have hInter : ((Inter.inter B T).card : Real) <= (B.card : Real) :=
    Nat.cast_le.mpr (Finset.card_le_card Finset.inter_subset_left)
  have hProduct := (hInter.trans hB).trans (mul_le_mul_of_nonneg_left hEvent hP)
  have hBound : ((Inter.inter B T).card : Real) <= (K * P) * (T.card : Real) :=
    hProduct.trans_eq (by ring)
  have h := div_le_div_of_nonneg_right hBound hT.le
  convert h using 1 <;> field_simp [ne_of_gt hT]

theorem hamiltonian_polynomial_conditioning_budgets
    (n : Real) (hn : 2 <= n) :
    And (n + 1 <= n ^ 3) (4 * (n - 1) <= n ^ 3) := by
  have hn0 : 0 <= n := by linarith only [hn]
  have hSquare : 4 <= n ^ 2 := by
    nlinarith only [hn, sq_nonneg (n - 2)]
  have hCubic := mul_le_mul_of_nonneg_right hSquare hn0
  exact And.intro (by nlinarith only [hCubic, hn]) (by nlinarith only [hCubic])

theorem hamiltonian_conditioning_power_budget
    (n A K : Real) (hn : 2 <= n) (hK : K <= n ^ 3) :
    K * n ^ (-(A + 3)) <= n ^ (-A) := by
  have hnPos : 0 < n := by linarith only [hn]
  have hP : 0 <= n ^ (-(A + 3)) := Real.rpow_nonneg hnPos.le _
  have hIdentity : n ^ 3 * n ^ (-(A + 3)) = n ^ (-A) := by
    rw [<- Real.rpow_natCast, <- Real.rpow_add hnPos]
    congr 1
    ring
  exact (mul_le_mul_of_nonneg_right hK hP).trans_eq hIdentity

end PrimeFactorOscillations

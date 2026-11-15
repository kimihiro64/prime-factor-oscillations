/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.HamiltonianRowCapLogBudget

/-! # The global row-cap bound in every order, including empty minors

The zero- and one-row cases are evaluated exactly. The same explicit
exponential bound therefore applies to every complementary minor,
including the two exceptional largest deleted-support ranks.
-/

set_option autoImplicit false
set_option Elab.async false

noncomputable section

namespace PrimeFactorOscillations

theorem hamiltonian_row_cap_permanent_all_orders (n : Nat)
    (A : Matrix (Fin n) (Fin n) Real) (a X : Real)
    (ha : 1 <= a) (hX1 : 1 <= X) (hX : (n : Real) <= X)
    (hNonneg : forall i j, 0 <= A i j)
    (hRow : forall i, Finset.univ.sum (fun j => A i j) <= 1)
    (hCap : forall i j, A i j <= a / X) :
    Finset.univ.sum (fun sigma : Equiv.Perm (Fin n) =>
      Finset.univ.prod (fun i => A i (sigma i))) <=
        Real.exp (-(n : Real) + 16 * a * Real.log (2 * X)) := by
  have ha0 : 0 <= a := le_trans (by norm_num) ha
  have hLogTwo : (1 / 2 : Real) <= Real.log 2 := by
    have h := Real.one_sub_inv_le_log_of_pos (x := 2) (by norm_num)
    norm_num at h
    exact h
  have hHalf : (1 / 2 : Real) <= Real.log (2 * X) :=
    le_trans hLogTwo (Real.log_le_log (by norm_num) (by linarith only [hX1]))
  have hScale := mul_le_mul_of_nonneg_left hHalf ha0
  have hOne : 0 <= -(1 : Real) + 16 * a * Real.log (2 * X) := by
    nlinarith only [hScale, ha]
  have hZero : 0 <= 16 * a * Real.log (2 * X) := by
    nlinarith only [hScale, ha]
  cases n with
  | zero =>
    change finitePermutationSum A.transpose <= _
    rw [finitePermutationSum_fin_zero]
    simpa only [Nat.cast_zero, neg_zero, zero_add, Real.exp_zero] using Real.exp_le_exp.mpr hZero
  | succ n =>
    cases n with
    | zero =>
      have hFin : (Finset.univ : Finset (Fin 1)) = {0} := by
        ext i
        simp only [Finset.mem_univ, Finset.mem_singleton, true_iff]
        exact Subsingleton.elim i 0
      have hProduct (sigma : Equiv.Perm (Fin 1)) :
          Finset.univ.prod (fun i => A i (sigma i)) = A 0 0 := by
        rw [hFin, Finset.prod_singleton]
        rw [show sigma 0 = 0 from Subsingleton.elim _ _]
      have hMass : Finset.univ.sum (fun sigma : Equiv.Perm (Fin 1) =>
          Finset.univ.prod (fun i => A i (sigma i))) = A 0 0 := by
        simp only [hProduct, Finset.sum_const, Finset.card_univ, Fintype.card_perm,
          Fintype.card_fin, Nat.factorial_one, one_smul]
      have hSmall : A 0 0 <= 1 := by
        have h := hRow 0
        rw [hFin, Finset.sum_singleton] at h
        exact h
      have hExp : 1 <= Real.exp (-(1 : Real) + 16 * a * Real.log (2 * X)) := by
        simpa only [Real.exp_zero] using Real.exp_le_exp.mpr hOne
      rw [hMass]
      convert le_trans hSmall hExp using 1 <;> norm_num
    | succ n =>
      have hOrder : (n + 2 : Real) <= X := by
        norm_num only [Nat.cast_add, Nat.cast_one] at hX
        linarith only [hX]
      have h := hamiltonian_row_cap_permanent_upper n A a X ha hOrder hNonneg hRow hCap
      convert h using 1 <;> norm_num <;> ring

end PrimeFactorOscillations

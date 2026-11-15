/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import Mathlib.NumberTheory.Harmonic.Bounds
import PrimeFactorOscillations.Helpers.HamiltonianRowCapPermanent
import PrimeFactorOscillations.Helpers.LPFSievePrimeCutoff

/-! # The explicit exponential row-cap budget

The actual row-order logarithm is bounded using the already proved
Stirling sum estimate and the harmonic bound. Every denominator is
positive on the stated domain. No asymptotic permanent estimate is
assumed by the global complementary-minor upper bound.
-/

set_option autoImplicit false
set_option Elab.async false

noncomputable section

namespace PrimeFactorOscillations

theorem hamiltonian_fin_shift_sum (m : Nat) (f : Nat -> Real) :
    Finset.univ.sum (fun i : Fin m => f (i.val + 1)) =
      (Finset.Icc 1 m).sum f := by
  refine Finset.sum_bij (fun (i : Fin m) _ => i.val + 1) ?_ ?_ ?_ ?_
  next =>
    intro i hi
    exact Finset.mem_Icc.mpr (And.intro
      (Nat.succ_le_succ (Nat.zero_le i.val)) (Nat.succ_le_of_lt i.isLt))
  next =>
    intro i hi j hj hEq
    exact Fin.ext (Nat.add_right_cancel hEq)
  next =>
    intro k hk
    have hBounds := Finset.mem_Icc.mp hk
    have hIndex : k - 1 < m := by omega
    refine Exists.intro (Fin.mk (k - 1) hIndex) (Exists.intro (Finset.mem_univ _) ?_)
    simp only [Fin.val_mk]
    omega
  next =>
    intro i hi
    rfl

theorem hamiltonian_row_cap_log_reverse (n : Nat) (c : Real) :
    hamiltonianRowCapLogBound n c =
      Finset.univ.sum (fun k : Fin (n + 2) =>
        Real.log (c + (k.val : Real) / (n + 1 : Real))) := by
  have h := Equiv.sum_comp (Fin.revPerm : Equiv.Perm (Fin (n + 2)))
    (fun k : Fin (n + 2) => Real.log (c + (k.val : Real) / (n + 1 : Real)))
  have hIndex (k : Fin (n + 2)) : n + 2 - (k.val + 1) = n + 1 - k.val := by omega
  simpa only [hamiltonianRowCapLogBound, Fin.revPerm_apply, Fin.val_rev, hIndex] using h

theorem hamiltonian_row_cap_log_stirling (n : Nat) (c : Real) (hc : 0 < c) :
    hamiltonianRowCapLogBound n c <=
      Real.log c - (n + 1 : Real) + Real.log (n + 1 : Real) + 1 +
        c * (n + 1 : Real) * (1 + Real.log (n + 1 : Real)) := by
  let m : Real := n + 1
  have hm : 0 < m := by dsimp only [m]; exact_mod_cast Nat.succ_pos n
  have hHead : hamiltonianRowCapLogBound n c =
      Real.log c + Finset.univ.sum (fun k : Fin (n + 1) =>
        Real.log (c + ((k.val : Real) + 1) / m)) := by
    rw [hamiltonian_row_cap_log_reverse, Fin.sum_univ_succ]
    simp only [Fin.val_zero, Nat.cast_zero, zero_div, add_zero,
      Fin.val_succ, Nat.cast_add, Nat.cast_one, m]
  have hTerm (k : Fin (n + 1)) :
      Real.log (c + ((k.val : Real) + 1) / m) <=
        Real.log ((k.val : Real) + 1) - Real.log m +
          c * m * (1 / ((k.val : Real) + 1)) := by
    let b : Real := (k.val : Real) + 1
    have hK : (0 : Real) <= (k.val : Real) := Nat.cast_nonneg k.val
    have hb : 0 < b := by dsimp only [b]; linarith only [hK]
    have hRatio : 0 < b / m := div_pos hb hm
    have hExtra : 0 < 1 + c * m / b :=
      add_pos_of_pos_of_nonneg (by norm_num) (le_of_lt (div_pos (mul_pos hc hm) hb))
    have hFactor : c + b / m = (b / m) * (1 + c * m / b) := by
      field_simp [ne_of_gt hb, ne_of_gt hm] <;> ring
    change Real.log (c + b / m) <= Real.log b - Real.log m + c * m * (1 / b)
    rw [hFactor, Real.log_mul (ne_of_gt hRatio) (ne_of_gt hExtra),
      Real.log_div (ne_of_gt hb) (ne_of_gt hm)]
    have h := Real.log_le_sub_one_of_pos hExtra
    have hDiv : c * m / b = c * m * (1 / b) := by ring
    rw [hDiv] at h
    rw [hDiv]
    linarith only [h]
  have hLogShift := hamiltonian_fin_shift_sum (n + 1) (fun k => Real.log (k : Real))
  have hInvShift := hamiltonian_fin_shift_sum (n + 1) (fun k => (1 : Real) / (k : Real))
  simp only [Nat.cast_add, Nat.cast_one] at hLogShift hInvShift
  have hSummands : Finset.univ.sum (fun k : Fin (n + 1) =>
      Real.log ((k.val : Real) + 1) - Real.log m +
        c * m * (1 / ((k.val : Real) + 1))) =
      (Finset.Icc 1 (n + 1)).sum (fun k => Real.log (k : Real)) - m * Real.log m +
        c * m * (Finset.Icc 1 (n + 1)).sum (fun k => (1 : Real) / (k : Real)) := by
    rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, <- Finset.mul_sum,
      hLogShift, hInvShift]
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
      Nat.cast_add, Nat.cast_one, m]
  have hIntervals : Finset.Icc 1 (n + 1) = Finset.Ioc 0 (n + 1) := by
    ext k
    simp only [Finset.mem_Icc, Finset.mem_Ioc]
    omega
  have hStirling := LPF.log_factorial_stirling_upper (n + 1) (by omega)
  rw [<- hIntervals] at hStirling
  simp only [Nat.cast_add, Nat.cast_one] at hStirling
  have hHarmonic : (Finset.Icc 1 (n + 1)).sum (fun k => (1 : Real) / (k : Real)) <=
      1 + Real.log m := by
    simpa only [harmonic_eq_sum_Icc, Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast,
      one_div, Nat.cast_add, Nat.cast_one, m] using harmonic_le_one_add_log (n + 1)
  have hHarmonicScaled := mul_le_mul_of_nonneg_left hHarmonic
    (mul_nonneg (le_of_lt hc) (le_of_lt hm))
  have hSum := Finset.sum_le_sum (fun k (_ : Membership.mem Finset.univ k) => hTerm k)
  rw [hSummands] at hSum
  rw [hHead]
  dsimp only [m] at *
  nlinarith only [hSum, hStirling, hHarmonicScaled]

theorem hamiltonian_row_cap_log_budget (n : Nat) (a X : Real)
    (ha : 1 <= a) (hX : (n + 2 : Real) <= X) :
    hamiltonianRowCapLogBound n (a / X) <=
      -(n + 2 : Real) + 16 * a * Real.log (2 * X) := by
  let m : Real := n + 1
  let t := Real.log (2 * X)
  have ha0 : 0 <= a := le_trans (by norm_num) ha
  have haPos : 0 < a := lt_of_lt_of_le (by norm_num) ha
  have hNat : (0 : Real) <= (n : Real) := Nat.cast_nonneg n
  have hm1 : 1 <= m := by dsimp only [m]; linarith only [hNat]
  have hm : 0 < m := lt_of_lt_of_le (by norm_num) hm1
  have hXm : m <= X := by dsimp only [m]; linarith only [hX]
  have hX1 : 1 <= X := le_trans hm1 hXm
  have hXPos : 0 < X := lt_of_lt_of_le (by norm_num) hX1
  have hc : 0 < a / X := div_pos haPos hXPos
  have hBase := hamiltonian_row_cap_log_stirling n (a / X) hc
  have hLogM : Real.log m <= t :=
    Real.log_le_log hm (by linarith only [hXm, hX1])
  have hCLe : a / X <= a := div_le_self ha0 hX1
  have hLogC : Real.log (a / X) <= a :=
    le_trans (Real.log_le_self (le_of_lt hc)) hCLe
  have hCM : (a / X) * m <= a := by
    have h := mul_le_mul_of_nonneg_left hXm (le_of_lt hc)
    have hClear : (a / X) * X = a := by field_simp [ne_of_gt hXPos]
    rw [hClear] at h
    exact h
  have hLogNonneg : 0 <= Real.log m := Real.log_nonneg hm1
  have hTop : (a / X) * m * (1 + Real.log m) <= a * (1 + t) := by
    have h1 : (a / X) * m * (1 + Real.log m) <= a * (1 + Real.log m) :=
      mul_le_mul_of_nonneg_right hCM (by linarith only [hLogNonneg])
    have h2 : a * (1 + Real.log m) <= a * (1 + t) :=
      mul_le_mul_of_nonneg_left (by linarith only [hLogM]) ha0
    exact le_trans h1 h2
  have hLogTwo : (1 / 2 : Real) <= Real.log 2 := by
    have h := Real.one_sub_inv_le_log_of_pos (x := 2) (by norm_num)
    norm_num at h
    exact h
  have hHalf : (1 / 2 : Real) <= t :=
    le_trans hLogTwo (Real.log_le_log (by norm_num) (by linarith only [hX1]))
  have ht : 0 <= t := le_trans (by norm_num) hHalf
  have hAhalf := mul_le_mul_of_nonneg_left hHalf ha0
  have hAt := mul_le_mul_of_nonneg_right ha ht
  dsimp only [m, t] at *
  nlinarith only [hBase, hLogC, hLogM, hTop, hAhalf, hAt, ha]

theorem hamiltonian_row_cap_permanent_upper (n : Nat)
    (A : Matrix (Fin (n + 2)) (Fin (n + 2)) Real) (a X : Real)
    (ha : 1 <= a) (hX : (n + 2 : Real) <= X)
    (hNonneg : forall i j, 0 <= A i j)
    (hRow : forall i, Finset.univ.sum (fun j => A i j) <= 1)
    (hCap : forall i j, A i j <= a / X) :
    Finset.univ.sum (fun sigma : Equiv.Perm (Fin (n + 2)) =>
      Finset.univ.prod (fun i => A i (sigma i))) <=
        Real.exp (-(n + 2 : Real) + 16 * a * Real.log (2 * X)) := by
  exact le_trans (hamiltonian_row_cap_permanent_exponential n A (a / X) hNonneg hRow hCap)
    (Real.exp_le_exp.mpr (hamiltonian_row_cap_log_budget n a X ha hX))

end PrimeFactorOscillations

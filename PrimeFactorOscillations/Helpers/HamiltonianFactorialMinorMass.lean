/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.HamiltonianCompensatedMinorTail
import PrimeFactorOscillations.Helpers.HamiltonianDeterminantEntryBudget
import PrimeFactorOscillations.Helpers.HamiltonianMinorHadamard

/-! # Factorial envelopes for aperiodic residual minor masses

The signed determinant is evaluated before this positive envelope is used.
The estimates below control only the accumulated ratio error and its tail.
-/

set_option autoImplicit false
set_option Elab.async false

noncomputable section

namespace PrimeFactorOscillations

theorem hamiltonian_exponential_term_bound
    (x : Real) (hx : 0 <= x) (r : Nat) :
    x ^ r <= Real.exp x * (r.factorial : Real) := by
  have hf : (0 : Real) < r.factorial := by exact_mod_cast Nat.factorial_pos r
  have hTerm : x ^ r / (r.factorial : Real) <=
      Finset.sum (Finset.range (r + 1)) (fun j => x ^ j / (j.factorial : Real)) := by
    exact Finset.single_le_sum
      (fun j _ => div_nonneg (pow_nonneg hx j) (Nat.cast_nonneg _))
      (Finset.mem_range.mpr (Nat.lt_succ_self r))
  have h := mul_le_mul_of_nonneg_right
    (hTerm.trans (Real.sum_le_exp_of_nonneg hx (r + 1))) hf.le
  have hCancel : x ^ r / (r.factorial : Real) * (r.factorial : Real) = x ^ r := by
    field_simp
  rw [hCancel] at h
  exact h

theorem hamiltonian_factorial_weighted_mass_bound
    (a : Nat -> Real) (C z : Real) (hC : 0 <= C)
    (hCoeff : forall r, a r ^ 2 <= C ^ r / (r.factorial : Real)) (n : Nat) :
    Finset.sum (Finset.range n) (fun r => (r : Real) * z ^ r * a r) <=
      2 * Real.exp (16 * C * z ^ 2) := by
  have hPoint (r : Nat) :
      2 * ((r : Real) * z ^ r * a r) <=
        ((1 : Real) / 4) ^ r +
          (16 * C * z ^ 2) ^ r / (r.factorial : Real) := by
    let u : Real := (r : Real) * ((1 : Real) / 4) ^ r
    let v : Real := (4 * z) ^ r * a r
    have hU : u ^ 2 <= ((1 : Real) / 4) ^ r := by
      have hr : (0 : Real) <= r := Nat.cast_nonneg r
      have hRank := hamiltonian_rank_square_exponential r
      have hRankSmall : (r : Real) ^ 2 <= (4 : Real) ^ r := by
        nlinarith only [hRank, hr]
      have h := mul_le_mul_of_nonneg_right
        hRankSmall
        (sq_nonneg (((1 : Real) / 4) ^ r))
      have hCancel : (4 : Real) ^ r * (((1 : Real) / 4) ^ r) ^ 2 =
          ((1 : Real) / 4) ^ r := by
        calc
          _ = ((4 : Real) * ((1 : Real) / 4) ^ 2) ^ r := by
            rw [mul_pow, pow_right_comm]
          _ = _ := by norm_num
      dsimp [u]
      rw [mul_pow]
      nlinarith only [h, hCancel]
    have hV : v ^ 2 <= (16 * C * z ^ 2) ^ r / (r.factorial : Real) := by
      have h := mul_le_mul_of_nonneg_left (hCoeff r) (sq_nonneg ((4 * z) ^ r))
      calc
        _ = ((4 * z) ^ r) ^ 2 * a r ^ 2 := mul_pow _ _ _
        _ <= ((4 * z) ^ r) ^ 2 * (C ^ r / (r.factorial : Real)) := h
        _ = _ := by
          rw [pow_right_comm, <- mul_div_assoc, <- mul_pow]
          congr 2
          ring
    have hUV : u * v = (r : Real) * z ^ r * a r := by
      dsimp [u, v]
      have hBase : ((1 : Real) / 4) ^ r * (4 * z) ^ r = z ^ r := by
        rw [<- mul_pow]
        congr 1
        ring
      calc
        _ = (r : Real) * (((1 : Real) / 4) ^ r * (4 * z) ^ r) * a r := by ring
        _ = _ := by rw [hBase]
    nlinarith only [sq_nonneg (u - v), hU, hV, hUV]
  have hSum := Finset.sum_le_sum (fun r (_ : Membership.mem (Finset.range n) r) => hPoint r)
  rw [<- Finset.mul_sum, Finset.sum_add_distrib] at hSum
  have hGeom := hamiltonian_geometric_sum_le_two ((1 : Real) / 4)
    (by norm_num) (by norm_num) n
  have hArg : 0 <= 16 * C * z ^ 2 := mul_nonneg (mul_nonneg (by norm_num) hC) (sq_nonneg z)
  have hTaylor := Real.sum_le_exp_of_nonneg hArg n
  have hExp : 1 <= Real.exp (16 * C * z ^ 2) := Real.one_le_exp hArg
  nlinarith only [hSum, hGeom, hTaylor, hExp]

end PrimeFactorOscillations

/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import PrimeFactorOscillations.Helpers.HamiltonianL2Resolvent

/-! # A finite mixing estimate for the full signed resolvent

A short prefix is controlled in row mass and the entire remaining tail is
smoothed once in Euclidean norm. Choosing the free cutoff at the mixing
scale gives a logarithmic diffuseness cost. The full inverse is retained.
-/

set_option autoImplicit false
set_option Elab.async false

open scoped Matrix.Norms.L2Operator

noncomputable section

namespace PrimeFactorOscillations

variable {Iota : Type*} [Fintype Iota] [DecidableEq Iota]

def hamiltonianRowMass (M : Matrix Iota Iota Real) (i : Iota) : Real :=
  Finset.univ.sum (fun j => abs (M i j))

theorem hamiltonian_row_mass_add (M N : Matrix Iota Iota Real) (i : Iota) :
    hamiltonianRowMass (M + N) i <= hamiltonianRowMass M i + hamiltonianRowMass N i := by
  unfold hamiltonianRowMass
  rw [<- Finset.sum_add_distrib]
  exact Finset.sum_le_sum (fun j _ => abs_add_le (M i j) (N i j))

theorem hamiltonian_row_mass_sum {J : Type*} (s : Finset J)
    (M : J -> Matrix Iota Iota Real) (i : Iota) :
    hamiltonianRowMass (s.sum M) i <= s.sum (fun a => hamiltonianRowMass (M a) i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [hamiltonianRowMass]
  | @insert a s ha ih =>
      rw [Finset.sum_insert ha, Finset.sum_insert ha]
      exact (hamiltonian_row_mass_add _ _ i).trans (add_le_add (le_refl _) ih)

theorem hamiltonian_row_mass_smoothed (M N : Matrix Iota Iota Real) (i : Iota) :
    hamiltonianRowMass (M * N) i <=
      Real.sqrt (Fintype.card Iota : Real) *
        norm (WithLp.toLp 2 (fun j => M i j) : EuclideanSpace Real Iota) * norm N := by
  classical
  let u : EuclideanSpace Real Iota := WithLp.toLp 2 (fun j => M i j)
  let v : EuclideanSpace Real Iota :=
    WithLp.toLp 2 (fun j => if 0 <= (M * N) i j then 1 else -1)
  let op := (@Matrix.toEuclideanCLM Real Iota _ _ _) N
  have hV : norm v = Real.sqrt (Fintype.card Iota : Real) := by
    have hSquare : norm v ^ 2 = (Fintype.card Iota : Real) := by
      rw [EuclideanSpace.real_norm_sq_eq]
      change Finset.univ.sum (fun j : Iota =>
        (if 0 <= (M * N) i j then (1 : Real) else -1) ^ 2) = _
      simp only [ite_pow, one_pow, neg_one_sq, ite_self]
      simp
    nlinarith only [hSquare, Real.sq_sqrt (Nat.cast_nonneg (Fintype.card Iota)),
      norm_nonneg v, Real.sqrt_nonneg (Fintype.card Iota : Real)]
  have hEntry : hamiltonianRowMass (M * N) i = inner Real u (op v) := by
    rw [Matrix.inner_toEuclideanCLM]
    change Finset.univ.sum (fun j => abs ((M * N) i j)) =
      M.mulVec (N.mulVec v.ofLp) i
    rw [Matrix.mulVec_mulVec]
    change Finset.univ.sum (fun j => abs ((M * N) i j)) =
      Finset.univ.sum (fun j => (M * N) i j *
        (if 0 <= (M * N) i j then 1 else -1))
    apply Finset.sum_congr rfl
    intro j hj
    by_cases h : 0 <= (M * N) i j
    . rw [if_pos h, mul_one, abs_of_nonneg h]
    . rw [if_neg h, mul_neg_one, abs_of_neg (lt_of_not_ge h)]
  calc
    _ = abs (inner Real u (op v)) := by
      rw [<- hEntry, abs_of_nonneg (Finset.sum_nonneg (fun j _ => abs_nonneg _))]
    _ <= norm u * norm (op v) := by
      have hInner : norm (inner Real u (op v)) <= norm u * norm (op v) :=
        norm_inner_le_norm _ _
      simpa only [Real.norm_eq_abs] using hInner
    _ <= norm u * (norm op * norm v) :=
      mul_le_mul_of_nonneg_left (op.le_opNorm v) (norm_nonneg u)
    _ = _ := by
      rw [hV, Matrix.l2_opNorm_toEuclideanCLM]
      ring


theorem hamiltonian_row_mass_neg (M : Matrix Iota Iota Real) (i : Iota) :
    hamiltonianRowMass (-M) i = hamiltonianRowMass M i := by
  simp only [hamiltonianRowMass, Matrix.neg_apply, abs_neg]

theorem hamiltonian_row_mass_sub (M N : Matrix Iota Iota Real) (i : Iota) :
    hamiltonianRowMass (M - N) i <= hamiltonianRowMass M i + hamiltonianRowMass N i := by
  simpa only [sub_eq_add_neg, hamiltonian_row_mass_neg] using hamiltonian_row_mass_add M (-N) i

theorem hamiltonian_row_mass_mul (M N : Matrix Iota Iota Real)
    (b : Real) (hN : forall j : Iota, hamiltonianRowMass N j <= b) (i : Iota) :
    hamiltonianRowMass (M * N) i <= hamiltonianRowMass M i * b := by
  unfold hamiltonianRowMass
  calc
    _ <= Finset.univ.sum (fun j => Finset.univ.sum (fun a => abs (M i a * N a j))) := by
      apply Finset.sum_le_sum
      intro j hj
      exact Finset.abs_sum_le_sum_abs _ _
    _ = Finset.univ.sum (fun a => abs (M i a) *
        Finset.univ.sum (fun j => abs (N a j))) := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro a ha
      rw [Finset.mul_sum]
      simp only [abs_mul]
    _ <= Finset.univ.sum (fun a => abs (M i a) * b) := by
      apply Finset.sum_le_sum
      intro a ha
      exact mul_le_mul_of_nonneg_left (hN a) (abs_nonneg _)
    _ = _ := (Finset.sum_mul _ _ _).symm

theorem hamiltonian_row_mass_power (M : Matrix Iota Iota Real)
    (b : Real) (hb : 0 <= b) (hM : forall i : Iota, hamiltonianRowMass M i <= b)
    (k : Nat) (i : Iota) :
    hamiltonianRowMass (M ^ k) i <= b ^ k := by
  induction k with
  | zero => simp [hamiltonianRowMass, Matrix.one_apply, abs_ite]
  | succ k ih =>
      rw [pow_succ, pow_succ]
      exact (hamiltonian_row_mass_mul _ M b hM i).trans
        (mul_le_mul_of_nonneg_right ih hb)

theorem hamiltonian_annihilating_power_sum (Q A : Matrix Iota Iota Real)
    (hQA : Q * A = 0) (hAQ : A * Q = 0) (k : Nat) :
    (Q + A) ^ (k + 1) = Q ^ (k + 1) + A ^ (k + 1) := by
  induction k with
  | zero => simp
  | succ k ih =>
      have hCrossQA : Q ^ (k + 1) * A = 0 := by
        rw [pow_succ, mul_assoc, hQA, mul_zero]
      have hCrossAQ : A ^ (k + 1) * Q = 0 := by
        rw [pow_succ, mul_assoc, hAQ, mul_zero]
      calc
        _ = (Q + A) ^ (k + 1) * (Q + A) := pow_succ _ _
        _ = (Q ^ (k + 1) + A ^ (k + 1)) * (Q + A) := by rw [ih]
        _ = Q ^ (k + 1) * Q + A ^ (k + 1) * A := by
          rw [add_mul, mul_add, mul_add, hCrossQA, hCrossAQ, add_zero, zero_add]
        _ = _ := by rw [pow_succ Q (k + 1), pow_succ A (k + 1)]

theorem hamiltonian_centered_power_row_bound (P A : Matrix Iota Iota Real)
    (b : Real) (hb : 0 <= b)
    (hP : forall i : Iota, hamiltonianRowMass P i <= b)
    (hA : forall i : Iota, hamiltonianRowMass A i <= 1)
    (hPA : (P - A) * A = 0) (hAP : A * (P - A) = 0)
    (k : Nat) (i : Iota) :
    hamiltonianRowMass ((P - A) ^ k) i <= b ^ k + 1 := by
  cases k with
  | zero => simp [hamiltonianRowMass, Matrix.one_apply, abs_ite]
  | succ k =>
      have hSplit : (P - A) ^ (k + 1) = P ^ (k + 1) - A ^ (k + 1) := by
        have h := hamiltonian_annihilating_power_sum (P - A) A hPA hAP k
        rw [sub_add_cancel] at h
        exact eq_sub_of_add_eq h.symm
      rw [hSplit]
      exact (hamiltonian_row_mass_sub _ _ i).trans
        (add_le_add (hamiltonian_row_mass_power P b hb hP _ i)
          (by simpa only [one_pow] using hamiltonian_row_mass_power A 1 (by norm_num) hA (k + 1) i))

variable [Nonempty Iota]

theorem hamiltonian_resolvent_finite_expansion (Q : Matrix Iota Iota Real)
    (hNorm : norm Q < 1) (k : Nat) :
    Ring.inverse ((1 : Matrix Iota Iota Real) - Q) =
      (Finset.range k).sum (fun j => Q ^ j) +
        Q ^ k * Ring.inverse ((1 : Matrix Iota Iota Real) - Q) := by
  let R := Ring.inverse ((1 : Matrix Iota Iota Real) - Q)
  have hCancel : ((1 : Matrix Iota Iota Real) - Q) * R = 1 :=
    Ring.mul_inverse_cancel _ (isUnit_one_sub_of_norm_lt_one hNorm)
  have hR : R = 1 + Q * R := by
    rw [sub_mul, one_mul] at hCancel
    exact sub_eq_iff_eq_add.mp hCancel
  change R = _
  induction k with
  | zero => simp [R]
  | succ k ih =>
      have hTail : Q ^ k * R = Q ^ k + (Q ^ k * Q) * R := by
        calc
          _ = Q ^ k * (1 + Q * R) := congrArg (fun X => Q ^ k * X) hR
          _ = _ := by rw [mul_add, mul_one, mul_assoc]
      rw [Finset.sum_range_succ, pow_succ]
      calc
        R = (Finset.range k).sum (fun j => Q ^ j) + Q ^ k * R := ih
        _ = (Finset.range k).sum (fun j => Q ^ j) +
          (Q ^ k + (Q ^ k * Q) * R) := by rw [hTail]
        _ = _ := (add_assoc _ _ _).symm

theorem hamiltonian_resolvent_mixing_cutoff (Q : Matrix Iota Iota Real)
    (rho C a : Real) (k : Nat)
    (hNorm : norm Q <= rho) (hRho : rho < 1)
    (hC : 0 <= C) (hA : 0 <= a)
    (hPrefix : forall j : Nat, j <= k -> forall i : Iota,
      hamiltonianRowMass (Q ^ j) i <= C)
    (hSmooth : forall i : Iota,
      Real.sqrt (Fintype.card Iota : Real) *
        norm (WithLp.toLp 2 (fun j => Q i j) : EuclideanSpace Real Iota) <= a)
    (i : Iota) :
    (1 - rho) * hamiltonianRowMass
      (Ring.inverse ((1 : Matrix Iota Iota Real) - Q)) i <=
        (1 - rho) * ((k + 1 : Nat) : Real) * C + a * rho ^ k := by
  let R := Ring.inverse ((1 : Matrix Iota Iota Real) - Q)
  have hGap : 0 <= 1 - rho := le_of_lt (sub_pos.mpr hRho)
  have hRho0 : 0 <= rho := (norm_nonneg Q).trans hNorm
  have hPower : norm (Q ^ k) <= rho ^ k := by
    apply (norm_pow_le Q k).trans
    gcongr
  have hR : (1 - rho) * norm R <= 1 := l2_neumann_certificate Q rho hNorm hRho
  have hShort : hamiltonianRowMass
      ((Finset.range (k + 1)).sum (fun j => Q ^ j)) i <= ((k + 1 : Nat) : Real) * C := by
    calc
      _ <= (Finset.range (k + 1)).sum (fun j => hamiltonianRowMass (Q ^ j) i) :=
        hamiltonian_row_mass_sum _ _ _
      _ <= (Finset.range (k + 1)).sum (fun _ => C) := by
        apply Finset.sum_le_sum
        intro j hj
        exact hPrefix j (Nat.le_of_lt_succ (Finset.mem_range.mp hj)) i
      _ = _ := by simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  have hTail : (1 - rho) * hamiltonianRowMass (Q ^ (k + 1) * R) i <= a * rho ^ k := by
    have hSmoothRow := hamiltonian_row_mass_smoothed Q (Q ^ k * R) i
    rw [pow_succ', Matrix.mul_assoc]
    calc
      _ <= (1 - rho) *
          (Real.sqrt (Fintype.card Iota : Real) *
            norm (WithLp.toLp 2 (fun j => Q i j) : EuclideanSpace Real Iota) *
              norm (Q ^ k * R)) := mul_le_mul_of_nonneg_left hSmoothRow hGap
      _ <= (1 - rho) * (a * (rho ^ k * norm R)) := by
        apply mul_le_mul_of_nonneg_left _ hGap
        exact mul_le_mul (hSmooth i)
          ((norm_mul_le _ _).trans (mul_le_mul_of_nonneg_right hPower (norm_nonneg R)))
          (norm_nonneg _) hA
      _ = (a * rho ^ k) * ((1 - rho) * norm R) := by ring
      _ <= (a * rho ^ k) * 1 := mul_le_mul_of_nonneg_left hR (mul_nonneg hA (pow_nonneg hRho0 k))
      _ = _ := mul_one _
  have hExpand := hamiltonian_resolvent_finite_expansion Q (hNorm.trans_lt hRho) (k + 1)
  have hMass : hamiltonianRowMass R i <=
      hamiltonianRowMass ((Finset.range (k + 1)).sum (fun j => Q ^ j)) i +
        hamiltonianRowMass (Q ^ (k + 1) * R) i := by
    change hamiltonianRowMass (Ring.inverse _) i <= _
    rw [hExpand]
    exact hamiltonian_row_mass_add _ _ _
  calc
    _ <= (1 - rho) *
      (hamiltonianRowMass ((Finset.range (k + 1)).sum (fun j => Q ^ j)) i +
        hamiltonianRowMass (Q ^ (k + 1) * R) i) :=
      mul_le_mul_of_nonneg_left hMass hGap
    _ = (1 - rho) *
        hamiltonianRowMass ((Finset.range (k + 1)).sum (fun j => Q ^ j)) i +
      (1 - rho) * hamiltonianRowMass (Q ^ (k + 1) * R) i := mul_add _ _ _
    _ <= (1 - rho) * (((k + 1 : Nat) : Real) * C) + a * rho ^ k :=
      add_le_add (mul_le_mul_of_nonneg_left hShort hGap) hTail
    _ = _ := by ring


theorem hamiltonian_logarithmic_mixing_cutoff (a rho : Real)
    (hA : 1 <= a) (hRho0 : 0 < rho) (hRho1 : rho < 1) :
    exists k : Nat, And
      ((k : Real) <= Real.log a / (-Real.log rho) + 1)
      (a * rho ^ k <= 1) := by
  let ell := Real.log a / (-Real.log rho)
  have hLog : 0 < -Real.log rho := neg_pos.mpr (Real.log_neg hRho0 hRho1)
  have hEll : 0 <= ell := div_nonneg (Real.log_nonneg hA) hLog.le
  refine Exists.intro (Nat.ceil ell) (And.intro ?_ ?_)
  . exact (Nat.ceil_lt_add_one hEll).le
  . have hK : Real.log a <= (Nat.ceil ell : Real) * (-Real.log rho) := by
      have hMul := mul_le_mul_of_nonneg_right (Nat.le_ceil ell) hLog.le
      have hCancel : ell * (-Real.log rho) = Real.log a := by
        dsimp only [ell]
        have hLogNonzero : Not (Real.log rho = 0) := ne_of_lt (Real.log_neg hRho0 hRho1)
        field_simp [hLogNonzero]
      rw [hCancel] at hMul
      exact hMul
    have hArg : Real.log a + (Nat.ceil ell : Real) * Real.log rho <= 0 := by
      nlinarith only [hK]
    calc
      a * rho ^ Nat.ceil ell =
          Real.exp (Real.log a + (Nat.ceil ell : Real) * Real.log rho) := by
        rw [Real.exp_add, Real.exp_nat_mul, Real.exp_log (lt_of_lt_of_le zero_lt_one hA),
          Real.exp_log hRho0]
      _ <= Real.exp 0 := Real.exp_le_exp.mpr hArg
      _ = 1 := Real.exp_zero

theorem hamiltonian_resolvent_logarithmic_row_bound (Q : Matrix Iota Iota Real)
    (rho C a : Real) (hNorm : norm Q <= rho)
    (hRho0 : 0 < rho) (hRho1 : rho < 1)
    (hC : 0 <= C) (hA : 1 <= a)
    (hPrefix : forall j : Nat, forall i : Iota, hamiltonianRowMass (Q ^ j) i <= C)
    (hSmooth : forall i : Iota,
      Real.sqrt (Fintype.card Iota : Real) *
        norm (WithLp.toLp 2 (fun j => Q i j) : EuclideanSpace Real Iota) <= a)
    (i : Iota) :
    (1 - rho) * hamiltonianRowMass
        (Ring.inverse ((1 : Matrix Iota Iota Real) - Q)) i <=
      (1 - rho) * C * (Real.log a / (-Real.log rho) + 2) + 1 := by
  choose k hK hTail using hamiltonian_logarithmic_mixing_cutoff a rho hA hRho0 hRho1
  have h := hamiltonian_resolvent_mixing_cutoff Q rho C a k hNorm hRho1 hC
    (lt_of_lt_of_le zero_lt_one hA).le (fun j _ i => hPrefix j i) hSmooth i
  have hK' : ((k + 1 : Nat) : Real) <= Real.log a / (-Real.log rho) + 2 := by
    push_cast
    linarith only [hK]
  have hScale := mul_le_mul_of_nonneg_left hK'
    (mul_nonneg (sub_pos.mpr hRho1).le hC)
  nlinarith only [h, hTail, hScale]

end PrimeFactorOscillations

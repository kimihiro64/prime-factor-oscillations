/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/

import OAI.NumberTheory.DirichletL.QuadraticSieve.FiniteOperator
import PrimeFactorOscillations.Assembly.DetectorPackets.QuadraticCarrierPacket

/-!
# IntegerQuadraticSieve

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
# Arithmetic reductions for the integer quadratic large sieve

The actual Jacobi matrix has reciprocity duality with a constant independent
of both cutoffs. Square factors in a row become coefficient masks, rather
than being discarded. These are unconditional finite reductions; the
Poisson self-improving estimate is not asserted here.
-/


noncomputable section
open scoped BigOperators
namespace PrimeFactorOscillations.IntegerQuadraticSieve

open QuadraticCarrierPacket

theorem kernel_mul_left (u v n : Nat) :
    kernel (u * v) n = kernel u n * kernel v n := by
  simp only [kernel, Nat.cast_mul, jacobiSym.mul_left, Int.cast_mul]

theorem kernel_mul_right (u a b : Nat)
    (ha : Not (a = 0)) (hb : Not (b = 0)) :
    kernel u (a * b) = kernel u a * kernel u b := by
  simp only [kernel, jacobiSym.mul_right' (u : Int) ha hb, Int.cast_mul]

theorem square_row_mask (v n : Nat) (hn : Not (n = 0)) :
    kernel (v ^ 2) n =
      if (v : Int).gcd n = 1 then (1 : Complex) else 0 := by
  by_cases h : (v : Int).gcd n = 1
  . rw [if_pos h, kernel_square v n h]
  . have hz : jacobiSym (v : Int) n = 0 :=
      jacobiSym.eq_zero_iff.mpr (And.intro hn h)
    simp only [kernel, Nat.cast_pow, jacobiSym.pow_left, hz,
      zero_pow (by decide : Not (2 = 0)), Int.cast_zero, if_neg h]

theorem row_square_factor (u v n : Nat) (hn : Not (n = 0)) :
    kernel (v ^ 2 * u) n =
      if (v : Int).gcd n = 1 then kernel u n else 0 := by
  rw [kernel_mul_left, square_row_mask v n hn]
  split_ifs <;> simp

theorem square_factor_amplitude (s : Finset Nat) (a : Nat -> Complex)
    (u v : Nat) (hs : forall n, Membership.mem s n -> Not (n = 0)) :
    s.sum (fun n => a n * kernel (v ^ 2 * u) n) =
      s.sum (fun n =>
        (if (v : Int).gcd n = 1 then a n else 0) * kernel u n) := by
  classical
  apply Finset.sum_congr rfl
  intro n hn
  rw [row_square_factor u v n (hs n hn)]
  split_ifs <;> simp

theorem common_column_factor (u g a b : Nat)
    (hg : Not (g = 0)) (ha : Not (a = 0)) (hb : Not (b = 0)) :
    kernel u (g * a) * kernel u (g * b) =
      kernel u g ^ 2 * kernel u (a * b) := by
  rw [kernel_mul_right u g a hg ha, kernel_mul_right u g b hg hb,
    kernel_mul_right u a b ha hb]
  ring

theorem kernel_square_value (u g : Nat) (hg : Not (g = 0)) :
    kernel u g ^ 2 =
      if (u : Int).gcd g = 1 then (1 : Complex) else 0 := by
  have heq : kernel u g ^ 2 = kernel (u ^ 2) g := by
    simp only [pow_two, kernel_mul_left]
  rw [heq, square_row_mask u g hg]

theorem common_column_mask (u g a b : Nat)
    (hg : Not (g = 0)) (ha : Not (a = 0)) (hb : Not (b = 0)) :
    kernel u (g * a) * kernel u (g * b) =
      if (u : Int).gcd g = 1 then kernel u (a * b) else 0 := by
  rw [common_column_factor u g a b hg ha hb, kernel_square_value u g hg]
  split_ifs <;> simp

theorem common_factor_correlation (rows : Finset Nat) (w : Nat -> Complex)
    (g a b : Nat) (hg : Not (g = 0))
    (ha : Not (a = 0)) (hb : Not (b = 0)) :
    rows.sum (fun u => w u * kernel u (g * a) * kernel u (g * b)) =
      (rows.filter (fun u : Nat => (u : Int).gcd g = 1)).sum
        (fun u => w u * kernel u (a * b)) := by
  classical
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro u hu
  rw [mul_assoc, common_column_mask u g a b hg ha hb]
  split_ifs <;> simp

def matrix {m n : Type*} (rows : m -> Nat) (cols : n -> Nat) :
    Matrix m n Complex := fun i j => kernel (rows i) (cols j)

def minusClass (a : Nat) : Complex := if a % 4 = 3 then -1 else 1

def thirdClass (a : Nat) : Complex := if a % 4 = 3 then 1 else 0

theorem reciprocity_split (u v : Nat) (hu : Odd u) (hv : Odd v) :
    kernel u v =
      kernel v u * (1 - thirdClass v) +
        minusClass u * kernel v u * thirdClass v := by
  have hu2 : u % 2 = 1 := Nat.odd_iff.mp hu
  have hv2 : v % 2 = 1 := Nat.odd_iff.mp hv
  have hrec := congrArg (fun z : Int => (z : Complex))
    (jacobiSym.quadratic_reciprocity_if hu2 hv2)
  by_cases hu3 : u % 4 = 3 <;> by_cases hv3 : v % 4 = 3
  all_goals
    simp only [hu3, hv3, and_self, true_and, false_and, ite_true, ite_false,
      Int.cast_neg] at hrec
    simp only [kernel, thirdClass, minusClass, hu3, hv3, ite_true, ite_false]
    simp_all

theorem reciprocity_operator_norm {m n : Type*}
    [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
    (rows : m -> Nat) (cols : n -> Nat)
    (hr : forall i, Odd (rows i)) (hc : forall j, Odd (cols j)) :
    norm (OAI.FiniteSieveOperator.operator (matrix rows cols)) <=
      2 * norm (OAI.FiniteSieveOperator.operator (matrix cols rows)) := by
  let B : Matrix m n Complex := (matrix cols rows).conjTranspose
  let T : Matrix m n Complex :=
    fun i j => (1 : Complex) * B i j * (1 - thirdClass (cols j))
  let U : Matrix m n Complex :=
    fun i j => minusClass (rows i) * B i j * thirdClass (cols j)
  have hB (i : m) (j : n) : B i j = kernel (cols j) (rows i) := by
    simp [B, matrix, kernel, Matrix.conjTranspose_apply]
  have hA : matrix rows cols = T + U := by
    ext i j
    change kernel (rows i) (cols j) = T i j + U i j
    dsimp only [T, U]
    rw [hB, one_mul]
    exact reciprocity_split (rows i) (cols j) (hr i) (hc j)
  have hThird (v : Nat) : norm (thirdClass v) <= 1 := by
    unfold thirdClass
    split_ifs <;> norm_num
  have hNotThird (v : Nat) : norm (1 - thirdClass v) <= 1 := by
    unfold thirdClass
    split_ifs <;> norm_num
  have hMinus (v : Nat) : norm (minusClass v) <= 1 := by
    unfold minusClass
    split_ifs <;> norm_num
  have hT : norm (OAI.FiniteSieveOperator.operator T) <=
      norm (OAI.FiniteSieveOperator.operator B) :=
    OAI.FiniteSieveOperator.diagonal_twist_norm_le B (fun _ => 1)
      (fun j => 1 - thirdClass (cols j)) (fun _ => by norm_num)
      (fun j => hNotThird (cols j))
  have hU : norm (OAI.FiniteSieveOperator.operator U) <=
      norm (OAI.FiniteSieveOperator.operator B) :=
    OAI.FiniteSieveOperator.diagonal_twist_norm_le B
      (fun i => minusClass (rows i)) (fun j => thirdClass (cols j))
      (fun i => hMinus (rows i)) (fun j => hThird (cols j))
  rw [hA, OAI.FiniteSieveOperator.operator_add]
  calc
    _ <= norm (OAI.FiniteSieveOperator.operator T) +
        norm (OAI.FiniteSieveOperator.operator U) := norm_add_le _ _
    _ <= 2 * norm (OAI.FiniteSieveOperator.operator B) := by linarith
    _ = _ := by
      change 2 * norm (OAI.FiniteSieveOperator.operator
        (matrix cols rows).conjTranspose) = _
      rw [OAI.FiniteSieveOperator.operator_conjTranspose_norm]

theorem reciprocity_energy {m n : Type*}
    [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
    (rows : m -> Nat) (cols : n -> Nat) (a : n -> Complex)
    (hr : forall i, Odd (rows i)) (hc : forall j, Odd (cols j)) :
    (Finset.univ.sum (fun i =>
      norm (Finset.univ.sum (fun j => kernel (rows i) (cols j) * a j)) ^ 2)) <=
      4 * norm (OAI.FiniteSieveOperator.operator (matrix cols rows)) ^ 2 *
        Finset.univ.sum (fun j => norm (a j) ^ 2) := by
  have h := OAI.FiniteSieveOperator.energy_bound (matrix rows cols) a
  have hn := reciprocity_operator_norm rows cols hr hc
  have hs : norm (OAI.FiniteSieveOperator.operator (matrix rows cols)) ^ 2 <=
      4 * norm (OAI.FiniteSieveOperator.operator (matrix cols rows)) ^ 2 := by
    have hsq := mul_self_le_mul_self
      (norm_nonneg (OAI.FiniteSieveOperator.operator (matrix rows cols))) hn
    nlinarith
  exact h.trans (mul_le_mul_of_nonneg_right hs
    (Finset.sum_nonneg (fun j _ => sq_nonneg (norm (a j)))))

end PrimeFactorOscillations.IntegerQuadraticSieve


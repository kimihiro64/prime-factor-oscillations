/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.HamiltonianCoprimePathLower
import PrimeFactorOscillations.Helpers.HamiltonianPathCountNormalization

/-! # Native exact integer path weights and endpoint-uniform upper counts -/

set_option autoImplicit false
set_option Elab.async false

open scoped Classical

noncomputable section

namespace PrimeFactorOscillations

variable {n : Nat} [NeZero n]

theorem hamiltonian_coprime_path_weight (a b : ZMod n) :
    hamiltonianPrescribedPathSum (hamiltonianCoprimeKernel (n := n)) a b =
      (hamiltonianGraphPathCount (hamiltonianCoprimeRelation (n := n)) a b : Real) /
        (n.totient : Real) ^ (n - 1) := by
  let M : Matrix (ZMod n) (ZMod n) Real :=
    fun i j => if hamiltonianCoprimeRelation i j then 1 else 0
  have hKernel : hamiltonianCoprimeKernel (n := n) =
      (fun i j => (1 / (n.totient : Real)) * M i j) := by
    ext i j
    by_cases h : hamiltonianCoprimeRelation i j
    case pos =>
      simp only [hamiltonian_coprime_kernel_indicator, M, h, ite_true, mul_one]
    case neg =>
      simp only [hamiltonian_coprime_kernel_indicator, M, h, ite_false, mul_zero]
  have hCount : hamiltonianPrescribedPathSum M a b =
      (hamiltonianGraphPathCount (hamiltonianCoprimeRelation (n := n)) a b : Real) :=
    hamiltonian_indicator_path_count (hamiltonianCoprimeRelation (n := n)) a b
  have hScale := hamiltonian_path_sum_scalar M a b (1 / (n.totient : Real))
  calc
    _ = hamiltonianPrescribedPathSum
        (fun i j => (1 / (n.totient : Real)) * M i j) a b :=
      congrArg (fun Q : Matrix (ZMod n) (ZMod n) Real =>
        hamiltonianPrescribedPathSum Q a b) hKernel
    _ = (1 / (n.totient : Real)) ^ (Fintype.card (ZMod n) - 1) *
        hamiltonianPrescribedPathSum M a b := hScale
    _ = _ := by
      rw [hCount, ZMod.card]
      simp only [div_pow, one_pow]
      ring

theorem hamiltonian_coprime_path_upper (hn : 2 <= n)
    (a b : ZMod n) (hab : Not (a = b)) :
    hamiltonianPrescribedPathSum (hamiltonianCoprimeKernel (n := n)) a b <=
      Real.exp (-((n - 1 : Nat) : Real) +
        16 * ((n : Real) / (n.totient : Real)) * Real.log (2 * (n : Real))) := by
  let m := n - 2
  let A := (n : Real) / (n.totient : Real)
  choose e he0 he1 using hamiltonian_two_endpoint_labels a b hab m
    (by rw [ZMod.card]; dsimp only [m]; omega)
  have hnPos : 0 < (n : Real) := by exact_mod_cast (show 0 < n by omega)
  have hdPos : 0 < (n.totient : Real) := by
    exact_mod_cast Nat.totient_pos.mpr (show 0 < n by omega)
  have hCap (i j : Fin (m + 2)) :
      (hamiltonianCoprimeKernel (n := n)).submatrix e e i j <= A / (n : Real) := by
    have hEq : A / (n : Real) = 1 / (n.totient : Real) := by
      dsimp only [A]
      field_simp [ne_of_gt hnPos, ne_of_gt hdPos]
    rw [hEq]
    exact hamiltonian_coprime_kernel_entry_cap (e i) (e j)
  have hRow (i : Fin (m + 2)) : Finset.univ.sum (fun j =>
      (hamiltonianCoprimeKernel (n := n)).submatrix e e i j) <= 1 := by
    change Finset.univ.sum (fun j => hamiltonianCoprimeKernel (e i) (e j)) <= 1
    rw [hamiltonian_sum_reindex e]
    exact (hamiltonian_coprime_kernel_row_sum (e i)).le
  have h := hamiltonian_prescribed_path_uniform_upper
    ((hamiltonianCoprimeKernel (n := n)).submatrix e e) 0 1 A (n : Real)
    (hamiltonian_totient_ratio_ge_one n (by omega))
    (by exact_mod_cast (show 1 <= n by omega))
    (by dsimp only [m]; exact_mod_cast (show n - 2 + 1 + 1 <= n by omega))
    (fun i j => hamiltonian_coprime_kernel_nonnegative (e i) (e j)) hRow hCap
  rw [hamiltonian_prescribed_path_reindex, he0, he1] at h
  have hRank : m + 1 = n - 1 := by dsimp only [m]; omega
  have hExponent : -((m + 1 : Nat) : Real) +
      16 * A * Real.log (2 * (n : Real)) =
      -((n - 1 : Nat) : Real) + 16 * A * Real.log (2 * (n : Real)) := by
    rw [hRank]
  exact h.trans_eq (congrArg Real.exp hExponent)

end PrimeFactorOscillations

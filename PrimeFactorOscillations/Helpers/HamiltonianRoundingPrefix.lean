/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.HamiltonianFiniteTracePath
import PrimeFactorOscillations.Helpers.HamiltonianUsedEdgeJointStep

/-! # Finite graph-rounding prefixes retain the complete matrix path and drift -/

set_option autoImplicit false
set_option Elab.async false

open scoped Matrix.Norms.L2Operator

noncomputable section

namespace PrimeFactorOscillations

abbrev HamiltonianRoundingIndex (Iota : Type*) :=
  Sum (Sum Iota Iota) (Sum (Sum Iota Iota) (Sum Iota Iota))

def hamiltonianRoundingDriftCost (Iota : Type*) [Fintype Iota] (delta alpha : Real) : Real :=
  hamiltonianForbiddenObservableCost delta * alpha *
    Real.log (4 * (Fintype.card Iota : Real))

variable {Iota : Type*} [Fintype Iota] [DecidableEq Iota]

structure HamiltonianRoundingPrefix
    (P : Matrix Iota Iota Real) (S1 S2 : Finset (Sum Iota Iota))
    (delta alpha : Real) (p n : Nat) where
  cross : Matrix Iota Iota Real
  centered : Nat -> Matrix (HamiltonianRoundingIndex Iota) (HamiltonianRoundingIndex Iota) Real
  increments : Nat -> Matrix (HamiltonianRoundingIndex Iota) (HamiltonianRoundingIndex Iota) Real
  drift : Matrix (HamiltonianRoundingIndex Iota) (HamiltonianRoundingIndex Iota) Real
  binary : forall i j, cross i j = 0 \/ cross i j = 1
  rows : forall i, Finset.univ.sum (fun j => cross i j) = (n : Real)
  cols : forall j, Finset.univ.sum (fun i => cross i j) = (n : Real)
  support : forall i j, P i j = 0 -> cross i j = 0
  start : centered 0 = 0
  hermitian : forall k, k <= n -> (centered k).IsHermitian
  increment_hermitian : forall k, k < n -> (increments k).IsHermitian
  increment_norm : forall k, k < n -> norm (increments k) <= 2
  direction : forall k, k < n -> Matrix.trace ((centered k) ^ p.pred * increments k) <= 0
  step : forall k, k < n -> centered (k + 1) = centered k + increments k
  error_identity : hamiltonianBipartiteJointLift S1 S2
    (cross - HSMul.hSMul (n : Real) P) = centered n + drift
  drift_norm : norm drift <= hamiltonianRoundingDriftCost Iota delta alpha * (n : Real) ^ 2

def hamiltonianRoundingPrefixZero
    (P : Matrix Iota Iota Real) (S1 S2 : Finset (Sum Iota Iota))
    (delta alpha : Real) (p : Nat) :
    HamiltonianRoundingPrefix P S1 S2 delta alpha p 0 where
  cross := 0
  centered := fun _ => 0
  increments := fun _ => 0
  drift := 0
  binary := fun _ _ => Or.inl rfl
  rows := fun _ => by simp
  cols := fun _ => by simp
  support := fun _ _ _ => rfl
  start := rfl
  hermitian := by
    intro k _
    change (0 : Matrix (HamiltonianRoundingIndex Iota)
      (HamiltonianRoundingIndex Iota) Real).conjTranspose = 0
    simp
  increment_hermitian := by intro k hk; omega
  increment_norm := by intro k hk; omega
  direction := by intro k hk; omega
  step := by intro k hk; omega
  error_identity := by simp
  drift_norm := by simp

theorem hamiltonian_rounding_prefix_moment
    (P : Matrix Iota Iota Real) (S1 S2 : Finset (Sum Iota Iota))
    (delta alpha : Real) (p n : Nat)
    (h : HamiltonianRoundingPrefix P S1 S2 delta alpha p n)
    (hp : 2 <= p) (hEven : Even p) :
    norm (h.centered n) ^ 2 <= 1 + 8 * (p.pred : Real) * (n : Real) *
      (Fintype.card (HamiltonianRoundingIndex Iota) : Real) ^ (2 / (p : Real)) :=
  hamiltonian_signed_trace_path_unit_regularization h.centered h.increments n p hp hEven
    h.start h.hermitian h.increment_hermitian h.step h.direction h.increment_norm

end PrimeFactorOscillations

/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/

import Lean.Elab.Tactic.Omega
import PrimeFactorOscillations.Assembly.DetectorPackets.JointSquarePrefixMean

/-!
# QuarticPrimitiveTransfer

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
# Quartic primitive transfer and joint product-label energy

The valuation branches in quartic primitive inversion reconstruct the
original exponent as w + 2*a + 4*b, with a at most one. Thus a changed
prime costs its inverse norm and the original numerator is m*a^2*b^4.
The analytic full Kubota mean and the local Gauss identities are separate
inputs, not formalized by this module.

The finite product-label identity charges the actual multiplication
fibre. Its analytic consumer replaces a sum of individual growing-label
bounds by one unrestricted numerator mean before the Mellin integral.
No zero-free boundary or analytic moment is asserted here.
-/


noncomputable section

namespace PrimeFactorOscillations.QuarticPrimitiveTransfer

inductive ValuationBranch (v : Nat) : Nat -> Nat -> Nat -> Prop where
  | unchanged : ValuationBranch v (v % 4) 0 (v / 4)
  | raised (hv : 4 <= v) (hr : v % 4 = 0) :
      ValuationBranch v 2 1 (v / 4 - 1)
  | lowered (hr : v % 4 = 2) :
      ValuationBranch v 0 1 (v / 4)

theorem valuation_identity {v w a b : Nat}
    (h : ValuationBranch v w a b) : v = w + 2 * a + 4 * b := by
  cases h with
  | unchanged => omega
  | raised hv hr => omega
  | lowered hr => omega

theorem residual_exponent_lt_four {v w a b : Nat}
    (h : ValuationBranch v w a b) : w < 4 := by
  cases h with
  | unchanged => omega
  | raised hv hr => omega
  | lowered hr => omega

theorem changed_exponent_le_one {v w a b : Nat}
    (h : ValuationBranch v w a b) : a <= 1 := by
  cases h <;> omega

theorem power_reconstruction (p : Nat) {v w a b : Nat}
    (h : ValuationBranch v w a b) :
    p ^ v = p ^ w * p ^ (2 * a) * p ^ (4 * b) := by
  rw [valuation_identity h, pow_add, pow_add]

theorem fiberwise_energy {I J : Type} [DecidableEq J]
    (P : Finset I) (Q : Finset J) (f : I -> J) (energy : J -> Real)
    (hmaps : forall i, Membership.mem P i -> Membership.mem Q (f i)) :
    P.sum (fun i => energy (f i)) =
      Q.sum (fun j =>
        ((P.filter (fun i => f i = j)).card : Real) * energy j) := by
  classical
  calc
    _ = P.sum (fun i => Q.sum (fun j =>
        if j = f i then energy j else 0)) := by
      apply Finset.sum_congr rfl
      intro i hi
      simp [hmaps i hi]
    _ = Q.sum (fun j => P.sum (fun i =>
        if j = f i then energy j else 0)) := Finset.sum_comm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro j hj
      simp only [eq_comm (a := j)]
      rw [<- Finset.sum_filter]
      simp only [Finset.sum_const, nsmul_eq_mul]

theorem fiberwise_energy_le {I J : Type} [DecidableEq J]
    (P : Finset I) (Q : Finset J) (f : I -> J) (energy : J -> Real)
    (multiplicity : Real)
    (hmaps : forall i, Membership.mem P i -> Membership.mem Q (f i))
    (henergy : forall j, Membership.mem Q j -> 0 <= energy j)
    (hfibre : forall j, Membership.mem Q j ->
      ((P.filter (fun i => f i = j)).card : Real) <= multiplicity) :
    P.sum (fun i => energy (f i)) <=
      multiplicity * Q.sum energy := by
  rw [fiberwise_energy P Q f energy hmaps, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro j hj
  exact mul_le_mul_of_nonneg_right (hfibre j hj) (henergy j hj)

theorem joint_product_energy_le {I J K : Type} [DecidableEq K]
    (N : Finset I) (R : Finset J) (P : Finset K)
    (product : I -> J -> K) (energy : K -> Real) (multiplicity : Real)
    (hmaps : forall n, Membership.mem N n ->
      forall r, Membership.mem R r -> Membership.mem P (product n r))
    (henergy : forall m, Membership.mem P m -> 0 <= energy m)
    (hfibre : forall m, Membership.mem P m ->
      (((N.product R).filter (fun p => product p.1 p.2 = m)).card : Real)
        <= multiplicity) :
    N.sum (fun n => R.sum (fun r => energy (product n r))) <=
      multiplicity * P.sum energy := by
  have hmap : forall p, Membership.mem (N.product R) p ->
      Membership.mem P (product p.1 p.2) := by
    intro p hp
    have h := Finset.mem_product.mp hp
    exact hmaps p.1 h.1 p.2 h.2
  have h := fiberwise_energy_le (N.product R) P
    (fun p => product p.1 p.2) energy multiplicity hmap henergy hfibre
  have heq := Finset.sum_product N R
    (fun p : Prod I J => energy (product p.1 p.2))
  exact heq.symm.le.trans h

end PrimeFactorOscillations.QuarticPrimitiveTransfer

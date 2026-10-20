/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/

import PrimeFactorOscillations.Assembly.DetectorPackets.CarrierAmplifiedMoment

/-!
# JointSquarePrefixMean

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
# Joint squarefree-prefix energy

This is the finite overlap step in a joint Type I mean. A prefix shared
by several divisor rows is charged its actual overlap, not the number
of rows times an unrestricted prefix moment. No analytic Gauss-sum
moment or zero-free boundary is assumed or proved by this finite lemma.
-/


noncomputable section

namespace PrimeFactorOscillations.JointSquarePrefixMean

theorem finite_cauchy {J : Type} (P : Finset J) (z h : J -> Complex) :
    norm (P.sum (fun j => z j * h j)) ^ 2 <=
      P.sum (fun j => norm (z j) ^ 2) *
        P.sum (fun j => norm (h j) ^ 2) := by
  have hn : norm (P.sum (fun j => z j * h j)) <=
      P.sum (fun j => norm (z j) * norm (h j)) := by
    calc
      _ <= P.sum (fun j => norm (z j * h j)) := norm_sum_le _ _
      _ = _ := by simp only [norm_mul]
  calc
    _ <= (P.sum (fun j => norm (z j) * norm (h j))) ^ 2 := by
      gcongr
    _ <= _ := Finset.sum_mul_sq_le_sq_mul_sq P (fun j => norm (z j))
      (fun j => norm (h j))

theorem incidence_energy {I J : Type} (R : Finset I) (P : Finset J)
    (inc : I -> J -> Prop) [forall i j, Decidable (inc i j)]
    (z : I -> J -> Complex) (h : J -> Complex) (W : Real)
    (hweight : forall i, Membership.mem R i ->
      P.sum (fun j => if inc i j then norm (z i j) ^ 2 else 0) <= W) :
    R.sum (fun i =>
      norm (P.sum (fun j => if inc i j then z i j * h j else 0)) ^ 2) <=
      W * P.sum (fun j =>
        ((R.filter (fun i => inc i j)).card : Real) * norm (h j) ^ 2) := by
  have hrow : forall i, Membership.mem R i ->
      norm (P.sum (fun j => if inc i j then z i j * h j else 0)) ^ 2 <=
        W * P.sum (fun j => if inc i j then norm (h j) ^ 2 else 0) := by
    intro i hi
    have hc := finite_cauchy P
      (fun j => if inc i j then z i j else 0)
      (fun j => if inc i j then h j else 0)
    simp only [ite_mul_ite, zero_mul, apply_ite norm, apply_ite (fun x : Real => x ^ 2),
      norm_zero, zero_pow (by decide : Not (2 = 0))] at hc
    exact hc.trans (mul_le_mul_of_nonneg_right (hweight i hi)
      (Finset.sum_nonneg (fun j _ => by split_ifs <;> positivity)))
  calc
    _ <= R.sum (fun i =>
        W * P.sum (fun j => if inc i j then norm (h j) ^ 2 else 0)) :=
      Finset.sum_le_sum hrow
    _ = W * P.sum (fun j =>
        ((R.filter (fun i => inc i j)).card : Real) * norm (h j) ^ 2) := by
      rw [<- Finset.mul_sum, Finset.sum_comm]
      congr 1
      apply Finset.sum_congr rfl
      intro j hj
      rw [<- Finset.sum_filter]
      simp only [Finset.sum_const, nsmul_eq_mul]

end PrimeFactorOscillations.JointSquarePrefixMean


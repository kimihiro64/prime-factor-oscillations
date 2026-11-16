/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.HamiltonianPrimeRelativeCount

/-! # Exact finite entropy optimality from stochastic scaling potentials -/

set_option autoImplicit false
set_option Elab.async false

noncomputable section

namespace PrimeFactorOscillations

theorem hamiltonian_log_tangent (t u : Real) (ht : 0 <= t) (hu : 0 < u) :
    t * Real.log u + t - u <= t * Real.log t := by
  by_cases hzero : t = 0
  . subst t
    simp only [zero_mul, zero_add, zero_sub]
    linarith only [hu]
  . have htPos : 0 < t := lt_of_le_of_ne ht (Ne.symm hzero)
    have h := Real.log_le_sub_one_of_pos (div_pos hu htPos)
    rw [Real.log_div (ne_of_gt hu) hzero] at h
    have hScaled := mul_le_mul_of_nonneg_left h ht
    have hCancel : t * (u / t - 1) = u - t := by field_simp [hzero]
    rw [hCancel] at hScaled
    nlinarith only [hScaled]

variable {Iota : Type*} [Fintype Iota] [DecidableEq Iota]

def hamiltonianCrossEntropy (X : Matrix Iota Iota Real) : Real :=
  -Finset.univ.sum (fun i => Finset.univ.sum (fun j => X i j * Real.log (X i j)))

theorem hamiltonian_stochastic_potential_sum
    (X : Matrix Iota Iota Real) (r s : Iota -> Real)
    (hRow : forall i, Finset.univ.sum (fun j => X i j) = 1)
    (hCol : forall j, Finset.univ.sum (fun i => X i j) = 1) :
    Finset.univ.sum (fun i => Finset.univ.sum (fun j => X i j * (r i + s j))) =
      Finset.univ.sum r + Finset.univ.sum s := by
  have hLeft : Finset.univ.sum (fun i => Finset.univ.sum (fun j => X i j * r i)) =
      Finset.univ.sum r := by
    apply Finset.sum_congr rfl
    intro i hi
    rw [<- Finset.sum_mul, hRow, one_mul]
  have hRight : Finset.univ.sum (fun i => Finset.univ.sum (fun j => X i j * s j)) =
      Finset.univ.sum s := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro j hj
    rw [<- Finset.sum_mul, hCol, one_mul]
  simp_rw [mul_add, Finset.sum_add_distrib]
  rw [hLeft, hRight]

theorem hamiltonian_stochastic_entropy_value
    (T : Matrix Iota Iota Real) (r s : Iota -> Real)
    (hRow : forall i, Finset.univ.sum (fun j => T i j) = 1)
    (hCol : forall j, Finset.univ.sum (fun i => T i j) = 1)
    (hLog : forall i j, Not (T i j = 0) -> Real.log (T i j) = r i + s j) :
    hamiltonianCrossEntropy T = -Finset.univ.sum r - Finset.univ.sum s := by
  have hPoint (i j : Iota) :
      T i j * Real.log (T i j) = T i j * (r i + s j) := by
    by_cases h : T i j = 0
    . simp only [h, zero_mul]
    . rw [hLog i j h]
  unfold hamiltonianCrossEntropy
  simp_rw [hPoint]
  rw [hamiltonian_stochastic_potential_sum T r s hRow hCol]
  ring

theorem hamiltonian_stochastic_entropy_maximum
    (T X : Matrix Iota Iota Real) (r s : Iota -> Real)
    (hT : forall i j, 0 <= T i j) (hX : forall i j, 0 <= X i j)
    (hTRow : forall i, Finset.univ.sum (fun j => T i j) = 1)
    (hTCol : forall j, Finset.univ.sum (fun i => T i j) = 1)
    (hXRow : forall i, Finset.univ.sum (fun j => X i j) = 1)
    (hXCol : forall j, Finset.univ.sum (fun i => X i j) = 1)
    (hSupport : forall i j, T i j = 0 -> X i j = 0)
    (hLog : forall i j, Not (T i j = 0) -> Real.log (T i j) = r i + s j) :
    hamiltonianCrossEntropy X <= hamiltonianCrossEntropy T := by
  have hPoint (i j : Iota) :
      X i j * (r i + s j) + X i j - T i j <= X i j * Real.log (X i j) := by
    by_cases h : T i j = 0
    . simp only [h, hSupport i j h, zero_mul, zero_add, sub_self, le_refl]
    . have hPos : 0 < T i j := lt_of_le_of_ne (hT i j) (Ne.symm h)
      have hTangent := hamiltonian_log_tangent (X i j) (T i j) (hX i j) hPos
      rwa [hLog i j h] at hTangent
  have hSum := Finset.sum_le_sum (fun i (_ : Membership.mem Finset.univ i) =>
    Finset.sum_le_sum (fun j (_ : Membership.mem Finset.univ j) => hPoint i j))
  simp_rw [Finset.sum_sub_distrib, Finset.sum_add_distrib] at hSum
  rw [hamiltonian_stochastic_potential_sum X r s hXRow hXCol] at hSum
  have hMass : Finset.univ.sum (fun i => Finset.univ.sum (fun j => X i j)) =
      Finset.univ.sum (fun i => Finset.univ.sum (fun j => T i j)) := by
    simp only [hXRow, hTRow]
  have hValue := hamiltonian_stochastic_entropy_value T r s hTRow hTCol hLog
  unfold hamiltonianCrossEntropy at hValue
  unfold hamiltonianCrossEntropy
  linarith only [hSum, hMass, hValue]

end PrimeFactorOscillations

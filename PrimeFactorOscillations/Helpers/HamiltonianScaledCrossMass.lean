/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.HamiltonianForbiddenCrossPacket

/-! # Full row and column mass of a scaled deletion and every subset observable -/

set_option autoImplicit false
set_option Elab.async false

open scoped Matrix.Norms.L2Operator

noncomputable section

namespace PrimeFactorOscillations

variable {Iota : Type*} [Fintype Iota] [DecidableEq Iota]

theorem hamiltonian_scaled_cross_pointwise_error
    (T : Matrix Iota Iota Real) (z : Sum Iota Iota -> Real) (r : Real)
    (hr : 0 <= r) (hZ : forall k, abs (z k) <= r)
    (hT : forall i j, 0 <= T i j) (i j : Iota) :
    abs (hamiltonianScaledCross T z i j - T i j) <=
      (2 * r + r ^ 2) * T i j := by
  have hMul := mul_le_mul (hZ (Sum.inl i)) (hZ (Sum.inr j)) (abs_nonneg _) hr
  have hTriangle := abs_add_le
    (z (Sum.inl i) + z (Sum.inr j)) (z (Sum.inl i) * z (Sum.inr j))
  rw [abs_mul] at hTriangle
  have hCoeff :
      abs (z (Sum.inl i) + z (Sum.inr j) + z (Sum.inl i) * z (Sum.inr j)) <=
        2 * r + r ^ 2 := by
    nlinarith only [hTriangle, abs_add_le (z (Sum.inl i)) (z (Sum.inr j)),
      hZ (Sum.inl i), hZ (Sum.inr j), hMul]
  have hId : hamiltonianScaledCross T z i j - T i j =
      (z (Sum.inl i) + z (Sum.inr j) + z (Sum.inl i) * z (Sum.inr j)) * T i j := by
    unfold hamiltonianScaledCross
    ring
  rw [hId, abs_mul, abs_of_nonneg (hT i j)]
  exact mul_le_mul_of_nonneg_right hCoeff (hT i j)

theorem hamiltonian_scaled_deletion_pointwise_mass
    (P Q : Matrix Iota Iota Real) (z : Sum Iota Iota -> Real) (r : Real)
    (hr : 0 <= r) (hZ : forall k, abs (z k) <= r)
    (hQ : forall i j, 0 <= Q i j) (hQP : forall i j, Q i j <= P i j)
    (i j : Iota) :
    abs (hamiltonianScaledCross (P - Q) z i j - P i j) <=
      (2 * r + r ^ 2) * (P i j - Q i j) + Q i j := by
  have hT := hamiltonian_scaled_cross_pointwise_error (P - Q) z r hr hZ
    (fun a b => sub_nonneg.mpr (hQP a b)) i j
  have hId : hamiltonianScaledCross (P - Q) z i j - P i j =
      (hamiltonianScaledCross (P - Q) z i j - (P - Q) i j) - Q i j := by
    simp only [Matrix.sub_apply]
    ring
  rw [hId]
  have hTriangle := abs_add_le
    (hamiltonianScaledCross (P - Q) z i j - (P - Q) i j) (-Q i j)
  rw [abs_neg] at hTriangle
  change abs (hamiltonianScaledCross (P - Q) z i j - (P - Q) i j - Q i j) <= _ at hTriangle
  exact hTriangle.trans (add_le_add hT (le_of_eq (abs_of_nonneg (hQ i j))))

theorem hamiltonian_scaled_deletion_absolute_mass
    (P Q : Matrix Iota Iota Real) (z : Sum Iota Iota -> Real) (r eta : Real)
    (hr : 0 <= r) (hZ : forall k, abs (z k) <= r)
    (hPRow : forall i, Finset.univ.sum (fun j => P i j) = 1)
    (hPCol : forall j, Finset.univ.sum (fun i => P i j) = 1)
    (hQ : forall i j, 0 <= Q i j) (hQP : forall i j, Q i j <= P i j)
    (hQRow : forall i, Finset.univ.sum (fun j => Q i j) <= eta)
    (hQCol : forall j, Finset.univ.sum (fun i => Q i j) <= eta) :
    (forall i, Finset.univ.sum
      (fun j => abs (hamiltonianScaledCross (P - Q) z i j - P i j)) <=
        eta + (2 * r + r ^ 2)) /\
    (forall j, Finset.univ.sum
      (fun i => abs (hamiltonianScaledCross (P - Q) z i j - P i j)) <=
        eta + (2 * r + r ^ 2)) := by
  have hc : 0 <= 2 * r + r ^ 2 := by positivity
  have hPoint := hamiltonian_scaled_deletion_pointwise_mass P Q z r hr hZ hQ hQP
  constructor
  . intro i
    have hMass : Finset.univ.sum (fun j => P i j - Q i j) <= 1 := by
      rw [Finset.sum_sub_distrib, hPRow i]
      exact sub_le_self _ (Finset.sum_nonneg (fun j _ => hQ i j))
    calc
      _ <= Finset.univ.sum (fun j => (2 * r + r ^ 2) * (P i j - Q i j) + Q i j) :=
        Finset.sum_le_sum (fun j _ => hPoint i j)
      _ = (2 * r + r ^ 2) * Finset.univ.sum (fun j => P i j - Q i j) +
          Finset.univ.sum (fun j => Q i j) := by
            rw [Finset.sum_add_distrib, Finset.mul_sum]
      _ <= (2 * r + r ^ 2) * 1 + eta :=
        add_le_add (mul_le_mul_of_nonneg_left hMass hc) (hQRow i)
      _ = _ := by ring
  . intro j
    have hMass : Finset.univ.sum (fun i => P i j - Q i j) <= 1 := by
      rw [Finset.sum_sub_distrib, hPCol j]
      exact sub_le_self _ (Finset.sum_nonneg (fun i _ => hQ i j))
    calc
      _ <= Finset.univ.sum (fun i => (2 * r + r ^ 2) * (P i j - Q i j) + Q i j) :=
        Finset.sum_le_sum (fun i _ => hPoint i j)
      _ = (2 * r + r ^ 2) * Finset.univ.sum (fun i => P i j - Q i j) +
          Finset.univ.sum (fun i => Q i j) := by
            rw [Finset.sum_add_distrib, Finset.mul_sum]
      _ <= (2 * r + r ^ 2) * 1 + eta :=
        add_le_add (mul_le_mul_of_nonneg_left hMass hc) (hQCol j)
      _ = _ := by ring

theorem hamiltonian_absolute_mass_subset_observables
    (A : Matrix Iota Iota Real) (b : Real)
    (hRows : forall i, Finset.univ.sum (fun j => abs (A i j)) <= b)
    (hCols : forall j, Finset.univ.sum (fun i => abs (A i j)) <= b)
    (S : Finset Iota) :
    (forall i, abs (S.sum (fun j => A i j)) <= b) /\
      (forall j, abs (S.sum (fun i => A i j)) <= b) := by
  constructor
  . intro i
    exact (Finset.abs_sum_le_sum_abs _ _).trans
      ((Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ S)
        (fun j _ _ => abs_nonneg (A i j))).trans (hRows i))
  . intro j
    exact (Finset.abs_sum_le_sum_abs _ _).trans
      ((Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ S)
        (fun i _ _ => abs_nonneg (A i j))).trans (hCols j))

end PrimeFactorOscillations

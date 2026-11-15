/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.HamiltonianBoundaryEquations

/-! # Exact conservation removes the residual parity obstruction

For arbitrary real multipliers and an arbitrary rectangular cross block,
the two scaling residuals have the same total whenever the part sizes
agree. Thus a parity-shaped residual must be zero. All products remain
coupled; positivity and an estimate are not substituted for conservation.
-/

set_option autoImplicit false
set_option Elab.async false

noncomputable section

namespace PrimeFactorOscillations

variable {Rows Cols : Type*} [Fintype Rows] [Fintype Cols]

def hamiltonianScalingResidual (Q : Matrix Rows Cols Real)
    (x : Rows -> Real) (y : Cols -> Real) : Sum Rows Cols -> Real
  | Sum.inl i => x i * Finset.sum Finset.univ (fun j => Q i j * y j) - 1
  | Sum.inr j => y j * Finset.sum Finset.univ (fun i => Q i j * x i) - 1

theorem hamiltonianScalingResidual_balance (Q : Matrix Rows Cols Real)
    (x : Rows -> Real) (y : Cols -> Real)
    (hCard : Fintype.card Rows = Fintype.card Cols) :
    Finset.sum Finset.univ (fun i => hamiltonianScalingResidual Q x y (Sum.inl i)) =
      Finset.sum Finset.univ (fun j => hamiltonianScalingResidual Q x y (Sum.inr j)) := by
  have hCross :
      Finset.sum Finset.univ (fun i => x i *
        Finset.sum Finset.univ (fun j => Q i j * y j)) =
      Finset.sum Finset.univ (fun j => y j *
        Finset.sum Finset.univ (fun i => Q i j * x i)) := by
    simp_rw [Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro j hj
    apply Finset.sum_congr rfl
    intro i hi
    ring
  simp only [hamiltonianScalingResidual, Finset.sum_sub_distrib,
    Finset.sum_const, Finset.card_univ, nsmul_eq_mul, hCard, hCross]

theorem hamiltonianScalingResidual_parity_zero [Nonempty Rows]
    (Q : Matrix Rows Cols Real) (x : Rows -> Real) (y : Cols -> Real)
    (hCard : Fintype.card Rows = Fintype.card Cols) (c : Real)
    (hLeft : forall i, hamiltonianScalingResidual Q x y (Sum.inl i) = c)
    (hRight : forall j, hamiltonianScalingResidual Q x y (Sum.inr j) = -c) :
    c = 0 /\ forall k, hamiltonianScalingResidual Q x y k = 0 := by
  have h := hamiltonianScalingResidual_balance Q x y hCard
  simp only [hLeft, hRight, Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
    <- hCard] at h
  have hN : 0 < (Fintype.card Rows : Real) := Nat.cast_pos.mpr Fintype.card_pos
  have hc : c = 0 := by nlinarith only [h, hN]
  refine And.intro hc ?_
  intro k
  cases k with
  | inl i => rw [hLeft, hc]
  | inr j => rw [hRight, hc, neg_zero]

theorem hamiltonianScaling_from_parity_residual [Nonempty Rows]
    (Q : Matrix Rows Cols Real) (x : Rows -> Real) (y : Cols -> Real)
    (hCard : Fintype.card Rows = Fintype.card Cols) (c : Real)
    (hLeft : forall i, hamiltonianScalingResidual Q x y (Sum.inl i) = c)
    (hRight : forall j, hamiltonianScalingResidual Q x y (Sum.inr j) = -c) :
    (forall i, x i * Finset.sum Finset.univ (fun j => Q i j * y j) = 1) /\
      (forall j, y j * Finset.sum Finset.univ (fun i => Q i j * x i) = 1) := by
  have hZero := (hamiltonianScalingResidual_parity_zero Q x y hCard c hLeft hRight).2
  exact And.intro
    (fun i => sub_eq_zero.mp (hZero (Sum.inl i)))
    (fun j => sub_eq_zero.mp (hZero (Sum.inr j)))

end PrimeFactorOscillations

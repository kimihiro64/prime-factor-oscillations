/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.HamiltonianSpectralCuts

/-! # The exact finite centered cut vector and its full support -/

set_option autoImplicit false
set_option Elab.async false

open scoped Matrix.Norms.L2Operator

noncomputable section

namespace PrimeFactorOscillations

variable {Iota : Type*} [Fintype Iota] [DecidableEq Iota]

def hamiltonianCutIndicator (W : Finset Iota) (i : Iota) : Real :=
  if Membership.mem W i then 1 else 0

def hamiltonianCutCentered (W : Finset Iota) (i : Iota) : Real :=
  hamiltonianCutIndicator W i - (W.card : Real) / (Fintype.card Iota : Real)

def hamiltonianCutBoundary (M : Matrix Iota Iota Real) (W : Finset Iota) : Real :=
  W.sum (fun i => (Finset.univ \ W).sum (fun j => M i j))

theorem hamiltonian_cut_filter (W : Finset Iota) :
    Finset.univ.filter (fun i => Membership.mem W i) = W := by
  ext i
  simp

theorem hamiltonian_cut_complement_filter (W : Finset Iota) :
    Finset.univ.filter (fun i => Not (Membership.mem W i)) = Finset.univ \ W := by
  ext i
  simp

theorem hamiltonian_sum_cut_partition (W : Finset Iota) (f : Iota -> Real) :
    Finset.univ.sum f = W.sum f + (Finset.univ \ W).sum f := by
  have hLeft : Finset.univ.sum (fun i => if Membership.mem W i then f i else 0) =
      W.sum f := by
    rw [<- Finset.sum_filter, hamiltonian_cut_filter]
  have hRight : Finset.univ.sum (fun i => if Not (Membership.mem W i) then f i else 0) =
      (Finset.univ \ W).sum f := by
    rw [<- Finset.sum_filter, hamiltonian_cut_complement_filter]
  calc
    _ = Finset.univ.sum (fun i => (if Membership.mem W i then f i else 0) +
        (if Not (Membership.mem W i) then f i else 0)) := by
      apply Finset.sum_congr rfl
      intro i hi
      by_cases h : Membership.mem W i <;> simp [h]
    _ = _ := by rw [Finset.sum_add_distrib, hLeft, hRight]

theorem hamiltonian_cut_indicator_sum (W : Finset Iota) :
    Finset.univ.sum (hamiltonianCutIndicator W) = (W.card : Real) := by
  unfold hamiltonianCutIndicator
  rw [<- Finset.sum_filter, hamiltonian_cut_filter]
  simp

theorem hamiltonian_cut_centered_sum [Nonempty Iota] (W : Finset Iota) :
    Finset.univ.sum (hamiltonianCutCentered W) = 0 := by
  have hn : Not ((Fintype.card Iota : Real) = 0) :=
    ne_of_gt (Nat.cast_pos.mpr Fintype.card_pos)
  unfold hamiltonianCutCentered
  rw [Finset.sum_sub_distrib, hamiltonian_cut_indicator_sum, Finset.sum_const]
  simp only [Finset.card_univ, nsmul_eq_mul]
  field_simp [hn]
  ring

theorem hamiltonian_cut_centered_square_sum [Nonempty Iota] (W : Finset Iota) :
    Finset.univ.sum (fun i => hamiltonianCutCentered W i ^ 2) =
      (W.card : Real) * ((Fintype.card Iota : Real) - (W.card : Real)) /
        (Fintype.card Iota : Real) := by
  let c := (W.card : Real) / (Fintype.card Iota : Real)
  have hPoint (i : Iota) : hamiltonianCutCentered W i ^ 2 =
      (1 - 2 * c) * hamiltonianCutIndicator W i + c ^ 2 := by
    by_cases h : Membership.mem W i
    . simp only [hamiltonianCutCentered, hamiltonianCutIndicator, h, ite_true]
      change (1 - c) ^ 2 = (1 - 2 * c) * 1 + c ^ 2
      ring
    . simp only [hamiltonianCutCentered, hamiltonianCutIndicator, h, ite_false]
      change (0 - c) ^ 2 = (1 - 2 * c) * 0 + c ^ 2
      ring
  simp_rw [hPoint, Finset.sum_add_distrib]
  rw [<- Finset.mul_sum, hamiltonian_cut_indicator_sum, Finset.sum_const]
  simp only [Finset.card_univ, nsmul_eq_mul]
  dsimp only [c]
  have hn : Not ((Fintype.card Iota : Real) = 0) :=
    ne_of_gt (Nat.cast_pos.mpr Fintype.card_pos)
  field_simp
  ring

theorem hamiltonian_dirichlet_centered_indicator (M : Matrix Iota Iota Real)
    (W : Finset Iota) :
    hamiltonianDirichlet M (hamiltonianCutCentered W) =
      hamiltonianDirichlet M (hamiltonianCutIndicator W) := by
  change hamiltonianDirichlet M (fun i => hamiltonianCutIndicator W i -
    (W.card : Real) / (Fintype.card Iota : Real)) = _
  simpa only [sub_eq_add_neg] using
    hamiltonian_dirichlet_shift M (hamiltonianCutIndicator W)
      (-((W.card : Real) / (Fintype.card Iota : Real)))


theorem hamiltonian_dirichlet_indicator_boundary (M : Matrix Iota Iota Real)
    (hSymm : forall i j, M i j = M j i) (W : Finset Iota) :
    hamiltonianDirichlet M (hamiltonianCutIndicator W) = hamiltonianCutBoundary M W := by
  let V := Finset.univ \ W
  let row := fun i => Finset.univ.sum (fun j => M i j *
    (hamiltonianCutIndicator W i - hamiltonianCutIndicator W j) ^ 2)
  have hIn (i : Iota) (hi : Membership.mem W i) : row i = V.sum (fun j => M i j) := by
    calc
      _ = Finset.univ.sum (fun j => if Not (Membership.mem W j) then M i j else 0) := by
        apply Finset.sum_congr rfl
        intro j hj
        by_cases h : Membership.mem W j <;> simp [hamiltonianCutIndicator, hi, h]
      _ = _ := by rw [<- Finset.sum_filter, hamiltonian_cut_complement_filter]
  have hOut (i : Iota) (hi : Not (Membership.mem W i)) : row i = W.sum (fun j => M i j) := by
    calc
      _ = Finset.univ.sum (fun j => if Membership.mem W j then M i j else 0) := by
        apply Finset.sum_congr rfl
        intro j hj
        by_cases h : Membership.mem W j <;> simp [hamiltonianCutIndicator, hi, h]
      _ = _ := by rw [<- Finset.sum_filter, hamiltonian_cut_filter]
  have hReverse : V.sum (fun i => W.sum (fun j => M i j)) = hamiltonianCutBoundary M W := by
    calc
      _ = W.sum (fun i => V.sum (fun j => M j i)) := Finset.sum_comm
      _ = _ := by
        unfold hamiltonianCutBoundary
        apply Finset.sum_congr rfl
        intro i hi
        apply Finset.sum_congr rfl
        intro j hj
        exact hSymm j i
  have hTotal : Finset.univ.sum row = 2 * hamiltonianCutBoundary M W := by
    rw [hamiltonian_sum_cut_partition W row]
    have hLeft : W.sum row = hamiltonianCutBoundary M W :=
      Finset.sum_congr rfl (fun i hi => hIn i hi)
    have hRight : V.sum row = V.sum (fun i => W.sum (fun j => M i j)) := by
      apply Finset.sum_congr rfl
      intro i hi
      have hNot : Not (Membership.mem W i) := (Finset.mem_sdiff.mp hi).2
      exact hOut i hNot
    change W.sum row + V.sum row = _
    rw [hLeft, hRight, hReverse]
    ring
  change (1 / 2 : Real) * Finset.univ.sum row = _
  rw [hTotal]
  ring

theorem hamiltonian_cut_reference_bound [Nonempty Iota]
    (M P : Matrix Iota Iota Real) (W : Finset Iota) (d rho : Real)
    (hSymm : forall i j, M i j = M j i)
    (hDegree : forall i, d <= Finset.univ.sum (fun j => M i j))
    (hReference : hamiltonianQuadratic P (hamiltonianCutCentered W) <= 0)
    (hNorm : norm (M - P) <= rho) :
    (d - rho) * ((W.card : Real) * ((Fintype.card Iota : Real) - (W.card : Real)) /
      (Fintype.card Iota : Real)) <= hamiltonianCutBoundary M W := by
  have h := hamiltonian_dirichlet_reference_bound M P (hamiltonianCutCentered W)
    d rho hSymm hDegree hReference hNorm
  rw [hamiltonian_cut_centered_square_sum, hamiltonian_dirichlet_centered_indicator,
    hamiltonian_dirichlet_indicator_boundary M hSymm W] at h
  exact h

end PrimeFactorOscillations

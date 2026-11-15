/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.HamiltonianRevealOrderAverage
import PrimeFactorOscillations.Helpers.HamiltonianRevealSuffix

/-! # A global weighted row-cap permanent upper bound

The full matching measure is retained while the actual row orders
are averaged. Zero matching weights contribute exactly zero.
The sequential denominators, fixed matched entries, suffix supports
and both permutation sums remain in the argument until the bound.
-/

set_option autoImplicit false
set_option Elab.async false

noncomputable section

namespace PrimeFactorOscillations

def hamiltonianRowCapLogBound (n : Nat) (c : Real) : Real :=
  Finset.univ.sum (fun k : Fin (n + 2) =>
    Real.log (c + ((n + 1 - k.val : Nat) : Real) / (n + 1 : Real)))

theorem hamiltonian_row_cap_log_permanent_bound (n : Nat)
    (A : Matrix (Fin (n + 2)) (Fin (n + 2)) Real) (c : Real)
    (hNonneg : forall i j, 0 <= A i j)
    (hRow : forall i, Finset.univ.sum (fun j => A i j) <= 1)
    (hCap : forall i j, A i j <= c)
    (hMass : 0 < Finset.univ.sum (fun sigma : Equiv.Perm (Fin (n + 2)) =>
      Finset.univ.prod (fun i => A i (sigma i)))) :
    Real.log (Finset.univ.sum (fun sigma : Equiv.Perm (Fin (n + 2)) =>
      Finset.univ.prod (fun i => A i (sigma i)))) <= hamiltonianRowCapLogBound n c := by
  let w := fun sigma : Equiv.Perm (Fin (n + 2)) =>
    Finset.univ.prod (fun i => A i (sigma i))
  let P := Finset.univ.sum w
  let m : Real := Fintype.card (Equiv.Perm (Fin (n + 2)))
  let L := hamiltonianRowCapLogBound n c
  let cost := fun (sigma nu : Equiv.Perm (Fin (n + 2))) =>
    Finset.univ.sum (fun k : Fin (n + 2) => Real.log (Finset.univ.sum
      (fun j : Fin (n + 2) => if k <= j then A (nu k) (sigma (nu j)) else 0)))
  have hP : 0 < P := hMass
  have hM : 0 < m := Nat.cast_pos.mpr Fintype.card_pos
  have hW (sigma : Equiv.Perm (Fin (n + 2))) : 0 <= w sigma :=
    Finset.prod_nonneg (fun i _ => hNonneg i (sigma i))
  have hMatching (sigma : Equiv.Perm (Fin (n + 2))) (hw : 0 < w sigma) :
      forall i, 0 < A i (sigma i) := by
    intro i
    by_contra hNot
    have hZero : A i (sigma i) = 0 := le_antisymm (le_of_not_gt hNot) (hNonneg i (sigma i))
    have hProduct : w sigma = 0 := Finset.prod_eq_zero (Finset.mem_univ i) hZero
    rw [hProduct] at hw
    exact (lt_irrefl 0) hw
  have hCost (sigma : Equiv.Perm (Fin (n + 2))) (hw : 0 < w sigma) :
      Finset.univ.sum (fun nu : Equiv.Perm (Fin (n + 2)) => cost sigma nu) <= m * L := by
    unfold cost
    rw [Finset.sum_comm]
    calc
      _ <= Finset.univ.sum (fun k : Fin (n + 2) =>
          m * Real.log (c + ((n + 1 - k.val : Nat) : Real) / (n + 1 : Real))) :=
        Finset.sum_le_sum (fun k _ => hamiltonian_reveal_stage_order_average n A sigma k c
          hNonneg hRow hCap (hMatching sigma hw))
      _ = _ := (Finset.mul_sum _ _ _).symm
  have hWeighted (sigma : Equiv.Perm (Fin (n + 2))) :
      w sigma * Finset.univ.sum (fun nu : Equiv.Perm (Fin (n + 2)) => cost sigma nu) <=
        w sigma * (m * L) := by
    by_cases hZero : w sigma = 0
    case pos => rw [hZero, zero_mul, zero_mul]
    case neg =>
      have hw : 0 < w sigma := lt_of_le_of_ne (hW sigma) (Ne.symm hZero)
      exact mul_le_mul_of_nonneg_left (hCost sigma hw) (hW sigma)
  have hOrdered (nu : Equiv.Perm (Fin (n + 2))) :
      Real.log P * P <= Finset.univ.sum
        (fun sigma : Equiv.Perm (Fin (n + 2)) => w sigma * cost sigma nu) := by
    have h := hamiltonian_permutation_order_log_bound (n + 2) A hNonneg nu hMass
    change Real.log P <= Finset.univ.sum
      (fun sigma : Equiv.Perm (Fin (n + 2)) => w sigma * cost sigma nu) / P at h
    have hScaled := mul_le_mul_of_nonneg_right h (le_of_lt hP)
    have hClear : (Finset.univ.sum
        (fun sigma : Equiv.Perm (Fin (n + 2)) => w sigma * cost sigma nu) / P) * P =
        Finset.univ.sum
          (fun sigma : Equiv.Perm (Fin (n + 2)) => w sigma * cost sigma nu) := by
      field_simp [ne_of_gt hP]
    rw [hClear] at hScaled
    exact hScaled
  have hOrders := Finset.sum_le_sum
    (fun nu (_ : Membership.mem Finset.univ nu) => hOrdered nu)
  have hWeights := Finset.sum_le_sum
    (fun sigma (_ : Membership.mem Finset.univ sigma) => hWeighted sigma)
  have hSwap : Finset.univ.sum (fun nu : Equiv.Perm (Fin (n + 2)) =>
      Finset.univ.sum (fun sigma : Equiv.Perm (Fin (n + 2)) => w sigma * cost sigma nu)) =
      Finset.univ.sum (fun sigma : Equiv.Perm (Fin (n + 2)) =>
        w sigma * Finset.univ.sum (fun nu : Equiv.Perm (Fin (n + 2)) => cost sigma nu)) := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro sigma hs
    exact (Finset.mul_sum _ _ _).symm
  rw [hSwap] at hOrders
  have hLeft : Finset.univ.sum (fun _ : Equiv.Perm (Fin (n + 2)) => Real.log P * P) =
      m * (Real.log P * P) := by
    simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, m]
  have hRight : Finset.univ.sum (fun sigma : Equiv.Perm (Fin (n + 2)) => w sigma * (m * L)) =
      P * (m * L) := (Finset.sum_mul _ _ _).symm
  rw [hLeft] at hOrders
  rw [hRight] at hWeights
  have hBound : (m * P) * Real.log P <= (m * P) * L := by
    nlinarith only [hOrders, hWeights]
  exact le_of_mul_le_mul_left hBound (mul_pos hM hP)

theorem hamiltonian_row_cap_permanent_exponential (n : Nat)
    (A : Matrix (Fin (n + 2)) (Fin (n + 2)) Real) (c : Real)
    (hNonneg : forall i j, 0 <= A i j)
    (hRow : forall i, Finset.univ.sum (fun j => A i j) <= 1)
    (hCap : forall i j, A i j <= c) :
    Finset.univ.sum (fun sigma : Equiv.Perm (Fin (n + 2)) =>
      Finset.univ.prod (fun i => A i (sigma i))) <=
        Real.exp (hamiltonianRowCapLogBound n c) := by
  let P := Finset.univ.sum (fun sigma : Equiv.Perm (Fin (n + 2)) =>
    Finset.univ.prod (fun i => A i (sigma i)))
  have hP : 0 <= P := Finset.sum_nonneg (fun sigma _ =>
    Finset.prod_nonneg (fun i _ => hNonneg i (sigma i)))
  by_cases hZero : P = 0
  case pos =>
    change P <= _
    rw [hZero]
    exact le_of_lt (Real.exp_pos _)
  case neg =>
    have hPositive : 0 < P := lt_of_le_of_ne hP (Ne.symm hZero)
    have h := hamiltonian_row_cap_log_permanent_bound n A c hNonneg hRow hCap hPositive
    have hExp := Real.exp_le_exp.mpr h
    change Real.exp (Real.log P) <= Real.exp (hamiltonianRowCapLogBound n c) at hExp
    rw [Real.exp_log hPositive] at hExp
    exact hExp

end PrimeFactorOscillations

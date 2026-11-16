/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.HamiltonianPrincipalMinorMass

/-! # Complete principal-support mass and the aperiodic ratio tail

The rank partition is exact. Every principal support is retained,
including rank zero, and the exponential tilt is applied only to
the explicitly separated large-support residual.
-/

set_option autoImplicit false
set_option Elab.async false

noncomputable section

namespace PrimeFactorOscillations

variable {Iota : Type*} [Fintype Iota] [DecidableEq Iota]

def hamiltonianPrincipalTiltedMass (M : Matrix Iota Iota Real) (z : Real) : Real :=
  Finset.univ.sum (fun S : Finset Iota =>
    (S.card : Real) * z ^ S.card * abs (principalMinorDet M S))

theorem hamiltonian_principal_tilted_mass_rank_sum
    (M : Matrix Iota Iota Real) (z : Real) :
    hamiltonianPrincipalTiltedMass M z =
      Finset.sum (Finset.range (Fintype.card Iota + 1))
        (fun r => (r : Real) * z ^ r * hamiltonianPrincipalRankMass M r) := by
  have hSet (r : Nat) :
      (Finset.univ : Finset Iota).powersetCard r =
        (Finset.univ : Finset (Finset Iota)).filter (fun S => S.card = r) := by
    ext S
    simp [Finset.mem_powersetCard]
  symm
  calc
    _ = Finset.sum (Finset.range (Fintype.card Iota + 1)) (fun r =>
        Finset.univ.sum (fun S : Finset Iota =>
          if S.card = r then
            (S.card : Real) * z ^ S.card * abs (principalMinorDet M S) else 0)) := by
      apply Finset.sum_congr rfl
      intro r hr
      rw [hamiltonianPrincipalRankMass, Finset.mul_sum, hSet r, Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro S hS
      by_cases h : S.card = r
      case pos => simp only [h, ite_true]
      case neg => simp only [h, ite_false]
    _ = Finset.univ.sum (fun S : Finset Iota =>
        Finset.sum (Finset.range (Fintype.card Iota + 1)) (fun r =>
          if S.card = r then
            (S.card : Real) * z ^ S.card * abs (principalMinorDet M S) else 0)) :=
      Finset.sum_comm
    _ = hamiltonianPrincipalTiltedMass M z := by
      apply Finset.sum_congr rfl
      intro S hS
      have hMem : Membership.mem (Finset.range (Fintype.card Iota + 1)) S.card :=
        Finset.mem_range.mpr (Nat.lt_succ_of_le (Finset.card_le_univ S))
      simp [hMem]

theorem hamiltonian_principal_tilted_mass_bound
    (M : Matrix Iota Iota Real) (c z : Real) (hc : 0 < c)
    (hEntry : forall i j, abs (M i j) <= c) :
    hamiltonianPrincipalTiltedMass M z <=
      2 * Real.exp (16 * Real.exp 2 * ((Fintype.card Iota : Real) * c) ^ 2 * z ^ 2) := by
  rw [hamiltonian_principal_tilted_mass_rank_sum]
  exact hamiltonian_principal_tilted_rank_mass_bound M c z hc hEntry _

theorem hamiltonian_principal_exponential_tail
    (M : Matrix Iota Iota Real) (c R : Real) (hc : 0 < c)
    (hEntry : forall i j, abs (M i j) <= c) :
    (Finset.univ.filter (fun S : Finset Iota => R < (S.card : Real))).sum
        (fun S => (S.card : Real) * Real.exp (S.card : Real) *
          abs (principalMinorDet M S)) <=
      Real.exp (-R) *
        (2 * Real.exp (16 * Real.exp 2 * ((Fintype.card Iota : Real) * c) ^ 2 *
          (Real.exp 2) ^ 2)) := by
  let F := (Finset.univ : Finset (Finset Iota)).filter
    (fun S => R < (S.card : Real))
  have hPoint (S : Finset Iota) (hS : Membership.mem F S) :
      (S.card : Real) * Real.exp (S.card : Real) * abs (principalMinorDet M S) <=
        Real.exp (-R) *
          ((S.card : Real) * (Real.exp 2) ^ S.card * abs (principalMinorDet M S)) := by
    have hR : R < (S.card : Real) := (Finset.mem_filter.mp hS).2
    have hExp : Real.exp (S.card : Real) <=
        Real.exp (-R) * (Real.exp 2) ^ S.card := by
      calc
        _ <= Real.exp (-R + (S.card : Real) * 2) :=
          Real.exp_le_exp.mpr (by linarith only [hR])
        _ = _ := by rw [Real.exp_add, hamiltonian_exp_nat_scalar]
    have h := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hExp (Nat.cast_nonneg S.card))
      (abs_nonneg (principalMinorDet M S))
    calc
      _ <= (S.card : Real) * (Real.exp (-R) * (Real.exp 2) ^ S.card) *
          abs (principalMinorDet M S) := h
      _ = _ := by ring
  have hPositive (S : Finset Iota) :
      0 <= (S.card : Real) * (Real.exp 2) ^ S.card * abs (principalMinorDet M S) :=
    mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (pow_nonneg (Real.exp_pos _).le _))
      (abs_nonneg _)
  have hSubsum :
      F.sum (fun S => (S.card : Real) * (Real.exp 2) ^ S.card *
          abs (principalMinorDet M S)) <=
        hamiltonianPrincipalTiltedMass M (Real.exp 2) :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
      (fun S _ _ => hPositive S)
  calc
    _ <= F.sum (fun S => Real.exp (-R) *
        ((S.card : Real) * (Real.exp 2) ^ S.card * abs (principalMinorDet M S))) :=
      Finset.sum_le_sum hPoint
    _ = Real.exp (-R) * F.sum (fun S =>
        (S.card : Real) * (Real.exp 2) ^ S.card * abs (principalMinorDet M S)) :=
      (Finset.mul_sum _ _ _).symm
    _ <= Real.exp (-R) * hamiltonianPrincipalTiltedMass M (Real.exp 2) :=
      mul_le_mul_of_nonneg_left hSubsum (Real.exp_pos _).le
    _ <= _ := mul_le_mul_of_nonneg_left
      (hamiltonian_principal_tilted_mass_bound M c (Real.exp 2) hc hEntry)
      (Real.exp_pos _).le

end PrimeFactorOscillations

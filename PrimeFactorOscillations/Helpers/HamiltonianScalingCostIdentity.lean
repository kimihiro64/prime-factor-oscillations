/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.HamiltonianBipartiteSupports
import PrimeFactorOscillations.Helpers.HamiltonianBoundaryEquations
import PrimeFactorOscillations.Helpers.HamiltonianDeletedSupportDefect
import PrimeFactorOscillations.Helpers.HamiltonianNonlinearRepair

/-! # The complete signed scaling-cost identity

The actual scaling equations give the full quadratic main term, with
the nonlinear residual retained. Independent deleted supports contribute
their exact common overlap, rather than an unsigned or matched-support
replacement.
-/

set_option autoImplicit false
set_option Elab.async false

noncomputable section

namespace PrimeFactorOscillations

variable {Iota : Type*} [Fintype Iota] [DecidableEq Iota]

theorem hamiltonian_symmetric_mulVec_sum
    (P : Matrix Iota Iota Real) (hSym : forall i j, P i j = P j i) (z : Iota -> Real) :
    Finset.sum Finset.univ (fun i => P.mulVec z i) =
      Finset.sum Finset.univ (fun i => P.mulVec 1 i * z i) := by
  simp only [Matrix.mulVec, dotProduct, Pi.one_apply, mul_one, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  rw [hSym j i]

theorem hamiltonian_scaling_quadratic_cost_identity
    (P : Matrix Iota Iota Real) (hSym : forall i j, P i j = P j i)
    (ell z : Iota -> Real)
    (hDegree : forall i, P.mulVec 1 i = 1 - ell i)
    (hScaling : forall i, (1 + z i) * P.mulVec (1 + z) i = 1) :
    Finset.sum Finset.univ z - Finset.sum Finset.univ (fun i => z i ^ 2) / 2 =
      Finset.sum Finset.univ ell / 2 +
        Finset.sum Finset.univ (fun i => ell i * z i) / 2 -
          Finset.sum Finset.univ
            (fun i => z i * hamiltonianRepairNonlinear P ell z i) / 2 := by
  have hBalance := hamiltonian_symmetric_mulVec_sum P hSym z
  simp only [hDegree] at hBalance
  have hPoint (i : Iota) :
      2 * z i - z i ^ 2 - ell i - ell i * z i +
        z i * hamiltonianRepairNonlinear P ell z i =
      (1 - ell i) * z i - P.mulVec z i := by
    have hi := hScaling i
    rw [Matrix.mulVec_add] at hi
    change (1 + z i) * (P.mulVec 1 i + P.mulVec z i) = 1 at hi
    rw [hDegree i] at hi
    have hF : z i + P.mulVec z i - ell i - ell i * z i + z i * P.mulVec z i = 0 := by
      nlinarith only [hi]
    have hMult : (1 - z i) *
        (z i + P.mulVec z i - ell i - ell i * z i + z i * P.mulVec z i) = 0 := by
      rw [hF, mul_zero]
    change 2 * z i - z i ^ 2 - ell i - ell i * z i +
      z i * (ell i * z i - z i * P.mulVec z i) = _
    nlinarith only [hMult]
  have hZero : Finset.sum Finset.univ
      (fun i => (1 - ell i) * z i - P.mulVec z i) = 0 := by
    rw [Finset.sum_sub_distrib, <- hBalance, sub_self]
  have hSum : Finset.sum Finset.univ (fun i =>
      2 * z i - z i ^ 2 - ell i - ell i * z i +
        z i * hamiltonianRepairNonlinear P ell z i) = 0 :=
    (Finset.sum_congr rfl (fun i _ => hPoint i)).trans hZero
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, <- Finset.mul_sum] at hSum
  linarith only [hSum]

def hamiltonianDeletedOverlap (T : Matrix Iota Iota Real) (S U : Finset Iota) : Real :=
  Finset.sum S (fun i => Finset.sum U (fun j => T i j))

theorem hamiltonianDeletedSupportDefect_deleted_mass
    (T : Matrix Iota Iota Real) (S U : Finset Iota) :
    Finset.sum Finset.univ
      (fun d : S.disjSum U => hamiltonianDeletedSupportDefect T S U d.val) =
        2 * hamiltonianDeletedOverlap T S U := by
  let e := hamiltonianDisjSumEquiv S U
  have hFlip : Finset.sum U (fun j => Finset.sum S (fun i => T i j)) =
      Finset.sum S (fun i => Finset.sum U (fun j => T i j)) := Finset.sum_comm
  have hLeft : Finset.sum Finset.univ (fun i : S => Finset.sum U (fun j => T i.val j)) =
      Finset.sum S (fun i => Finset.sum U (fun j => T i j)) :=
    Finset.sum_coe_sort S (fun i => Finset.sum U (fun j => T i j))
  have hRight : Finset.sum Finset.univ (fun j : U => Finset.sum S (fun i => T i j.val)) =
      Finset.sum U (fun j => Finset.sum S (fun i => T i j)) :=
    Finset.sum_coe_sort U (fun j => Finset.sum S (fun i => T i j))
  calc
    _ = Finset.sum Finset.univ (fun k : Sum S U =>
        hamiltonianDeletedSupportDefect T S U (e k).val) :=
      (Equiv.sum_comp e (fun d => hamiltonianDeletedSupportDefect T S U d.val)).symm
    _ = Finset.sum Finset.univ (fun i : S => Finset.sum U (fun j => T i.val j)) +
        Finset.sum Finset.univ (fun j : U => Finset.sum S (fun i => T i j.val)) := by
      rw [Fintype.sum_sum_type]
      rfl
    _ = Finset.sum S (fun i => Finset.sum U (fun j => T i j)) +
        Finset.sum U (fun j => Finset.sum S (fun i => T i j)) := by rw [hLeft, hRight]
    _ = _ := by rw [hFlip]; dsimp only [hamiltonianDeletedOverlap]; ring

theorem hamiltonianDeletedSupportDefect_retained_mass
    (T : Matrix Iota Iota Real) (S U : Finset Iota) (hCard : S.card = U.card)
    (hRow : forall i, Finset.sum Finset.univ (fun j => T i j) = 1)
    (hCol : forall j, Finset.sum Finset.univ (fun i => T i j) = 1) :
    Finset.sum Finset.univ
      (fun i : (Compl.compl (S.disjSum U) : Finset (Sum Iota Iota)) =>
        hamiltonianDeletedSupportDefect T S U i.val) =
      2 * ((U.card : Real) - hamiltonianDeletedOverlap T S U) := by
  let ell := hamiltonianDeletedSupportDefect T S U
  have hHalves := hamiltonianDeletedSupportDefect_half_masses T S U hRow hCol
  have hFull : Finset.sum Finset.univ ell = 2 * (U.card : Real) := by
    rw [Fintype.sum_sum_type]
    change Finset.sum Finset.univ (fun i => hamiltonianDeletedSupportDefect T S U (Sum.inl i)) +
      Finset.sum Finset.univ (fun j => hamiltonianDeletedSupportDefect T S U (Sum.inr j)) = _
    rw [hHalves.1, hHalves.2, hCard]
    ring
  have hPart := hamiltonian_sum_support_partition ell (S.disjSum U)
  rw [hFull, hamiltonianDeletedSupportDefect_deleted_mass T S U] at hPart
  linarith only [hPart]

end PrimeFactorOscillations

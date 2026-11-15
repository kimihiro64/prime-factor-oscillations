/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.HamiltonianBipartiteSupports
import PrimeFactorOscillations.Helpers.HamiltonianBoundaryParityResidual

/-! # Exact scaling conservation on the actual retained coordinates

The full double sum cancels by its signed transpose, with every cross
term present. Equal deleted part sizes give exactly zero retained parity
mass. This proves that a parity-shaped scaling residual is zero.
-/

set_option autoImplicit false
set_option Elab.async false

noncomputable section

namespace PrimeFactorOscillations

variable {Iota : Type*} [Fintype Iota] [DecidableEq Iota]

theorem hamiltonian_signed_scaling_conservation
    (P : Matrix Iota Iota Real) (sign x : Iota -> Real)
    (hAnti : forall i j, sign i * P i j = -(sign j * P j i))
    (hMass : Finset.sum Finset.univ sign = 0) :
    Finset.sum Finset.univ
      (fun i => sign i * (x i * P.mulVec x i - 1)) = 0 := by
  let W := Finset.sum Finset.univ (fun i => sign i * (x i * P.mulVec x i))
  have hExpand : W = Finset.sum Finset.univ (fun i => Finset.sum Finset.univ
      (fun j => sign i * (x i * (P i j * x j)))) := by
    dsimp only [W, Matrix.mulVec, dotProduct]
    simp_rw [Finset.mul_sum]
  have hPair (i j : Iota) :
      sign i * (x i * (P i j * x j)) = -(sign j * (x j * (P j i * x i))) := by
    calc
      _ = (sign i * P i j) * (x i * x j) := by ring
      _ = (-(sign j * P j i)) * (x i * x j) := by rw [hAnti i j]
      _ = _ := by ring
  have hNeg : W = -W := by
    calc
      _ = Finset.sum Finset.univ (fun i => Finset.sum Finset.univ
          (fun j => sign i * (x i * (P i j * x j)))) := hExpand
      _ = Finset.sum Finset.univ (fun i => Finset.sum Finset.univ
          (fun j => -(sign j * (x j * (P j i * x i))))) := by
        apply Finset.sum_congr rfl
        intro i hi
        exact Finset.sum_congr rfl (fun j _ => hPair i j)
      _ = -(Finset.sum Finset.univ (fun i => Finset.sum Finset.univ
          (fun j => sign j * (x j * (P j i * x i))))) := by
        simp only [Finset.sum_neg_distrib]
      _ = -W := by rw [Finset.sum_comm, <- hExpand]
  have hW : W = 0 := by linarith only [hNeg]
  simp only [mul_sub, mul_one, Finset.sum_sub_distrib]
  change W - Finset.sum Finset.univ sign = 0
  rw [hW, hMass, sub_self]

theorem hamiltonian_retained_parity_mass (S U : Finset Iota) (hCard : S.card = U.card) :
    Finset.sum Finset.univ
      (fun i : (Compl.compl (S.disjSum U) : Finset (Sum Iota Iota)) =>
        hamiltonianParitySign i.val) = 0 := by
  let D := S.disjSum U
  let e := hamiltonianDisjSumEquiv S U
  have hFull : Finset.sum Finset.univ (hamiltonianParitySign (Iota := Iota)) = 0 := by
    simp [hamiltonianParitySign, Fintype.sum_sum_type]
  have hD : Finset.sum Finset.univ (fun d : D => hamiltonianParitySign d.val) = 0 := by
    calc
      _ = Finset.sum Finset.univ
          (fun k : Sum S U => hamiltonianParitySign (e k).val) :=
        (Equiv.sum_comp e (fun d => hamiltonianParitySign d.val)).symm
      _ = 0 := by
        simp [e, hamiltonianDisjSumEquiv, Fintype.sum_sum_type,
          hamiltonianParitySign, hCard]
  have hPart := hamiltonian_sum_support_partition (hamiltonianParitySign (Iota := Iota)) D
  rw [hFull, hD, zero_add] at hPart
  exact hPart.symm

theorem hamiltonian_retained_scaling_conservation
    (T : Matrix Iota Iota Real) (S U : Finset Iota) (hCard : S.card = U.card)
    (x : forall _i : (Compl.compl (S.disjSum U) : Finset (Sum Iota Iota)), Real) :
    let R : Finset (Sum Iota Iota) := Compl.compl (S.disjSum U)
    let PR := (bipartiteLift T).submatrix (fun i : R => i.val) (fun i : R => i.val)
    Finset.sum Finset.univ
      (fun i : R => hamiltonianParitySign i.val * (x i * PR.mulVec x i - 1)) = 0 := by
  let R : Finset (Sum Iota Iota) := Compl.compl (S.disjSum U)
  let PR := (bipartiteLift T).submatrix (fun i : R => i.val) (fun i : R => i.val)
  have hFull (i j : Sum Iota Iota) :
      hamiltonianParitySign i * bipartiteLift T i j =
        -(hamiltonianParitySign j * bipartiteLift T j i) := by
    cases i <;> cases j <;>
      simp [hamiltonianParitySign, bipartiteLift, Matrix.fromBlocks, Matrix.transpose_apply]
  exact hamiltonian_signed_scaling_conservation PR
    (fun i : R => hamiltonianParitySign i.val) x (fun i j => hFull i.val j.val)
    (hamiltonian_retained_parity_mass S U hCard)

theorem hamiltonian_retained_scaling_parity_zero
    (T : Matrix Iota Iota Real) (S U : Finset Iota) (hCard : S.card = U.card)
    (hPositive : 0 < (Compl.compl (S.disjSum U) : Finset (Sum Iota Iota)).card)
    (x : forall _i : (Compl.compl (S.disjSum U) : Finset (Sum Iota Iota)), Real)
    (c : Real)
    (hResidual : forall i : (Compl.compl (S.disjSum U) : Finset (Sum Iota Iota)),
      x i * ((bipartiteLift T).submatrix
        (fun j : (Compl.compl (S.disjSum U) : Finset (Sum Iota Iota)) => j.val)
        (fun j : (Compl.compl (S.disjSum U) : Finset (Sum Iota Iota)) => j.val)).mulVec x i - 1 =
          hamiltonianParitySign i.val * c) :
    c = 0 /\ forall i : (Compl.compl (S.disjSum U) : Finset (Sum Iota Iota)),
      x i * ((bipartiteLift T).submatrix
        (fun j : (Compl.compl (S.disjSum U) : Finset (Sum Iota Iota)) => j.val)
        (fun j : (Compl.compl (S.disjSum U) : Finset (Sum Iota Iota)) => j.val)).mulVec x i = 1 := by
  let R : Finset (Sum Iota Iota) := Compl.compl (S.disjSum U)
  have h := hamiltonian_retained_scaling_conservation T S U hCard x
  change Finset.sum Finset.univ (fun i : R =>
    hamiltonianParitySign i.val * (x i * _ - 1)) = 0 at h
  simp only [hResidual] at h
  have hEach (i : R) :
      hamiltonianParitySign i.val * (hamiltonianParitySign i.val * c) = c := by
    cases i.val <;> simp [hamiltonianParitySign]
  simp only [hEach, Finset.sum_const, Finset.card_univ, Fintype.card_coe, nsmul_eq_mul] at h
  have hN : 0 < (R.card : Real) := Nat.cast_pos.mpr hPositive
  have hc : c = 0 := by nlinarith only [h, hN]
  refine And.intro hc ?_
  intro i
  have hi := hResidual i
  rw [hc, mul_zero] at hi
  exact sub_eq_zero.mp hi

end PrimeFactorOscillations

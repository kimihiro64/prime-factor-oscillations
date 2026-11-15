/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.HamiltonianBoundaryEquations
import PrimeFactorOscillations.Helpers.HamiltonianRepairInverse

/-! # The exact parity residual of the actual Schur solve

The boundary compensation is retained in the scalar residual. This
identity is the consumer that lets exact balanced scaling conservation
upgrade a nonlinear fixed point to the full stochastic equations.
-/

set_option autoImplicit false
set_option Elab.async false

open scoped Matrix.Norms.L2Operator

noncomputable section

namespace PrimeFactorOscillations

variable {Iota : Type*} [Fintype Iota] [DecidableEq Iota]

theorem hamiltonianParityProjection_submatrix_mulVec
    {Rows Cols : Type*} [Fintype Cols] (q : Real)
    (f : Rows -> Sum Iota Iota) (g : Cols -> Sum Iota Iota)
    (v : Cols -> Real) (i : Rows) :
    ((hamiltonianParityProjection q).submatrix f g).mulVec v i =
      q / 2 * hamiltonianParitySign (f i) *
        Finset.sum Finset.univ (fun j => hamiltonianParitySign (g j) * v j) := by
  change Finset.sum Finset.univ
    (fun j => (q / 2 * hamiltonianParitySign (f i) * hamiltonianParitySign (g j)) * v j) = _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  ring

variable [Nonempty Iota]

theorem stochastic_boundary_inverse_residual
    (T : Matrix Iota Iota Real) (D : Finset (Sum Iota Iota))
    (q a rho : Real) (hq : (Fintype.card Iota : Real) * q = 1) (ha : 1 <= a)
    (hRow : forall i, Finset.sum Finset.univ (fun j => T i j) = 1)
    (hCol : forall j, Finset.sum Finset.univ (fun i => T i j) = 1)
    (hNonneg : forall i j, 0 <= T i j) (hUpper : forall i j, T i j <= a * q)
    (hNorm : norm (centeredKernel T q) <= rho) (hRho : rho < 1)
    (hSmall : (D.card : Real) * (4 * a * q) <= (1 - rho) / 2)
    (w : forall _i : (Compl.compl D : Finset (Sum Iota Iota)), Real) :
    exists c : Real, forall i : (Compl.compl D : Finset (Sum Iota Iota)),
      (((1 : Matrix (Sum Iota Iota) (Sum Iota Iota) Real) + bipartiteLift T).submatrix
          (fun r : (Compl.compl D : Finset (Sum Iota Iota)) => r.val)
          (fun r : (Compl.compl D : Finset (Sum Iota Iota)) => r.val)).mulVec
        ((hamiltonianBoundaryKernel (hamiltonianRepairKernel T q) D).mulVec w) i =
          w i - hamiltonianParitySign i.val * c := by
  let R : Finset (Sum Iota Iota) := Compl.compl D
  let rr := fun i : R => (i.val : Sum Iota Iota)
  let rd := fun d : D => (d.val : Sum Iota Iota)
  let H : Matrix (Sum Iota Iota) (Sum Iota Iota) Real := 1 + bipartiteLift T
  let K := hamiltonianRepairKernel T q
  let G := hamiltonianBoundaryKernel K D
  let V := hamiltonianParityProjection (Iota := Iota) q
  let J := Ring.inverse (K.submatrix rd rd)
  let B := K.submatrix rd rr
  let v := J.mulVec (B.mulVec w)
  have hHK : H * K = 1 - V :=
    stochastic_repair_kernel_right_inverse T q rho hq hRow hCol hNorm hRho
  have hUnit : IsUnit (K.submatrix rd rd) :=
    (stochastic_deleted_block_inverse T D q a rho hq ha
      hRow hCol hNonneg hUpper hNorm hRho hSmall).1
  have hMat := hamiltonianBoundaryKernel_inverse_equation H K D hUnit
  change H.submatrix rr rr * G =
    (H * K).submatrix rr rr - (H * K).submatrix rr rd * J * B at hMat
  rw [hHK] at hMat
  have hRR : ((1 : Matrix (Sum Iota Iota) (Sum Iota Iota) Real) - V).submatrix rr rr =
      1 - V.submatrix rr rr := by
    apply Matrix.ext
    intro i j
    simp only [Matrix.submatrix_apply, Matrix.sub_apply, Matrix.one_apply, rr,
      Subtype.ext_iff]
  have hRD : ((1 : Matrix (Sum Iota Iota) (Sum Iota Iota) Real) - V).submatrix rr rd =
      -(V.submatrix rr rd) := by
    apply Matrix.ext
    intro i d
    have hne : Not (i.val = d.val) := by
      intro heq
      have hd : Membership.mem D i.val := by rw [heq]; exact d.property
      exact (Finset.mem_compl.mp i.property) hd
    simp only [Matrix.submatrix_apply, Matrix.sub_apply, Matrix.one_apply, rr, rd,
      if_neg hne, zero_sub, Matrix.neg_apply]
  rw [hRR, hRD] at hMat
  have hVec : (H.submatrix rr rr).mulVec (G.mulVec w) =
      w - (V.submatrix rr rr).mulVec w + (V.submatrix rr rd).mulVec v := by
    rw [Matrix.mulVec_mulVec, hMat]
    simpa only [Matrix.sub_mulVec, Matrix.add_mulVec, Matrix.one_mulVec,
      Matrix.neg_mul, Matrix.neg_mulVec, <- Matrix.mulVec_mulVec, sub_neg_eq_add, v]
  let leftMass := Finset.sum Finset.univ (fun j : R => hamiltonianParitySign j.val * w j)
  let removedMass := Finset.sum Finset.univ (fun d : D => hamiltonianParitySign d.val * v d)
  refine Exists.intro (q / 2 * (leftMass - removedMass)) ?_
  intro i
  change (H.submatrix rr rr).mulVec (G.mulVec w) i =
    w i - hamiltonianParitySign i.val * (q / 2 * (leftMass - removedMass))
  rw [hVec]
  change w i - (V.submatrix rr rr).mulVec w i + (V.submatrix rr rd).mulVec v i = _
  rw [hamiltonianParityProjection_submatrix_mulVec q rr rr w i,
    hamiltonianParityProjection_submatrix_mulVec q rr rd v i]
  change w i - q / 2 * hamiltonianParitySign i.val * leftMass +
    q / 2 * hamiltonianParitySign i.val * removedMass = _
  ring

end PrimeFactorOscillations

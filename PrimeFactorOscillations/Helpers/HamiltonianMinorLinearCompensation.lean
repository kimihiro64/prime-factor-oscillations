/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.HamiltonianMinorQuadraticCompensation

/-! # Full signed first-order compensation in the minor exponent

The overlap, quadratic defect, diagonal trace, linear determinant term
and rank-normalizer shift cancel before any remainder is bounded.
-/

set_option autoImplicit false
set_option Elab.async false

open scoped Matrix.Norms.L2Operator

noncomputable section

namespace PrimeFactorOscillations

variable {Iota : Type*} [Fintype Iota] [DecidableEq Iota] [Nonempty Iota]

theorem stochastic_deleted_linear_compensation
    (T : Matrix Iota Iota Real) (S U : Finset Iota) (hCard : S.card = U.card)
    (q rho : Real) (hq : (Fintype.card Iota : Real) * q = 1)
    (hRow : forall i, Finset.univ.sum (fun j => T i j) = 1)
    (hCol : forall j, Finset.univ.sum (fun i => T i j) = 1)
    (hNorm : norm (centeredKernel T q) <= rho) (hRho : rho < 1) :
    let D := S.disjSum U
    let u := hamiltonianDeletedSupportIndicator S U
    let ell := hamiltonianDeletedSupportDefect T S U
    let K := hamiltonianRepairKernel T q
    let G := resolventCovariance (bipartiteLift (centeredKernel T q))
    let h := fun i => -G i i
    let v := fun i => (1 / 2 : Real) * h i - K.mulVec h i
    Finset.univ.sum (fun d : D => G d.val d.val) + 2 * dotProduct h (K.mulVec ell) =
      2 * dotProduct v u := by
  let D := S.disjSum U
  let u := hamiltonianDeletedSupportIndicator S U
  let ell := hamiltonianDeletedSupportDefect T S U
  let P := bipartiteLift T
  let K := hamiltonianRepairKernel T q
  let G := resolventCovariance (bipartiteLift (centeredKernel T q))
  let h := fun i => -G i i
  let v := fun i => (1 / 2 : Real) * h i - K.mulVec h i
  have hEll : ell = P.mulVec u := hamiltonianDeletedSupportDefect_eq_mulVec T S U
  have hNull := (hamiltonian_deleted_projection_pairings S U hCard q).1
  have hKell : K.mulVec ell = u - K.mulVec u := by
    rw [hEll, Matrix.mulVec_mulVec,
      stochastic_repair_kernel_mul_left T q rho hq hRow hCol hNorm hRho,
      Matrix.sub_mulVec, Matrix.sub_mulVec, Matrix.one_mulVec, hNull, sub_zero]
  have hSym (i j : Sum Iota Iota) : K i j = K j i :=
    congrArg (fun A => A j i) (stochastic_repair_kernel_transpose T q rho hNorm hRho)
  have hInner : dotProduct h (K.mulVec u) = dotProduct (K.mulVec h) u :=
    hamiltonian_symmetric_dot_mulVec K hSym h u
  have hTrace : dotProduct h u = -Finset.univ.sum (fun d : D => G d.val d.val) := by
    calc
      _ = -dotProduct u (fun i => G i i) := by
        simp only [dotProduct, <- Finset.sum_neg_distrib]
        apply Finset.sum_congr rfl
        intro i hi
        dsimp only [h]
        ring
      _ = _ := by rw [hamiltonian_deleted_indicator_dot_sum]
  have hDist : dotProduct h (K.mulVec ell) = dotProduct h u - dotProduct (K.mulVec h) u := by
    rw [hKell]
    calc
      _ = dotProduct h u - dotProduct h (K.mulVec u) := by
        simp only [dotProduct, Pi.sub_apply, mul_sub, Finset.sum_sub_distrib]
      _ = _ := by rw [hInner]
  have hV : dotProduct v u = (1 / 2 : Real) * dotProduct h u - dotProduct (K.mulVec h) u := by
    simp only [v, dotProduct, sub_mul, Finset.sum_sub_distrib, Finset.mul_sum, mul_assoc]
  change Finset.univ.sum (fun d : D => G d.val d.val) + 2 * dotProduct h (K.mulVec ell) =
    2 * dotProduct v u
  rw [hDist, hV, hTrace]
  ring

theorem stochastic_deleted_full_first_order_compensation
    (T : Matrix Iota Iota Real) (S U : Finset Iota) (hCard : S.card = U.card)
    (q rho : Real) (hq : (Fintype.card Iota : Real) * q = 1)
    (hRow : forall i, Finset.univ.sum (fun j => T i j) = 1)
    (hCol : forall j, Finset.univ.sum (fun i => T i j) = 1)
    (hNorm : norm (centeredKernel T q) <= rho) (hRho : rho < 1) :
    let D := S.disjSum U
    let u := hamiltonianDeletedSupportIndicator S U
    let ell := hamiltonianDeletedSupportDefect T S U
    let K := hamiltonianRepairKernel T q
    let G := resolventCovariance (bipartiteLift (centeredKernel T q))
    let h := fun i => -G i i
    let v := fun i => (1 / 2 : Real) * h i - K.mulVec h i
    2 * hamiltonianDeletedOverlap T S U - dotProduct ell (K.mulVec ell) +
      Finset.univ.sum (fun d : D => G d.val d.val) +
        2 * dotProduct h (K.mulVec ell) - (U.card : Real) * q =
      (U.card : Real) * ((U.card : Real) - 1) * q +
        dotProduct u (G.mulVec u) + 2 * dotProduct v u := by
  let D := S.disjSum U
  let u := hamiltonianDeletedSupportIndicator S U
  let ell := hamiltonianDeletedSupportDefect T S U
  let K := hamiltonianRepairKernel T q
  let G := resolventCovariance (bipartiteLift (centeredKernel T q))
  let h := fun i => -G i i
  let v := fun i => (1 / 2 : Real) * h i - K.mulVec h i
  have hQuadratic := stochastic_deleted_overlap_quadratic_cancellation T S U hCard q rho
    hq hRow hCol hNorm hRho
  have hLinear := stochastic_deleted_linear_compensation T S U hCard q rho
    hq hRow hCol hNorm hRho
  change 2 * hamiltonianDeletedOverlap T S U - dotProduct ell (K.mulVec ell) +
    Finset.univ.sum (fun d : D => G d.val d.val) + 2 * dotProduct h (K.mulVec ell) -
      (U.card : Real) * q =
    (U.card : Real) * ((U.card : Real) - 1) * q +
      dotProduct u (G.mulVec u) + 2 * dotProduct v u
  nlinarith only [hQuadratic, hLinear]

end PrimeFactorOscillations

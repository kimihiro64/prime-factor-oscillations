/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.HamiltonianRepairSymmetry
import PrimeFactorOscillations.Helpers.HamiltonianScalingCostIdentity
import PrimeFactorOscillations.Helpers.HamiltonianScalingResidualEquation

/-! # Exact signed quadratic cancellation for independent deleted supports

Every overlap and the parity and constant projections are retained.
This is the cancellation between the scaling and determinant costs
in the actual two-power minor ratio.
-/

set_option autoImplicit false
set_option Elab.async false

open scoped Matrix.Norms.L2Operator

noncomputable section

namespace PrimeFactorOscillations

variable {Iota : Type*} [Fintype Iota] [DecidableEq Iota]

theorem hamiltonian_symmetric_dot_mulVec (M : Matrix Iota Iota Real)
    (hSym : forall i j, M i j = M j i) (x y : Iota -> Real) :
    dotProduct x (M.mulVec y) = dotProduct (M.mulVec x) y := by
  simp only [dotProduct, Matrix.mulVec, Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j hj
  apply Finset.sum_congr rfl
  intro i hi
  rw [hSym i j]
  ring

theorem hamiltonian_deleted_indicator_dot_sum (S U : Finset Iota)
    (f : Sum Iota Iota -> Real) :
    dotProduct (hamiltonianDeletedSupportIndicator S U) f =
      Finset.univ.sum (fun d : S.disjSum U => f d.val) := by
  let D := S.disjSum U
  let u := hamiltonianDeletedSupportIndicator S U
  have hU (d : D) : u d.val = 1 := by
    dsimp only [u]
    rw [hamiltonianDeletedSupportIndicator_disjSum]
    exact if_pos d.property
  have hR (j : (Compl.compl D : Finset (Sum Iota Iota))) : u j.val = 0 := by
    dsimp only [u]
    rw [hamiltonianDeletedSupportIndicator_disjSum]
    exact if_neg (Finset.mem_compl.mp j.property)
  have h := hamiltonian_sum_support_partition (fun i => u i * f i) D
  change Finset.univ.sum (fun i => u i * f i) = _
  simpa only [hU, hR, one_mul, zero_mul, Finset.sum_const_zero, add_zero] using h

theorem hamiltonian_deleted_indicator_pairings (S U : Finset Iota) (hCard : S.card = U.card) :
    let u := hamiltonianDeletedSupportIndicator S U
    dotProduct u u = 2 * (U.card : Real) /\
    Finset.univ.sum u = 2 * (U.card : Real) /\
    Finset.univ.sum (fun i => hamiltonianParitySign i * u i) = 0 := by
  let D := S.disjSum U
  let u := hamiltonianDeletedSupportIndicator S U
  have hCardD : (Fintype.card D : Real) = 2 * (U.card : Real) := by
    simp only [D, Fintype.card_coe, Finset.card_disjSum, hCard, Nat.cast_add]
    ring
  have hU (d : D) : u d.val = 1 := by
    dsimp only [u]
    rw [hamiltonianDeletedSupportIndicator_disjSum]
    exact if_pos d.property
  have hUU : dotProduct u u = 2 * (U.card : Real) := by
    rw [hamiltonian_deleted_indicator_dot_sum]
    simp only [hU, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one]
    exact hCardD
  have hMass : Finset.univ.sum u = 2 * (U.card : Real) := by
    have h := hamiltonian_deleted_indicator_dot_sum S U (fun _ => (1 : Real))
    have hMass0 : Finset.univ.sum u = (Fintype.card D : Real) := by
      simpa only [dotProduct, mul_one, Finset.sum_const, Finset.card_univ,
        nsmul_eq_mul] using h
    exact hMass0.trans hCardD
  have hParityDot : dotProduct u hamiltonianParitySign = 0 := by
    let e := hamiltonianDisjSumEquiv S U
    calc
      _ = Finset.univ.sum (fun d : D => hamiltonianParitySign d.val) :=
        hamiltonian_deleted_indicator_dot_sum S U hamiltonianParitySign
      _ = Finset.univ.sum (fun d : Sum S U => hamiltonianParitySign (e d).val) :=
        (Equiv.sum_comp e (fun d : D => hamiltonianParitySign d.val)).symm
      _ = (S.card : Real) - (U.card : Real) := by
        simp [e, hamiltonianDisjSumEquiv, hamiltonianParitySign, Fintype.sum_sum_type, sub_eq_add_neg]
      _ = 0 := by rw [hCard]; ring
  have hParity : Finset.univ.sum (fun i => hamiltonianParitySign i * u i) = 0 := by
    calc
      _ = dotProduct u hamiltonianParitySign := by
        apply Finset.sum_congr rfl
        intro i hi
        ring
      _ = 0 := hParityDot
  exact And.intro hUU (And.intro hMass hParity)

theorem hamiltonian_deleted_projection_pairings
    (S U : Finset Iota) (hCard : S.card = U.card) (q : Real) :
    let u := hamiltonianDeletedSupportIndicator S U
    (hamiltonianParityProjection q).mulVec u = 0 /\
    dotProduct u ((hamiltonianRepairProjection q).mulVec u) = (U.card : Real) ^ 2 * q := by
  let u := hamiltonianDeletedSupportIndicator S U
  have hData := hamiltonian_deleted_indicator_pairings S U hCard
  have hMass : Finset.univ.sum u = 2 * (U.card : Real) := hData.2.1
  have hParity : Finset.univ.sum (fun i => hamiltonianParitySign i * u i) = 0 := hData.2.2
  have hNull : (hamiltonianParityProjection q).mulVec u = 0 := by
    funext i
    calc
      _ = (q / 2 * hamiltonianParitySign i) *
          Finset.univ.sum (fun j => hamiltonianParitySign j * u j) := by
        simp only [Matrix.mulVec, dotProduct, hamiltonianParityProjection, Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro j hj
        ring
      _ = 0 := by rw [hParity, mul_zero]
  have hRepair (i : Sum Iota Iota) :
      (hamiltonianRepairProjection q).mulVec u i = q * (U.card : Real) / 2 := by
    calc
      _ = q / 4 * Finset.univ.sum u +
          (q / 2 * hamiltonianParitySign i) *
            Finset.univ.sum (fun j => hamiltonianParitySign j * u j) := by
        simp only [Matrix.mulVec, dotProduct, hamiltonianRepairProjection, Finset.mul_sum,
          <- Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro j hj
        ring
      _ = _ := by rw [hMass, hParity]; ring
  refine And.intro hNull ?_
  change Finset.univ.sum (fun i => u i * (hamiltonianRepairProjection q).mulVec u i) = _
  simp only [hRepair, <- Finset.sum_mul, hMass]
  ring

variable [Nonempty Iota]

theorem stochastic_repair_kernel_mul_right (T : Matrix Iota Iota Real)
    (q rho : Real) (hq : (Fintype.card Iota : Real) * q = 1)
    (hRow : forall i, Finset.univ.sum (fun j => T i j) = 1)
    (hCol : forall j, Finset.univ.sum (fun i => T i j) = 1)
    (hNorm : norm (centeredKernel T q) <= rho) (hRho : rho < 1) :
    bipartiteLift T * hamiltonianRepairKernel T q =
      1 - hamiltonianRepairKernel T q - hamiltonianParityProjection q := by
  have h := stochastic_repair_kernel_right_inverse T q rho hq hRow hCol hNorm hRho
  rw [add_mul, one_mul] at h
  calc
    _ = (hamiltonianRepairKernel T q + bipartiteLift T * hamiltonianRepairKernel T q) -
        hamiltonianRepairKernel T q := by abel
    _ = _ := by rw [h]; abel

theorem stochastic_repair_kernel_mul_left (T : Matrix Iota Iota Real)
    (q rho : Real) (hq : (Fintype.card Iota : Real) * q = 1)
    (hRow : forall i, Finset.univ.sum (fun j => T i j) = 1)
    (hCol : forall j, Finset.univ.sum (fun i => T i j) = 1)
    (hNorm : norm (centeredKernel T q) <= rho) (hRho : rho < 1) :
    hamiltonianRepairKernel T q * bipartiteLift T =
      1 - hamiltonianRepairKernel T q - hamiltonianParityProjection q := by
  have hP : (bipartiteLift T).transpose = bipartiteLift T := by
    apply Matrix.ext
    intro i j
    cases i <;> cases j <;> rfl
  have hS : (hamiltonianParityProjection (Iota := Iota) q).transpose =
      hamiltonianParityProjection q := by
    apply Matrix.ext
    intro i j
    simp only [Matrix.transpose_apply, hamiltonianParityProjection]
    ring
  have h := congrArg Matrix.transpose
    (stochastic_repair_kernel_mul_right T q rho hq hRow hCol hNorm hRho)
  simpa only [Matrix.transpose_mul, hP, stochastic_repair_kernel_transpose T q rho hNorm hRho,
    Matrix.transpose_sub, Matrix.transpose_one, hS] using h

theorem stochastic_parity_projection_mul_kernel (T : Matrix Iota Iota Real)
    (q : Real)
    (hRow : forall i, Finset.univ.sum (fun j => T i j) = 1)
    (hCol : forall j, Finset.univ.sum (fun i => T i j) = 1) :
    hamiltonianParityProjection q * bipartiteLift T = -hamiltonianParityProjection q := by
  apply Matrix.ext
  intro i j
  cases i <;> cases j <;>
    simp [Matrix.mul_apply, Fintype.sum_sum_type, hamiltonianParityProjection,
      hamiltonianParitySign, bipartiteLift, Matrix.fromBlocks, Matrix.transpose_apply,
      <- Finset.mul_sum, <- Finset.sum_mul, hRow, hCol] <;> ring

theorem stochastic_repair_kernel_sandwich (T : Matrix Iota Iota Real)
    (q rho : Real) (hq : (Fintype.card Iota : Real) * q = 1)
    (hRow : forall i, Finset.univ.sum (fun j => T i j) = 1)
    (hCol : forall j, Finset.univ.sum (fun i => T i j) = 1)
    (hNorm : norm (centeredKernel T q) <= rho) (hRho : rho < 1) :
    bipartiteLift T * hamiltonianRepairKernel T q * bipartiteLift T =
      bipartiteLift T - 1 + hamiltonianRepairKernel T q +
        HSMul.hSMul (2 : Real) (hamiltonianParityProjection q) := by
  rw [stochastic_repair_kernel_mul_right T q rho hq hRow hCol hNorm hRho,
    sub_mul, sub_mul, one_mul,
    stochastic_repair_kernel_mul_left T q rho hq hRow hCol hNorm hRho,
    stochastic_parity_projection_mul_kernel T q hRow hCol, two_smul]
  abel

theorem stochastic_deleted_repair_quadratic
    (T : Matrix Iota Iota Real) (S U : Finset Iota) (hCard : S.card = U.card)
    (q rho : Real) (hNorm : norm (centeredKernel T q) <= rho) (hRho : rho < 1) :
    let u := hamiltonianDeletedSupportIndicator S U
    let G := resolventCovariance (bipartiteLift (centeredKernel T q))
    dotProduct u ((hamiltonianRepairKernel T q).mulVec u) =
      2 * (U.card : Real) - dotProduct u (G.mulVec u) - (U.card : Real) ^ 2 * q := by
  let u := hamiltonianDeletedSupportIndicator S U
  let G := resolventCovariance (bipartiteLift (centeredKernel T q))
  let K := hamiltonianRepairKernel T q
  let H := hamiltonianRepairProjection (Iota := Iota) q
  have hVector : K.mulVec u = u - G.mulVec u - H.mulVec u := by
    dsimp only [K]
    rw [hamiltonianRepairKernel_covariance T q rho hNorm hRho,
      Matrix.sub_mulVec, Matrix.sub_mulVec, Matrix.one_mulVec]
  have hPair : dotProduct u (K.mulVec u) =
      dotProduct u u - dotProduct u (G.mulVec u) - dotProduct u (H.mulVec u) := by
    rw [hVector]
    simp only [dotProduct, Pi.sub_apply, mul_sub, Finset.sum_sub_distrib]
  change dotProduct u (K.mulVec u) = 2 * (U.card : Real) - dotProduct u (G.mulVec u) - (U.card : Real) ^ 2 * q
  rw [hPair, (hamiltonian_deleted_indicator_pairings S U hCard).1,
    (hamiltonian_deleted_projection_pairings S U hCard q).2]

theorem stochastic_deleted_overlap_quadratic_cancellation
    (T : Matrix Iota Iota Real) (S U : Finset Iota) (hCard : S.card = U.card)
    (q rho : Real) (hq : (Fintype.card Iota : Real) * q = 1)
    (hRow : forall i, Finset.univ.sum (fun j => T i j) = 1)
    (hCol : forall j, Finset.univ.sum (fun i => T i j) = 1)
    (hNorm : norm (centeredKernel T q) <= rho) (hRho : rho < 1) :
    let u := hamiltonianDeletedSupportIndicator S U
    let ell := hamiltonianDeletedSupportDefect T S U
    let K := hamiltonianRepairKernel T q
    let G := resolventCovariance (bipartiteLift (centeredKernel T q))
    2 * hamiltonianDeletedOverlap T S U - dotProduct ell (K.mulVec ell) =
      dotProduct u (G.mulVec u) + (U.card : Real) ^ 2 * q := by
  let P := bipartiteLift T
  let u := hamiltonianDeletedSupportIndicator S U
  let ell := hamiltonianDeletedSupportDefect T S U
  let K := hamiltonianRepairKernel T q
  let G := resolventCovariance (bipartiteLift (centeredKernel T q))
  let V := hamiltonianParityProjection (Iota := Iota) q
  have hP (i j : Sum Iota Iota) : P i j = P j i := by cases i <;> cases j <;> rfl
  have hEll : ell = P.mulVec u := hamiltonianDeletedSupportDefect_eq_mulVec T S U
  have hUP : dotProduct u (P.mulVec u) = 2 * hamiltonianDeletedOverlap T S U := by
    rw [<- hEll, hamiltonian_deleted_indicator_dot_sum]
    exact hamiltonianDeletedSupportDefect_deleted_mass T S U
  have hUU := (hamiltonian_deleted_indicator_pairings S U hCard).1
  have hNull := (hamiltonian_deleted_projection_pairings S U hCard q).1
  have hQuad := stochastic_deleted_repair_quadratic T S U hCard q rho hNorm hRho
  have hPull : dotProduct ell (K.mulVec ell) =
      dotProduct u ((P * K * P).mulVec u) := by
    rw [hEll, <- hamiltonian_symmetric_dot_mulVec P hP u (K.mulVec (P.mulVec u)),
      Matrix.mulVec_mulVec, Matrix.mulVec_mulVec]
  have hExpand : dotProduct u ((P * K * P).mulVec u) =
      dotProduct u (P.mulVec u) - dotProduct u u + dotProduct u (K.mulVec u) := by
    have hZero (i : Sum Iota Iota) : (hamiltonianParityProjection q).mulVec u i = 0 :=
      congrFun hNull i
    rw [stochastic_repair_kernel_sandwich T q rho hq hRow hCol hNorm hRho, two_smul]
    simp only [Matrix.add_mulVec, Matrix.sub_mulVec, Matrix.one_mulVec,
      add_zero, dotProduct, Pi.add_apply, Pi.sub_apply, hZero,
      mul_zero, zero_mul, zero_add, Finset.sum_const_zero,
      mul_add, mul_sub, Finset.sum_add_distrib, Finset.sum_sub_distrib, P, K]
  change 2 * hamiltonianDeletedOverlap T S U - dotProduct ell (K.mulVec ell) =
    dotProduct u (G.mulVec u) + (U.card : Real) ^ 2 * q
  rw [hPull, hExpand, hUP, hUU, hQuad]
  ring

end PrimeFactorOscillations

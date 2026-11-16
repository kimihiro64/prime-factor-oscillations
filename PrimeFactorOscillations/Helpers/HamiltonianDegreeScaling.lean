/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.HamiltonianDegreeJacobian
import PrimeFactorOscillations.Helpers.HamiltonianDegreeScalingFixedPoint
import PrimeFactorOscillations.Helpers.HamiltonianScalingConservation

/-! # Exact positive scaling from the actual compatible degree inverse

The full nonlinear equation is solved on the original bipartite support.
Its parity residual is removed by exact signed conservation, including
every quadratic cross term. No auxiliary completion edge enters the result.
-/

set_option autoImplicit false
set_option Elab.async false

noncomputable section

namespace PrimeFactorOscillations

variable {Iota : Type*} [Fintype Iota] [DecidableEq Iota]

theorem hamiltonian_degree_scaling_residual (T : Matrix Iota Iota Real)
    (z : Sum Iota Iota -> Real) (i : Sum Iota Iota) :
    (1 + z i) * (bipartiteLift T).mulVec (1 + z) i - 1 =
      (hamiltonianDegreeJacobian T).mulVec z i -
        (1 - hamiltonianBipartiteDegree T i) + z i * (bipartiteLift T).mulVec z i := by
  have hOne : (bipartiteLift T).mulVec 1 i = hamiltonianBipartiteDegree T i := by
    change Finset.univ.sum (fun j => bipartiteLift T i j * 1) = _
    simp only [mul_one]
    exact hamiltonian_bipartite_degree_row T i
  have hDiag : (Matrix.diagonal (hamiltonianBipartiteDegree T)).mulVec z i =
      hamiltonianBipartiteDegree T i * z i := by
    simp [Matrix.mulVec, dotProduct, Matrix.diagonal_apply]
  rw [Matrix.mulVec_add]
  change (1 + z i) *
    ((bipartiteLift T).mulVec 1 i + (bipartiteLift T).mulVec z i) - 1 = _
  rw [hOne]
  unfold hamiltonianDegreeJacobian
  rw [Matrix.add_mulVec]
  change _ = (Matrix.diagonal (hamiltonianBipartiteDegree T)).mulVec z i +
    (bipartiteLift T).mulVec z i - _ + _
  rw [hDiag]
  ring

variable [Nonempty Iota]

theorem hamiltonian_degree_fixed_point_scales
    (T : Matrix Iota Iota Real)
    (G : Matrix (Sum Iota Iota) (Sum Iota Iota) Real) (q : Real)
    (hRight : hamiltonianDegreeJacobian T * G = 1 - hamiltonianParityProjection q)
    (z : Sum Iota Iota -> Real)
    (hFix : hamiltonianDegreeRepairMap (bipartiteLift T) G
      (1 - hamiltonianBipartiteDegree T) z = z) :
    forall i, (1 + z i) * (bipartiteLift T).mulVec (1 + z) i = 1 := by
  let ell := 1 - hamiltonianBipartiteDegree T
  let w := ell + hamiltonianDegreeNonlinear (bipartiteLift T) z
  let c := -(q / 2 * Finset.univ.sum (fun j => hamiltonianParitySign j * w j))
  have hZ : G.mulVec w = z := hFix
  have hJz : (hamiltonianDegreeJacobian T).mulVec z =
      w - (hamiltonianParityProjection q).mulVec w := by
    rw [<- hZ, Matrix.mulVec_mulVec, hRight, Matrix.sub_mulVec, Matrix.one_mulVec]
  have hParity (i : Sum Iota Iota) :
      (hamiltonianParityProjection q).mulVec w i = -hamiltonianParitySign i * c := by
    change Finset.univ.sum (fun j =>
      (q / 2 * hamiltonianParitySign i * hamiltonianParitySign j) * w j) = _
    simp_rw [mul_assoc]
    rw [<- Finset.mul_sum, <- Finset.mul_sum]
    dsimp only [c]
    ring
  have hResidual (i : Sum Iota Iota) :
      (1 + z i) * (bipartiteLift T).mulVec (1 + z) i - 1 =
        hamiltonianParitySign i * c := by
    rw [hamiltonian_degree_scaling_residual, hJz]
    change (w i - (hamiltonianParityProjection q).mulVec w i) -
      (1 - hamiltonianBipartiteDegree T i) + z i * (bipartiteLift T).mulVec z i = _
    rw [hParity]
    dsimp only [w, ell, hamiltonianDegreeNonlinear, Pi.add_apply,
      Pi.sub_apply, Pi.one_apply, Pi.neg_apply, Pi.mul_apply]
    ring
  let x : Iota -> Real := fun i => 1 + z (Sum.inl i)
  let y : Iota -> Real := fun j => 1 + z (Sum.inr j)
  have hLeft (i : Iota) : hamiltonianScalingResidual T x y (Sum.inl i) = c := by
    simpa [hamiltonianScalingResidual, x, y, Matrix.mulVec, dotProduct, mul_add, Finset.sum_add_distrib, bipartiteLift,
      Matrix.fromBlocks, Fintype.sum_sum_type, hamiltonianParitySign] using hResidual (Sum.inl i)
  have hRightSide (j : Iota) : hamiltonianScalingResidual T x y (Sum.inr j) = -c := by
    simpa [hamiltonianScalingResidual, x, y, Matrix.mulVec, dotProduct, mul_add, Finset.sum_add_distrib, bipartiteLift,
      Matrix.fromBlocks, Matrix.transpose_apply, Fintype.sum_sum_type,
      hamiltonianParitySign] using hResidual (Sum.inr j)
  have hZero := (hamiltonianScalingResidual_parity_zero T x y rfl c hLeft hRightSide).2
  intro i
  apply sub_eq_zero.mp
  cases i with
  | inl i =>
    simpa [hamiltonianScalingResidual, x, y, Matrix.mulVec, dotProduct, mul_add, Finset.sum_add_distrib, bipartiteLift,
      Matrix.fromBlocks, Fintype.sum_sum_type] using hZero (Sum.inl i)
  | inr j =>
    simpa [hamiltonianScalingResidual, x, y, Matrix.mulVec, dotProduct, mul_add, Finset.sum_add_distrib, bipartiteLift,
      Matrix.fromBlocks, Matrix.transpose_apply, Fintype.sum_sum_type] using hZero (Sum.inr j)

theorem hamiltonian_positive_degree_scaling
    (T : Matrix Iota Iota Real)
    (G : Matrix (Sum Iota Iota) (Sum Iota Iota) Real)
    (q eps g : Real) (hEps : 0 <= eps) (hEpsSmall : eps <= 1 / 2) (hg : 1 <= g)
    (hT : forall i j, 0 <= T i j)
    (hRow : forall i, abs (Finset.univ.sum (fun j => T i j) - 1) <= eps)
    (hCol : forall j, abs (Finset.univ.sum (fun i => T i j) - 1) <= eps)
    (hRight : hamiltonianDegreeJacobian T * G = 1 - hamiltonianParityProjection q)
    (hG : forall i, Finset.univ.sum (fun j => abs (G i j)) <= g)
    (hSmall : eps * g ^ 2 <= 1 / 64) :
    exists z : Sum Iota Iota -> Real, norm z <= 2 * g * eps /\
      (forall i, 0 < 1 + z i) /\
      forall i, (1 + z i) * (bipartiteLift T).mulVec (1 + z) i = 1 := by
  let P := bipartiteLift T
  let ell := 1 - hamiltonianBipartiteDegree T
  let radius := 2 * g * eps
  have hg0 : 0 <= g := (by norm_num : (0 : Real) <= 1).trans hg
  have hRadius : 0 <= radius := by dsimp only [radius]; positivity
  have hPN (i j : Sum Iota Iota) : 0 <= P i j := by
    cases i <;> cases j <;>
      simp [P, bipartiteLift, Matrix.fromBlocks, Matrix.transpose_apply, hT]
  have hPRow (i : Sum Iota Iota) : Finset.univ.sum (fun j => abs (P i j)) <= 2 := by
    simp only [abs_of_nonneg (hPN i _)]
    change Finset.univ.sum (fun j => bipartiteLift T i j) <= 2
    rw [hamiltonian_bipartite_degree_row]
    cases i with
    | inl i =>
      change Finset.univ.sum (fun j => T i j) <= 2
      linarith only [(abs_le.mp (hRow i)).2, hEpsSmall]
    | inr j =>
      change Finset.univ.sum (fun i => T i j) <= 2
      linarith only [(abs_le.mp (hCol j)).2, hEpsSmall]
  have hEll : norm ell <= eps := by
    apply (pi_norm_le_iff_of_nonneg hEps).mpr
    intro i
    rw [Real.norm_eq_abs]
    change abs (1 - hamiltonianBipartiteDegree T i) <= eps
    rw [abs_sub_comm]
    cases i with
    | inl i => exact hRow i
    | inr j => exact hCol j
  have hBall : g * eps + g * 2 * radius ^ 2 <= radius := by
    have hSave := mul_le_mul_of_nonneg_right hSmall (by positivity : 0 <= 8 * g * eps)
    dsimp only [radius]
    nlinarith only [hSave, mul_nonneg hg0 hEps]
  have hLip : 2 * g * 2 * radius <= 1 / 2 := by
    dsimp only [radius]
    nlinarith only [hSmall]
  have hFix := hamiltonian_degree_repair_fixed_point P G ell 2 g eps radius
    (by norm_num) hg0 hEps hRadius hPRow hG hEll hBall hLip
  choose z hNorm hFixed hDisplacement using hFix
  have hRadiusSmall : radius <= 1 / 32 := by
    have hGG : g <= g ^ 2 := by nlinarith only [hg]
    have hScale := mul_le_mul_of_nonneg_left hGG hEps
    dsimp only [radius]
    nlinarith only [hSmall, hScale]
  have hPos (i : Sum Iota Iota) : 0 < 1 + z i := by
    have hPoint := (pi_norm_le_iff_of_nonneg (by norm_num : 0 <= (1 / 32 : Real))).mp
      (hNorm.trans hRadiusSmall) i
    rw [Real.norm_eq_abs] at hPoint
    linarith only [(abs_le.mp hPoint).1]
  exact Exists.intro z (And.intro hNorm (And.intro hPos
    (hamiltonian_degree_fixed_point_scales T G q hRight z hFixed)))

end PrimeFactorOscillations

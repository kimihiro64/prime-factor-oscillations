/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.HamiltonianDegreeScaling
import PrimeFactorOscillations.Helpers.HamiltonianDiffuseJacobianInverse

/-! # Full positive scaling at logarithmic diffuseness cost

The actual inverse, quantitative perturbation and nonlinear consumer are
assembled under one explicit smallness condition. Every row equation is
on the original bipartite matrix and retains the full quadratic term.
-/

set_option autoImplicit false
set_option Elab.async false

open scoped Matrix.Norms.L2Operator

noncomputable section

namespace PrimeFactorOscillations

variable {Iota : Type*} [Fintype Iota] [DecidableEq Iota] [Nonempty Iota]

theorem hamiltonian_actual_diffuse_positive_scaling
    (T : Matrix Iota Iota Real) (q a eps rho : Real)
    (hq : (Fintype.card Iota : Real) * q = 1) (ha : 1 <= a)
    (hEps : 0 < eps) (hEpsSmall : eps <= 1 / 2)
    (hT : forall i j, 0 <= T i j)
    (hRow : forall i, abs (Finset.univ.sum (fun j => T i j) - 1) <= eps)
    (hCol : forall j, abs (Finset.univ.sum (fun i => T i j) - 1) <= eps)
    (hUpper : forall i j, T i j <= a * q)
    (hNorm : norm (centeredKernel T q) <= rho - 6 * eps)
    (hRho0 : 0 < rho) (hRho1 : rho < 1)
    (hSmall : eps * hamiltonianDiffuseInverseBudget (a + 9 * eps) rho ^ 2 <= 1 / 256) :
    exists z : Sum Iota Iota -> Real,
      norm z <= 4 * hamiltonianDiffuseInverseBudget (a + 9 * eps) rho * eps /\
      (forall i, 0 < 1 + z i) /\
      forall i, (1 + z i) * (bipartiteLift T).mulVec (1 + z) i = 1 := by
  let g := hamiltonianDiffuseInverseBudget (a + 9 * eps) rho
  have hStar : 1 <= a + 9 * eps := by linarith only [ha, hEps]
  have hg : 1 <= g := hamiltonian_diffuse_inverse_budget_positive _ rho hStar hRho0 hRho1
  have hgSquare : g <= g ^ 2 := by nlinarith only [hg]
  have hSave := mul_le_mul_of_nonneg_left hgSquare hEps.le
  have hInvSmall : 7 * eps * g <= 1 / 2 := by
    change eps * g ^ 2 <= 1 / 256 at hSmall
    nlinarith only [hSave, hSmall]
  choose G hRight hG using hamiltonian_actual_diffuse_jacobian_inverse T q a eps rho
    hq ha hEps hEpsSmall hT hRow hCol hUpper hNorm hRho0 hRho1 hInvSmall
  have hNonlinearSmall : eps * (2 * g) ^ 2 <= 1 / 64 := by
    change eps * g ^ 2 <= 1 / 256 at hSmall
    nlinarith only [hSmall]
  have h := hamiltonian_positive_degree_scaling T G q eps (2 * g)
    hEps.le hEpsSmall (by linarith only [hg]) hT hRow hCol hRight hG hNonlinearSmall
  choose z hBound hPos hRows using h
  refine Exists.intro z (And.intro ?_ (And.intro hPos hRows))
  change norm z <= 4 * g * eps
  nlinarith only [hBound]


def hamiltonianScaledCross (T : Matrix Iota Iota Real) (z : Sum Iota Iota -> Real) :
    Matrix Iota Iota Real :=
  fun i j => (1 + z (Sum.inl i)) * T i j * (1 + z (Sum.inr j))

theorem hamiltonian_scaled_cross_stochastic (T : Matrix Iota Iota Real)
    (z : Sum Iota Iota -> Real)
    (hRows : forall i, (1 + z i) * (bipartiteLift T).mulVec (1 + z) i = 1) :
    (forall i, Finset.univ.sum (fun j => hamiltonianScaledCross T z i j) = 1) /\
      (forall j, Finset.univ.sum (fun i => hamiltonianScaledCross T z i j) = 1) := by
  constructor
  . intro i
    simpa [hamiltonianScaledCross, Matrix.mulVec, bipartiteLift, Matrix.fromBlocks,
      Fintype.sum_sum_type, Finset.mul_sum, dotProduct, mul_add, Finset.sum_add_distrib, mul_assoc] using hRows (Sum.inl i)
  . intro j
    simpa [hamiltonianScaledCross, Matrix.mulVec, bipartiteLift, Matrix.fromBlocks,
      Matrix.transpose_apply, Fintype.sum_sum_type, Finset.mul_sum,
      dotProduct, mul_add, add_mul, Finset.sum_add_distrib, mul_comm, mul_left_comm,
      mul_assoc, add_comm, add_left_comm, add_assoc] using hRows (Sum.inr j)

theorem hamiltonian_scaled_cross_support (T : Matrix Iota Iota Real)
    (z : Sum Iota Iota -> Real) (hPos : forall i, 0 < 1 + z i) (i j : Iota) :
    hamiltonianScaledCross T z i j = 0 <-> T i j = 0 := by
  simp only [hamiltonianScaledCross, mul_eq_zero,
    (ne_of_gt (hPos (Sum.inl i))), (ne_of_gt (hPos (Sum.inr j))), false_or, or_false]

theorem hamiltonian_scaled_cross_nonnegative (T : Matrix Iota Iota Real)
    (z : Sum Iota Iota -> Real) (hPos : forall i, 0 < 1 + z i)
    (hT : forall i j, 0 <= T i j) (i j : Iota) :
    0 <= hamiltonianScaledCross T z i j :=
  mul_nonneg (mul_nonneg (hPos _).le (hT i j)) (hPos _).le

theorem hamiltonian_scaled_cross_entry_bound (T : Matrix Iota Iota Real)
    (z : Sum Iota Iota -> Real) (r c : Real) (hr : 0 <= r) (hc : 0 <= c)
    (hPos : forall i, 0 < 1 + z i)
    (hZ : forall i, abs (z i) <= r)
    (hT : forall i j, 0 <= T i j) (hUpper : forall i j, T i j <= c) (i j : Iota) :
    hamiltonianScaledCross T z i j <= (1 + r) ^ 2 * c := by
  have hLeft : 1 + z (Sum.inl i) <= 1 + r := by linarith only [(abs_le.mp (hZ (Sum.inl i))).2]
  have hRight : 1 + z (Sum.inr j) <= 1 + r := by linarith only [(abs_le.mp (hZ (Sum.inr j))).2]
  have hOne : 0 <= 1 + r := by positivity
  calc
    _ <= (1 + r) * c * (1 + z (Sum.inr j)) :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul hLeft (hUpper i j) (hT i j) hOne) (hPos _).le
    _ <= (1 + r) * c * (1 + r) :=
      mul_le_mul_of_nonneg_left hRight (mul_nonneg hOne hc)
    _ = _ := by ring

theorem hamiltonian_scaled_cross_operator_error (T : Matrix Iota Iota Real)
    (z : Sum Iota Iota -> Real) (r b : Real) (hr : 0 <= r) (hb : 0 <= b)
    (hZ : forall i, abs (z i) <= r) (hT : forall i j, 0 <= T i j)
    (hRow : forall i, Finset.univ.sum (fun j => T i j) <= b)
    (hCol : forall j, Finset.univ.sum (fun i => T i j) <= b) :
    norm (hamiltonianScaledCross T z - T) <= (2 * r + r ^ 2) * b := by
  have hCoeff (i j : Iota) :
      abs (z (Sum.inl i) + z (Sum.inr j) + z (Sum.inl i) * z (Sum.inr j)) <= 2 * r + r ^ 2 := by
    have hMul := mul_le_mul (hZ (Sum.inl i)) (hZ (Sum.inr j)) (abs_nonneg _) hr
    have hTriangle := abs_add_le
      (z (Sum.inl i) + z (Sum.inr j)) (z (Sum.inl i) * z (Sum.inr j))
    rw [abs_mul] at hTriangle
    nlinarith only [hTriangle, abs_add_le (z (Sum.inl i)) (z (Sum.inr j)),
      hZ (Sum.inl i), hZ (Sum.inr j), hMul]
  have hPoint (i j : Iota) :
      norm ((hamiltonianScaledCross T z - T) i j) <= (2 * r + r ^ 2) * T i j := by
    have hId : (hamiltonianScaledCross T z - T) i j =
        (z (Sum.inl i) + z (Sum.inr j) + z (Sum.inl i) * z (Sum.inr j)) * T i j := by
      simp only [hamiltonianScaledCross, Matrix.sub_apply]
      ring
    rw [hId, Real.norm_eq_abs, abs_mul, abs_of_nonneg (hT i j)]
    exact mul_le_mul_of_nonneg_right (hCoeff i j) (hT i j)
  have hCoeff0 : 0 <= 2 * r + r ^ 2 := by positivity
  apply hamiltonian_l2_row_column_budget _ ((2 * r + r ^ 2) * b) (mul_nonneg hCoeff0 hb)
  . intro i
    calc
      _ <= Finset.univ.sum (fun j => (2 * r + r ^ 2) * T i j) :=
        Finset.sum_le_sum (fun j _ => hPoint i j)
      _ = (2 * r + r ^ 2) * Finset.univ.sum (fun j => T i j) := (Finset.mul_sum _ _ _).symm
      _ <= _ := mul_le_mul_of_nonneg_left (hRow i) hCoeff0
  . intro j
    calc
      _ <= Finset.univ.sum (fun i => (2 * r + r ^ 2) * T i j) :=
        Finset.sum_le_sum (fun i _ => hPoint i j)
      _ = (2 * r + r ^ 2) * Finset.univ.sum (fun i => T i j) := (Finset.mul_sum _ _ _).symm
      _ <= _ := mul_le_mul_of_nonneg_left (hCol j) hCoeff0


theorem hamiltonian_actual_diffuse_stochastic_repair
    (T : Matrix Iota Iota Real) (q a eps rho : Real)
    (hq : (Fintype.card Iota : Real) * q = 1) (ha : 1 <= a)
    (hEps : 0 < eps) (hEpsSmall : eps <= 1 / 2)
    (hT : forall i j, 0 <= T i j)
    (hRow : forall i, abs (Finset.univ.sum (fun j => T i j) - 1) <= eps)
    (hCol : forall j, abs (Finset.univ.sum (fun i => T i j) - 1) <= eps)
    (hUpper : forall i j, T i j <= a * q)
    (hNorm : norm (centeredKernel T q) <= rho - 6 * eps)
    (hRho0 : 0 < rho) (hRho1 : rho < 1)
    (hSmall : eps * hamiltonianDiffuseInverseBudget (a + 9 * eps) rho ^ 2 <= 1 / 256) :
    let r := 4 * hamiltonianDiffuseInverseBudget (a + 9 * eps) rho * eps
    exists z : Sum Iota Iota -> Real,
      norm z <= r /\
      (forall i, 0 < 1 + z i) /\
      (forall i j, 0 <= hamiltonianScaledCross T z i j) /\
      (forall i, Finset.univ.sum (fun j => hamiltonianScaledCross T z i j) = 1) /\
      (forall j, Finset.univ.sum (fun i => hamiltonianScaledCross T z i j) = 1) /\
      (forall i j, hamiltonianScaledCross T z i j = 0 <-> T i j = 0) /\
      (forall i j, hamiltonianScaledCross T z i j <= (1 + r) ^ 2 * (a * q)) /\
      norm (hamiltonianScaledCross T z - T) <= (2 * r + r ^ 2) * (1 + eps) := by
  let r := 4 * hamiltonianDiffuseInverseBudget (a + 9 * eps) rho * eps
  have hStar : 1 <= a + 9 * eps := by linarith only [ha, hEps]
  have hBudget := hamiltonian_diffuse_inverse_budget_positive (a + 9 * eps) rho hStar hRho0 hRho1
  have hBudget0 : 0 <= hamiltonianDiffuseInverseBudget (a + 9 * eps) rho :=
    (by norm_num : (0 : Real) <= 1).trans hBudget
  have hr : 0 <= r :=
    mul_nonneg (mul_nonneg (by norm_num) hBudget0) hEps.le
  choose z hBound hPos hRows using hamiltonian_actual_diffuse_positive_scaling T q a eps rho
    hq ha hEps hEpsSmall hT hRow hCol hUpper hNorm hRho0 hRho1 hSmall
  have hZ (i : Sum Iota Iota) : abs (z i) <= r := by
    exact (pi_norm_le_iff_of_nonneg hr).mp hBound i
  have hStoch := hamiltonian_scaled_cross_stochastic T z hRows
  have hm : 0 < (Fintype.card Iota : Real) := Nat.cast_pos.mpr Fintype.card_pos
  have hq0 : 0 <= q := by nlinarith only [hq, hm]
  have hAq : 0 <= a * q := mul_nonneg ((by norm_num : (0 : Real) <= 1).trans ha) hq0
  have hCap := hamiltonian_scaled_cross_entry_bound T z r (a * q) hr hAq hPos hZ hT hUpper
  have hRowUpper (i : Iota) : Finset.univ.sum (fun j => T i j) <= 1 + eps := by
    linarith only [(abs_le.mp (hRow i)).2]
  have hColUpper (j : Iota) : Finset.univ.sum (fun i => T i j) <= 1 + eps := by
    linarith only [(abs_le.mp (hCol j)).2]
  have hError := hamiltonian_scaled_cross_operator_error T z r (1 + eps) hr
    (by positivity) hZ hT hRowUpper hColUpper
  refine Exists.intro z (And.intro hBound (And.intro hPos ?_))
  refine And.intro (hamiltonian_scaled_cross_nonnegative T z hPos hT) ?_
  refine And.intro hStoch.1 (And.intro hStoch.2 ?_)
  refine And.intro (hamiltonian_scaled_cross_support T z hPos) ?_
  exact And.intro hCap hError

end PrimeFactorOscillations

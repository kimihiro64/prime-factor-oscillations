/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.HamiltonianNormalizedPerron
import PrimeFactorOscillations.Helpers.HamiltonianWeightedSpectralReadout

/-! # Independent normalized spectral error from the proved raw degree packet -/

set_option autoImplicit false
set_option Elab.async false

open scoped Matrix.Norms.L2Operator

noncomputable section

namespace PrimeFactorOscillations

theorem hamiltonian_near_one_inverse_upper
    (r eps : Real) (he0 : 0 <= eps) (he1 : eps <= 1 / 2)
    (hr : abs (r - 1) <= eps) :
    1 / r <= 1 + 2 * eps := by
  have hBounds := abs_le.mp hr
  have hrPos : 0 < r := by linarith only [hBounds.1, he1]
  have hId : (1 / r) * r = 1 := by field_simp [ne_of_gt hrPos]
  have hLow : 1 - eps <= r := by linarith only [hBounds.1]
  have hCoeff : 0 <= 1 + 2 * eps := by linarith only [he0]
  have hProduct := mul_le_mul_of_nonneg_left hLow hCoeff
  have hSquare : eps ^ 2 <= eps / 2 := by nlinarith only [he0, he1]
  apply le_of_not_gt
  intro hBad
  have hStrict := mul_lt_mul_of_pos_right hBad hrPos
  rw [hId] at hStrict
  nlinarith only [hStrict, hProduct, hSquare]

variable {Iota : Type*} [Fintype Iota] [DecidableEq Iota] [Nonempty Iota]

theorem hamiltonian_inverse_degree_conjugation_identity
    (T : Matrix Iota Iota Real) (r c : Iota -> Real) (q t : Real)
    (hr : forall i, 0 < r i) (hc : forall j, 0 < c j)
    (ht : Not (t = 0)) :
    hamiltonianDegreeNormalizedCross T r c - hamiltonianDegreeNormalizedMode r c q t =
      (Matrix.diagonal (fun i => Real.sqrt (1 / r i)) *
        (T - hamiltonianDegreeReference r c q t)) *
        Matrix.diagonal (fun j => Real.sqrt (1 / c j)) := by
  ext i j
  have hr0 : Not (Real.sqrt (r i) = 0) := ne_of_gt (Real.sqrt_pos.mpr (hr i))
  have hc0 : Not (Real.sqrt (c j) = 0) := ne_of_gt (Real.sqrt_pos.mpr (hc j))
  have hMode :
      (q * r i * c j / t) / (Real.sqrt (r i) * Real.sqrt (c j)) =
        q * Real.sqrt (r i) * Real.sqrt (c j) / t := by
    calc
      _ = (q * Real.sqrt (r i) ^ 2 * Real.sqrt (c j) ^ 2 / t) /
          (Real.sqrt (r i) * Real.sqrt (c j)) := by
        rw [Real.sq_sqrt (hr i).le, Real.sq_sqrt (hc j).le]
      _ = _ := by
        field_simp [hr0, hc0, ht]
        <;> ring
  simp only [Matrix.sub_apply, Matrix.diagonal_mul, Matrix.mul_diagonal,
    hamiltonianDegreeNormalizedCross, hamiltonianDegreeNormalizedMode,
    hamiltonianDegreeReference]
  rw [<- hMode]
  simp only [one_div, Real.sqrt_inv]
  field_simp [hr0, hc0, ht]
  <;> ring

theorem hamiltonian_raw_to_normalized_degree_gap
    (T : Matrix Iota Iota Real) (r c : Iota -> Real) (q t eps rho : Real)
    (hq : (Fintype.card Iota : Real) * q = 1)
    (he0 : 0 <= eps) (he1 : eps <= 1 / 2)
    (hp0 : 0 <= rho) (hp1 : rho <= 1)
    (hr : forall i, abs (r i - 1) <= eps)
    (hc : forall j, abs (c j - 1) <= eps)
    (ht : abs (t - 1) <= eps)
    (hNorm : norm (centeredKernel T q) <= rho) :
    norm (hamiltonianDegreeNormalizedCross T r c -
      hamiltonianDegreeNormalizedMode r c q t) <= rho + 16 * eps := by
  have hrPos (i : Iota) : 0 < r i := by
    linarith only [(abs_le.mp (hr i)).1, he1]
  have hcPos (j : Iota) : 0 < c j := by
    linarith only [(abs_le.mp (hc j)).1, he1]
  have htPos : 0 < t := by linarith only [(abs_le.mp ht).1, he1]
  have hRef := hamiltonian_degree_reference_error r c q t eps hq he0 he1 hr hc ht
  have hRefRev : norm ((averagingKernel q : Matrix Iota Iota Real) -
      hamiltonianDegreeReference r c q t) <= 7 * eps := by
    rw [norm_sub_rev]
    exact hRef
  have hN : norm (T - hamiltonianDegreeReference r c q t) <= rho + 7 * eps :=
    (norm_sub_le_norm_sub_add_norm_sub T
      (averagingKernel q : Matrix Iota Iota Real) (hamiltonianDegreeReference r c q t)).trans
      (add_le_add hNorm hRefRev)
  have hConjugate := hamiltonian_degree_conjugation_norm
    (T - hamiltonianDegreeReference r c q t)
    (fun i => 1 / r i) (fun j => 1 / c j) (2 * eps) (rho + 7 * eps)
    (by positivity) (by positivity) hN
    (fun i => hamiltonian_near_one_inverse_upper (r i) eps he0 he1 (hr i))
    (fun j => hamiltonian_near_one_inverse_upper (c j) eps he0 he1 (hc j))
  rw [<- hamiltonian_inverse_degree_conjugation_identity T r c q t
    hrPos hcPos (ne_of_gt htPos)] at hConjugate
  have hSquare : eps ^ 2 <= eps / 2 := by nlinarith only [he0, he1]
  have hProduct := mul_le_mul_of_nonneg_right hp1 he0
  nlinarith only [hConjugate, hSquare, hProduct]

theorem hamiltonian_actual_raw_to_normalized_degree_gap
    (T : Matrix Iota Iota Real) (q eps rho : Real)
    (hq : (Fintype.card Iota : Real) * q = 1)
    (he0 : 0 <= eps) (he1 : eps <= 1 / 2)
    (hp0 : 0 <= rho) (hp1 : rho <= 1)
    (hr : forall i, abs (hamiltonianCrossRowDegrees T i - 1) <= eps)
    (hc : forall j, abs (hamiltonianCrossColumnDegrees T j - 1) <= eps)
    (hNorm : norm (centeredKernel T q) <= rho) :
    norm (hamiltonianActualDegreeNormalizedCross T -
      hamiltonianActualDegreeNormalizedMode T q) <= rho + 16 * eps := by
  exact hamiltonian_raw_to_normalized_degree_gap T
    (hamiltonianCrossRowDegrees T) (hamiltonianCrossColumnDegrees T)
    q (hamiltonianCrossMeanDegree T q) eps rho hq he0 he1 hp0 hp1 hr hc
    (hamiltonian_uniform_degree_mean_error (hamiltonianCrossRowDegrees T) q eps hq he0 hr)
    hNorm

theorem hamiltonian_actual_normalized_native_readout
    (T : Matrix Iota Iota Real) (q eps rho : Real)
    (hq : (Fintype.card Iota : Real) * q = 1)
    (he0 : 0 <= eps) (he1 : eps <= 1 / 2)
    (hp0 : 0 <= rho) (hp1 : rho <= 1)
    (hr : forall i, abs (hamiltonianCrossRowDegrees T i - 1) <= eps)
    (hc : forall j, abs (hamiltonianCrossColumnDegrees T j - 1) <= eps)
    (hNorm : norm (centeredKernel T q) <= rho)
    (k : Sum Iota Iota)
    (hOne : Not ((bipartiteLift_hermitian
      (hamiltonianActualDegreeNormalizedCross T)).eigenvalues k = 1))
    (hMinus : Not ((bipartiteLift_hermitian
      (hamiltonianActualDegreeNormalizedCross T)).eigenvalues k = -(1 : Real))) :
    abs ((bipartiteLift_hermitian
      (hamiltonianActualDegreeNormalizedCross T)).eigenvalues k) <= rho + 16 * eps := by
  have hrPos (i : Iota) : 0 < hamiltonianCrossRowDegrees T i := by
    linarith only [(abs_le.mp (hr i)).1, he1]
  have hcPos (j : Iota) : 0 < hamiltonianCrossColumnDegrees T j := by
    linarith only [(abs_le.mp (hc j)).1, he1]
  have hGap := hamiltonian_actual_raw_to_normalized_degree_gap
    T q eps rho hq he0 he1 hp0 hp1 hr hc hNorm
  rw [hamiltonian_actual_normalized_mode_identity T q hq hrPos] at hGap
  exact hamiltonian_weighted_native_eigenvalue_readout
    (hamiltonianActualDegreeNormalizedCross T)
    (hamiltonianRowRoot T) (hamiltonianColumnRoot T)
    (hamiltonianTotalDegree T) (rho + 16 * eps)
    (hamiltonian_actual_normalized_perron_left T hrPos hcPos)
    (hamiltonian_actual_normalized_perron_right T hrPos hcPos) hGap k hOne hMinus

end PrimeFactorOscillations

/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Analysis.Matrix.Spectrum
import PrimeFactorOscillations.Helpers.HamiltonianL2Resolvent
import PrimeFactorOscillations.Helpers.HamiltonianSpectralTaylor

/-! # The actual stochastic Gram determinant and spectral average

The eigenvalue family is derived from the real Gram matrix, including its
nonnegative eigenvalues, Euclidean operator bound and exact energy sum.
Unitary conjugation preserves the complete determinant, before any analytic
bound. This is the bridge from the finite-spectral Gamma consumer to the
actual centered stochastic matrix.
-/

set_option autoImplicit false
set_option Elab.async false

open scoped Matrix.Norms.L2Operator

noncomputable section

namespace PrimeFactorOscillations

variable {Iota : Type*} [DecidableEq Iota] [Fintype Iota]

private theorem matrixReal_conjTranspose_eq_transpose (B : Matrix Iota Iota Real) :
    B.conjTranspose = B.transpose := by
  ext i j
  simp [Matrix.conjTranspose_apply, Matrix.transpose_apply]

def realGramPositive (B : Matrix Iota Iota Real) :
    Matrix.PosSemidef (B.transpose * B) := by
  simpa only [matrixReal_conjTranspose_eq_transpose B] using
    Matrix.posSemidef_conjTranspose_mul_self B

def realGramHermitian (B : Matrix Iota Iota Real) :
    Matrix.IsHermitian (B.transpose * B) :=
  (realGramPositive B).isHermitian

def realGramEigenvalues (B : Matrix Iota Iota Real) : Iota -> Real :=
  (realGramHermitian B).eigenvalues

theorem realGramEigenvalues_nonnegative (B : Matrix Iota Iota Real) (i : Iota) :
    0 <= realGramEigenvalues B i := by
  exact (realGramPositive B).eigenvalues_nonneg i

theorem realGramEigenvalues_sum_eq_energy (B : Matrix Iota Iota Real) :
    Finset.sum Finset.univ (realGramEigenvalues B) =
      Finset.sum Finset.univ (fun i => Finset.sum Finset.univ (fun j => B i j ^ 2)) := by
  have hTrace : Matrix.trace (B.transpose * B) =
      Finset.sum Finset.univ (realGramEigenvalues B) := by
    simpa [realGramEigenvalues] using (realGramHermitian B).trace_eq_sum_eigenvalues
  rw [<- hTrace]
  change Finset.sum Finset.univ
    (fun i => Finset.sum Finset.univ (fun j => B j i * B j i)) = _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  ring

theorem realGramEigenvalues_le_norm_bound (B : Matrix Iota Iota Real) (rho : Real)
    (hRho : 0 <= rho) (hNorm : norm B <= rho) (i : Iota) :
    realGramEigenvalues B i <= rho ^ 2 := by
  letI : Nonempty Iota := Nonempty.intro i
  have hMem := (realGramHermitian B).eigenvalues_mem_spectrum_real i
  have hAbs := _root_.spectrum.norm_le_norm_of_mem hMem
  have hGram : norm (B.transpose * B) = norm B * norm B := by
    simpa only [matrixReal_conjTranspose_eq_transpose B] using
      Matrix.l2_opNorm_conjTranspose_mul_self B
  have hNormSquare : norm (B.transpose * B) <= rho ^ 2 := by
    rw [hGram, pow_two]
    exact mul_le_mul hNorm hNorm (norm_nonneg B) hRho
  have hValue : realGramEigenvalues B i <= norm (B.transpose * B) := by
    have hNonneg := realGramEigenvalues_nonnegative B i
    change norm (realGramEigenvalues B i) <= norm (B.transpose * B) at hAbs
    rw [Real.norm_eq_abs, abs_of_nonneg hNonneg] at hAbs
    exact hAbs
  exact le_trans hValue hNormSquare

theorem stochasticGram_spectral_data (T : Matrix Iota Iota Real) (q a delta : Real)
    (hq : (Fintype.card Iota : Real) * q = 1)
    (hrow : forall i, Finset.sum Finset.univ (fun j => T i j) = 1)
    (hnonneg : forall i j, 0 <= T i j) (hupper : forall i j, T i j <= a * q)
    (hDelta1 : delta <= 1) (hNorm : norm (centeredKernel T q) <= 1 - delta) :
    And (forall i, 0 <= realGramEigenvalues (centeredKernel T q) i)
      (And (forall i, realGramEigenvalues (centeredKernel T q) i <= (1 - delta) ^ 2)
        (Finset.sum Finset.univ (realGramEigenvalues (centeredKernel T q)) <= a - 1)) := by
  have hEigenUpper : forall i,
      realGramEigenvalues (centeredKernel T q) i <= (1 - delta) ^ 2 := by
    intro i
    exact realGramEigenvalues_le_norm_bound _ (1 - delta) (sub_nonneg.mpr hDelta1) hNorm i
  have hEnergy : Finset.sum Finset.univ
      (realGramEigenvalues (centeredKernel T q)) <= a - 1 := by
    rw [realGramEigenvalues_sum_eq_energy]
    exact stochastic_total_energy T q a hq hrow hnonneg hupper
  exact And.intro (fun i => realGramEigenvalues_nonnegative _ i) (And.intro hEigenUpper hEnergy)

private theorem det_unitary_conjugation (U : unitary (Matrix Iota Iota Real))
    (M : Matrix Iota Iota Real) :
    Matrix.det (Unitary.conjStarAlgAut Real (Matrix Iota Iota Real) U M) = Matrix.det M := by
  rw [Unitary.conjStarAlgAut_apply, Matrix.det_mul, Matrix.det_mul]
  calc
    _ = Matrix.det M * (Matrix.det (U : Matrix Iota Iota Real) *
        Matrix.det (star U : Matrix Iota Iota Real)) := by ring
    _ = Matrix.det M * Matrix.det
        ((U : Matrix Iota Iota Real) * (star U : Matrix Iota Iota Real)) := by
      rw [Matrix.det_mul]
    _ = Matrix.det M := by
      have hUnit : (U : Matrix Iota Iota Real) * star (U : Matrix Iota Iota Real) = 1 := by
        simpa only [Unitary.coe_star] using Unitary.coe_mul_star_self U
      rw [hUnit, Matrix.det_one, mul_one]

theorem hermitian_det_one_sub_smul (M : Matrix Iota Iota Real) (hM : M.IsHermitian)
    (u : Real) :
    Matrix.det ((1 : Matrix Iota Iota Real) - HSMul.hSMul u M) =
      Finset.prod Finset.univ (fun i => 1 - u * hM.eigenvalues i) := by
  let U := hM.eigenvectorUnitary
  let F := Unitary.conjStarAlgAut Real (Matrix Iota Iota Real) U
  have hSpectral : M = F (Matrix.diagonal hM.eigenvalues) := by
    simpa [F, U] using hM.spectral_theorem
  have hMap : F ((1 : Matrix Iota Iota Real) -
      HSMul.hSMul u (Matrix.diagonal hM.eigenvalues)) =
      (1 : Matrix Iota Iota Real) - HSMul.hSMul u M := by
    rw [map_sub, map_one, map_smul, <- hSpectral]
  rw [<- hMap, det_unitary_conjugation]
  have hDiagonal :
      (1 : Matrix Iota Iota Real) - HSMul.hSMul u (Matrix.diagonal hM.eigenvalues) =
      Matrix.diagonal (fun i => 1 - u * hM.eigenvalues i) := by
    ext i j
    by_cases hij : i = j
    case pos => subst j; simp [Matrix.diagonal_apply, Matrix.one_apply, Matrix.smul_apply]
    case neg => simp [Matrix.diagonal_apply, Matrix.one_apply, Matrix.smul_apply, hij]
  rw [hDiagonal, Matrix.det_diagonal]

def realGramDeterminantFactor (B : Matrix Iota Iota Real) (s : Real) : Real :=
  Real.rpow (Matrix.det ((1 : Matrix Iota Iota Real) -
    HSMul.hSMul (s ^ 2) (B.transpose * B))) (-(1 / 2 : Real))

theorem realGramDeterminantFactor_eq_spectral (B : Matrix Iota Iota Real) (s : Real)
    (hFactor : forall i, 0 < 1 - s ^ 2 * realGramEigenvalues B i) :
    realGramDeterminantFactor B s =
      spectralFactors Finset.univ (realGramEigenvalues B) s := by
  have hDet :
      Matrix.det ((1 : Matrix Iota Iota Real) -
        HSMul.hSMul (s ^ 2) (B.transpose * B)) =
      Finset.prod Finset.univ (fun i => 1 - s ^ 2 * realGramEigenvalues B i) :=
    hermitian_det_one_sub_smul (B.transpose * B) (realGramHermitian B) (s ^ 2)
  have hProd : 0 < Finset.prod Finset.univ
      (fun i => 1 - s ^ 2 * realGramEigenvalues B i) :=
    Finset.prod_pos (fun i _ => hFactor i)
  unfold realGramDeterminantFactor
  rw [hDet]
  change (Finset.prod Finset.univ (fun i => 1 - s ^ 2 * realGramEigenvalues B i)) ^
      (-(1 / 2 : Real)) = _
  rw [Real.rpow_def_of_pos hProd]
  unfold spectralFactors spectralLogFactors spectralCoordinate0
  congr 1
  rw [Real.log_prod (fun i _ => ne_of_gt (hFactor i)), Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i hi
  ring

theorem realGramDeterminantFactor_eq_spectral_on_strip
    (B : Matrix Iota Iota Real) (delta eps s : Real)
    (hDelta0 : 0 < delta) (hDelta1 : delta <= 1)
    (hEps0 : 0 <= eps) (hEps1 : eps <= delta / 4)
    (hNorm : norm B <= 1 - delta) (hs : abs (s - 1) <= eps) :
    realGramDeterminantFactor B s =
      spectralFactors Finset.univ (realGramEigenvalues B) s := by
  apply realGramDeterminantFactor_eq_spectral
  intro i
  have hStrip := spectralFactor_strip delta eps (realGramEigenvalues B i) s
    hDelta0 hDelta1 hEps0 hEps1 (realGramEigenvalues_nonnegative B i)
    (realGramEigenvalues_le_norm_bound B (1 - delta) (sub_nonneg.mpr hDelta1) hNorm i) hs
  exact lt_of_lt_of_le hDelta0 hStrip.2.2.2

theorem realGramDeterminantFactor_window_eq
    (B : Matrix Iota Iota Real) (delta eps : Real)
    (hDelta0 : 0 < delta) (hDelta1 : delta <= 1)
    (hEps0 : 0 <= eps) (hEps1 : eps <= delta / 4)
    (hNorm : norm B <= 1 - delta) :
    Set.indicator {s : Real | abs (s - 1) <= eps} (realGramDeterminantFactor B) =
      Set.indicator {s : Real | abs (s - 1) <= eps}
        (spectralFactors Finset.univ (realGramEigenvalues B)) := by
  funext s
  by_cases hs : Membership.mem {x : Real | abs (x - 1) <= eps} s
  case pos =>
    rw [Set.indicator_of_mem hs, Set.indicator_of_mem hs]
    exact realGramDeterminantFactor_eq_spectral_on_strip
      B delta eps s hDelta0 hDelta1 hEps0 hEps1 hNorm hs
  case neg =>
    rw [Set.indicator_of_notMem hs, Set.indicator_of_notMem hs]

theorem stochasticGramDeterminantFactor_gamma_window
    (T : Matrix Iota Iota Real) (q a : Real)
    (hq : (Fintype.card Iota : Real) * q = 1)
    (hrow : forall i, Finset.sum Finset.univ (fun j => T i j) = 1)
    (hnonneg : forall i j, 0 <= T i j) (hupper : forall i j, T i j <= a * q)
    (n : Nat) (hn : 16 <= n) (delta eps : Real)
    (hDelta0 : 0 < delta) (hDelta1 : delta <= 1)
    (hEps0 : 0 < eps) (hEpsHalf : eps <= 1 / 2) (hEps1 : eps <= delta / 4)
    (hLarge : 4 <= (n : Real) * eps)
    (hNorm : norm (centeredKernel T q) <= 1 - delta)
    (hSmall : 2 * (a - 1) * eps <= delta) :
    abs (gammaInverseAverage n
        (Set.indicator {s : Real | abs (s - 1) <= eps}
          (realGramDeterminantFactor (centeredKernel T q))) -
      (spectralFactors Finset.univ (realGramEigenvalues (centeredKernel T q)) 1 +
        (spectralFactorJet2 Finset.univ (realGramEigenvalues (centeredKernel T q)) 1 / 2) /
          ((n : Real) - 1) +
        4 * (spectralFactorJet3 Finset.univ (realGramEigenvalues (centeredKernel T q)) 1 / 6) /
          (((n : Real) - 1) * ((n : Real) - 2)))) <=
      spectralTaylorRemainderBound Finset.univ
        (realGramEigenvalues (centeredKernel T q)) delta *
        (3 * ((n : Real) + 6) /
          (((n : Real) - 1) * ((n : Real) - 2) * ((n : Real) - 3))) +
      Real.exp (-((n : Real) + 1) * eps ^ 2 / 72) *
        spectralTaylorTailCoefficient Finset.univ
          (realGramEigenvalues (centeredKernel T q)) := by
  rw [realGramDeterminantFactor_window_eq (centeredKernel T q) delta eps
    hDelta0 hDelta1 (le_of_lt hEps0) hEps1 hNorm]
  have hData := stochasticGram_spectral_data T q a delta hq hrow hnonneg hupper hDelta1 hNorm
  have hSmallEigen : 2 * (Finset.sum Finset.univ
      (realGramEigenvalues (centeredKernel T q))) * eps <= delta := by
    have hMass := mul_le_mul_of_nonneg_right hData.2.2 (le_of_lt hEps0)
    linarith only [hMass, hSmall]
  exact spectralFactors_gamma_window Finset.univ
    (realGramEigenvalues (centeredKernel T q)) n hn delta eps hDelta0 hDelta1
    hEps0 hEpsHalf hEps1 hLarge (fun i _ => hData.1 i) (fun i _ => hData.2.1 i)
    hSmallEigen

end PrimeFactorOscillations

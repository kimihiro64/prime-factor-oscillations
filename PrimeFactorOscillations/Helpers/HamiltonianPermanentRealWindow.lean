/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.HamiltonianCovarianceCorrectionWindow
import PrimeFactorOscillations.Helpers.HamiltonianPermanentPolylogWindow

/-! # The actual real rook polynomial with its full signed local correction

The compensated complex identity is transferred to the real rook polynomial
before averaging. The determinant factor is kept, and only the proved local
remainder is bounded with the central spectral ratio.
-/

set_option autoImplicit false
set_option Elab.async false

open scoped Matrix.Norms.L2Operator

noncomputable section

namespace PrimeFactorOscillations

theorem stochastic_real_rook_compensated_identity {n : Nat}
    (T : Matrix (Fin n) (Fin n) Real) (q delta s : Real)
    (hq : (n : Real) * q = 1)
    (hRow : forall i, Finset.sum Finset.univ (fun j => T i j) = 1)
    (hCol : forall j, Finset.sum Finset.univ (fun i => T i j) = 1)
    (hDelta0 : 0 < delta) (hDelta1 : delta <= 1)
    (hNorm : norm (centeredKernel T q) <= 1 - delta)
    (hs : abs (s - 1) <= delta / 4) :
    (hamiltonianRookPolynomial (centeredKernel T q) s : Complex) =
      (realGramDeterminantFactor (centeredKernel T q) s : Complex) *
        hamiltonianCompensatedRook (centeredKernel T q) (s : Complex) := by
  let B := centeredKernel T q
  have hDisk : forall j, norm ((s : Complex) *
      realGaussianEigenVariances (bipartiteLift B) (bipartiteLift_hermitian B) j) < 1 := by
    intro j
    have h := stochastic_compensated_eigen_disk T q delta s hDelta0 hDelta1 hNorm hs j
    simpa only [realGaussianEigenVariances, <- Complex.ofReal_mul, Complex.norm_real,
      Real.norm_eq_abs] using h
  have hComp := hamiltonianCompensatedRook_eq_average B (s : Complex)
    (centered_bipartite_column_sum_zero T q
      (by simpa only [Fintype.card_fin] using hq) hRow hCol) hDisk
  have h := stochastic_compensated_rook_identity T q delta s hq hRow hCol
    hDelta0 hDelta1 hNorm hs
  rw [<- hComp] at h
  exact h

theorem stochastic_real_rook_local_covariance_remainder {n : Nat}
    (T : Matrix (Fin n) (Fin n) Real) (q a delta eps s : Real)
    (hn : 11 <= n) (hq : (n : Real) * q = 1) (ha : 1 <= a)
    (hRow : forall i, Finset.sum Finset.univ (fun j => T i j) = 1)
    (hCol : forall j, Finset.sum Finset.univ (fun i => T i j) = 1)
    (hNonneg : forall i j, 0 <= T i j) (hUpper : forall i j, T i j <= a * q)
    (hDelta0 : 0 < delta) (hDelta1 : delta <= 1)
    (hNorm : norm (centeredKernel T q) <= 1 - delta)
    (hEps0 : 0 <= eps) (hEps1 : eps <= delta / 64)
    (hSmall : 2 * (a - 1) * eps <= delta)
    (hSize : hamiltonianPermanentCutoffThreshold delta a <= Real.sqrt (n : Real))
    (hs : abs (s - 1) <= eps) :
    abs (hamiltonianRookPolynomial (centeredKernel T q) s -
      realGramDeterminantFactor (centeredKernel T q) s *
        (1 + covarianceCorrection
          (resolventCovariance (HSMul.hSMul s (bipartiteLift (centeredKernel T q)))))) <=
      Real.exp 1 * realGramDeterminantFactor (centeredKernel T q) 1 *
        (hamiltonianPermanentLocalCorrectionConstant delta * (1 + a) ^ 24 /
          (n : Real) ^ 2) := by
  classical
  let B := centeredKernel T q
  let P := covarianceCorrection (resolventCovariance (HSMul.hSMul s (bipartiteLift B)))
  let E := hamiltonianPermanentLocalCorrectionConstant delta * (1 + a) ^ 24 / (n : Real) ^ 2
  let D := realGramDeterminantFactor B
  have hs4 : abs (s - 1) <= delta / 4 := by linarith only [hs, hEps1, hDelta0]
  have hStep : norm ((s - 1 : Real) : Complex) <= delta / 32 := by
    rw [Complex.norm_real, Real.norm_eq_abs]
    linarith only [hs, hEps1, hDelta0]
  have hSizeS := hamiltonianCorrection_shift_norm_bound delta hDelta0
    ((s - 1 : Real) : Complex) hStep
  have hPoint : (1 : Complex) + ((s - 1 : Real) : Complex) = (s : Complex) := by
    push_cast
    ring
  rw [hPoint] at hSizeS
  have hRealSize : abs s <= hamiltonianWindowScale delta := by
    simpa only [Complex.norm_real, Real.norm_eq_abs] using hSizeS
  have hLocal := stochastic_compensated_window_covariance_remainder T q a delta s hn
    hq ha hRow hCol hNonneg hUpper hDelta0 hDelta1 hNorm hRealSize hSize
  have hId := stochastic_real_rook_compensated_identity T q delta s hq
    hRow hCol hDelta0 hDelta1 hNorm hs4
  have hE0 : 0 <= E := le_trans (norm_nonneg _) hLocal
  have hData := stochasticGram_spectral_data T q a delta
    (by simpa only [Fintype.card_fin] using hq) hRow hNonneg hUpper hDelta1 hNorm
  have hEps4 : eps <= delta / 4 := by linarith only [hEps1, hDelta0]
  have hDet : forall v, abs (v - 1) <= eps ->
      D v = spectralFactors Finset.univ (realGramEigenvalues B) v := by
    intro v hv
    exact realGramDeterminantFactor_eq_spectral_on_strip B delta eps v
      hDelta0 hDelta1 hEps0 hEps4 hNorm hv
  have hD0 : 0 < D s := by rw [hDet s hs]; exact Real.exp_pos _
  have hOne : abs ((1 : Real) - 1) <= eps := by simpa only [sub_self, abs_zero] using hEps0
  have hSmall' : 2 * (Finset.sum Finset.univ (realGramEigenvalues B)) * eps <= delta := by
    have h := mul_le_mul_of_nonneg_right hData.2.2 hEps0
    nlinarith only [h, hSmall]
  have hRatio : D s <= Real.exp 1 * D 1 := by
    rw [hDet s hs, hDet 1 hOne]
    exact spectralFactors_central_ratio Finset.univ (realGramEigenvalues B)
      delta eps s hDelta0 hDelta1 hEps0 hEps4
      (fun i hi => hData.1 i) (fun i hi => hData.2.1 i) hSmall' hs
  have hFact : ((hamiltonianRookPolynomial B s - D s * (1 + P) : Real) : Complex) =
      (D s : Complex) * (hamiltonianCompensatedRook B (s : Complex) -
        (1 + (P : Complex))) := by
    push_cast
    rw [hId]
    ring
  change abs (hamiltonianRookPolynomial B s - D s * (1 + P)) <= Real.exp 1 * D 1 * E
  calc
    _ = norm ((hamiltonianRookPolynomial B s - D s * (1 + P) : Real) : Complex) := by
      rw [Complex.norm_real, Real.norm_eq_abs]
    _ = norm (D s : Complex) *
        norm (hamiltonianCompensatedRook B (s : Complex) - (1 + (P : Complex))) := by
      rw [hFact, norm_mul]
    _ = D s * norm (hamiltonianCompensatedRook B (s : Complex) - (1 + (P : Complex))) := by
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hD0]
    _ <= D s * E := mul_le_mul_of_nonneg_left hLocal hD0.le
    _ <= _ := mul_le_mul_of_nonneg_right hRatio hE0

end PrimeFactorOscillations

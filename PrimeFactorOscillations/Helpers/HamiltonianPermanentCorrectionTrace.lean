/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.HamiltonianDeterminantTraceJet
import PrimeFactorOscillations.Helpers.HamiltonianGaussianTraceBounds
import PrimeFactorOscillations.Helpers.HamiltonianPermanentFirstCorrection

/-! # The full first permanent correction as an actual covariance polynomial

The determinant derivative is identified, not postulated or bounded away.
The trace of the full matrix square retains every cross-block product.
This representation feeds the supported minor comparison with its rank shift.
-/

set_option autoImplicit false
set_option Elab.async false

open scoped Matrix.Norms.L2Operator

noncomputable section

namespace PrimeFactorOscillations

variable {Iota : Type*} [Fintype Iota] [DecidableEq Iota]

def covarianceTraceCorrection (G : Matrix Iota Iota Real) (n : Real) : Real :=
  ((Matrix.trace G) ^ 2 + 2 * Matrix.trace (G * G)) / (8 * (n - 1)) +
    covarianceCorrection G

theorem realGramDeterminantFactor_covariance_second_derivative
    (B : Matrix Iota Iota Real) (rho : Real) (hNorm : norm B <= rho) (hRho : rho < 1) :
    let G := resolventCovariance (bipartiteLift B)
    0 < realGramDeterminantFactor B 1 /\
    deriv (deriv (realGramDeterminantFactor B)) 1 =
      realGramDeterminantFactor B 1 *
        ((Matrix.trace G) ^ 2 / 4 + Matrix.trace (G * G) / 2) := by
  let M := bipartiteLift B
  let hM := bipartiteLift_hermitian B
  have hMNorm : norm M <= rho := le_trans (bipartiteLift_l2_norm_le B) hNorm
  have hPos (i : Sum Iota Iota) : 0 < 1 + hM.eigenvalues i := by
    have hAbs : abs (hM.eigenvalues i) <= rho :=
      le_trans (realGaussianEigenvalue_abs_le_norm M hM i) hMNorm
    have hLower := (abs_le.mp hAbs).1
    linarith only [hLower, hRho]
  have hFunctions : realGramDeterminantFactor B = hermitianDeterminantFactor M := by
    funext t
    unfold realGramDeterminantFactor hermitianDeterminantFactor
    rw [det_one_add_bipartiteLift]
  have hPositive : 0 < hermitianDeterminantFactor M 1 :=
    hermitianDeterminantFactor_pos M hM 1 (fun i => by simpa only [one_mul] using hPos i)
  have hJet := hermitianDeterminantFactor_covariance_second_derivative M hM hPos
  change 0 < realGramDeterminantFactor B 1 /\
    deriv (deriv (realGramDeterminantFactor B)) 1 =
      realGramDeterminantFactor B 1 *
        ((Matrix.trace (resolventCovariance M)) ^ 2 / 4 +
          Matrix.trace (resolventCovariance M * resolventCovariance M) / 2)
  rw [hFunctions]
  exact And.intro hPositive hJet

theorem stochasticPermanentFirstCorrection_trace_formula
    (T : Matrix Iota Iota Real) (q rho : Real)
    (hN : 2 <= Fintype.card Iota)
    (hNorm : norm (centeredKernel T q) <= rho) (hRho : rho < 1) :
    stochasticPermanentFirstCorrection T q =
      covarianceTraceCorrection (resolventCovariance (bipartiteLift (centeredKernel T q)))
        (Fintype.card Iota : Real) := by
  let B := centeredKernel T q
  let G := resolventCovariance (bipartiteLift B)
  have hJet := realGramDeterminantFactor_covariance_second_derivative B rho hNorm hRho
  have hNReal : (2 : Real) <= (Fintype.card Iota : Real) := by exact_mod_cast hN
  have hNm1 : Not ((Fintype.card Iota : Real) - 1 = 0) := by linarith only [hNReal]
  have hFactor : Not (realGramDeterminantFactor B 1 = 0) := ne_of_gt hJet.1
  change deriv (deriv (realGramDeterminantFactor B)) 1 /
      (2 * ((Fintype.card Iota : Real) - 1) * realGramDeterminantFactor B 1) +
        covarianceCorrection G =
      ((Matrix.trace G) ^ 2 + 2 * Matrix.trace (G * G)) /
        (8 * ((Fintype.card Iota : Real) - 1)) + covarianceCorrection G
  rw [hJet.2]
  field_simp [hFactor, hNm1]
  <;> ring

end PrimeFactorOscillations

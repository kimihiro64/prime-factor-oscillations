/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.LogGaussianPhysicalProbe
import PrimeFactorOscillations.Helpers.LogGaussianZeroResidues

/-!
# The full zero-residue series in the actual physical Gaussian probe

All canonical zero indices and multiplicities are retained. The summable
left-tail error is displayed with its sign, alongside the constant,
reference pole, gamma contribution and exact Gaussian reference.
-/

set_option autoImplicit false
set_option Elab.async false

open MeasureTheory

namespace PrimeFactorOscillations.PrimeClassDeletion

theorem logGaussian_xi_paired_sum_eq_residues_sub_errors
    (X V tau : Real) (hX : 0 < X) (hV : 1 <= V) :
    (((1 / (2 * Real.pi) : Real) : Complex)) *
      tsum (fun p : RiemannXiDivisorZeroIndex => integral volume (fun t : Real =>
        logGaussianVerticalKernel X V tau t *
          (1 / ((3 / 2 : Complex) + (t : Complex) * Complex.I - riemannXiDivisorZeroValue p) +
            1 / riemannXiDivisorZeroValue p))) =
      tsum (fun p : RiemannXiDivisorZeroIndex =>
        logGaussianZeroResidue X V tau (riemannXiDivisorZeroValue p)) -
      tsum (fun p : RiemannXiDivisorZeroIndex =>
        logGaussianLeftZeroError X V tau (riemannXiDivisorZeroValue p)) := by
  have hVPos : 0 < V := lt_of_lt_of_le Real.zero_lt_one hV
  calc
    _ = tsum (fun p : RiemannXiDivisorZeroIndex =>
        (((1 / (2 * Real.pi) : Real) : Complex)) *
          integral volume (fun t : Real =>
            logGaussianVerticalKernel X V tau t *
              (1 / ((3 / 2 : Complex) + (t : Complex) * Complex.I - riemannXiDivisorZeroValue p) +
                1 / riemannXiDivisorZeroValue p))) := tsum_mul_left.symm
    _ = tsum (fun p : RiemannXiDivisorZeroIndex =>
        (1 / riemannXiDivisorZeroValue p) *
          logGaussianSpectralTail X V tau 1 (riemannXiDivisorZeroValue p)) := by
      apply tsum_congr
      intro p
      exact logGaussian_xi_paired_integral_eq_tail X V tau hX hVPos p
    _ = _ := logGaussian_xi_physical_sum_eq_residues_sub_errors X V tau hX hV

theorem logGaussianPsiProbe_eq_full_signed_zero_residues
    (X V tau : Real) (hX : 0 < X) (hV : 1 <= V) :
    let H : Real -> Complex := logGaussianVerticalKernel X V tau
    logGaussianPsiProbe X V tau =
      (((1 / (2 * Real.pi) : Real) : Complex)) *
        (logGaussianXiConstant * integral volume H +
          integral volume (fun t : Real => H t /
            ((3 / 2 : Complex) + (t : Complex) * Complex.I - 1)) +
          integral volume (fun t : Real => H t * logGaussianGammaMultiplier t)) -
      tsum (fun p : RiemannXiDivisorZeroIndex =>
        logGaussianZeroResidue X V tau (riemannXiDivisorZeroValue p)) +
      tsum (fun p : RiemannXiDivisorZeroIndex =>
        logGaussianLeftZeroError X V tau (riemannXiDivisorZeroValue p)) -
      (X : Complex) * Complex.exp ((V : Complex) / 2 *
        ((1 : Complex) - (tau : Complex) * Complex.I) ^ 2) := by
  have hVPos : 0 < V := lt_of_lt_of_le Real.zero_lt_one hV
  have hSigned := logGaussianPsiProbe_eq_full_signed_xi_identity X V tau hX hVPos
  have hXi := logGaussian_xi_paired_sum_eq_residues_sub_errors X V tau hX hV
  dsimp only at hSigned
  dsimp only
  rw [hSigned, mul_add, mul_add, mul_sub, hXi]
  ring

end PrimeFactorOscillations.PrimeClassDeletion

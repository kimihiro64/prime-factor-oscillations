/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.LogGaussianPhysicalSpectralTail

/-!
# The complete Gaussian zero-residue series and its retained tail error

Absolute convergence comes from the proved paired physical series and
the summable left-tail error. Every canonical divisor-zero index and
its multiplicity remain present. No RH or zero-count hypothesis is added.
-/

set_option autoImplicit false
set_option Elab.async false

open MeasureTheory Set Filter

namespace PrimeFactorOscillations.PrimeClassDeletion

noncomputable def logGaussianZeroResidue
    (X V tau : Real) (rho : Complex) : Complex :=
  (X : Complex) ^ rho / rho *
    Complex.exp ((V : Complex) / 2 * (rho - (tau : Complex) * Complex.I) ^ 2)

theorem logGaussian_zero_tail_eq_residue_sub_error
    (X V tau : Real) (rho : Complex) (hX : 0 < X) (hV : 0 < V) :
    (1 / rho) * logGaussianSpectralTail X V tau 1 rho =
      logGaussianZeroResidue X V tau rho - logGaussianLeftZeroError X V tau rho := by
  have hSplit := integral_add_compl (s := Iic (-Real.log X)) measurableSet_Iic
    (logGaussianWeightedWave_integrable V tau rho hV)
  simp only [compl_Iic] at hSplit
  rw [logGaussianWeightedWave_integral V tau rho hV] at hSplit
  have hRight : integral (volume.restrict (Ioi (-Real.log X)))
      (logGaussianWeightedWave V tau rho) =
    Complex.exp ((V : Complex) / 2 * (rho - (tau : Complex) * Complex.I) ^ 2) -
      integral (volume.restrict (Iic (-Real.log X))) (logGaussianWeightedWave V tau rho) :=
    (eq_sub_iff_add_eq).mpr (by simpa only [add_comm] using hSplit)
  rw [logGaussianSpectralTail_eq_physical_spectral_tail X V tau rho hX, hRight]
  dsimp [logGaussianZeroResidue, logGaussianLeftZeroError]
  ring

theorem logGaussian_zero_residue_xi_summable
    (X V tau : Real) (hX : 0 < X) (hV : 1 <= V) :
    Summable (fun p : RiemannXiDivisorZeroIndex =>
      logGaussianZeroResidue X V tau (riemannXiDivisorZeroValue p)) := by
  have hVPos : 0 < V := lt_of_lt_of_le Real.zero_lt_one hV
  have hTail := logGaussian_xi_physical_tail_summable X V tau hX hVPos
  have hError := logGaussianLeftZeroError_xi_summable X V tau hX hV
  apply (hTail.add hError).congr
  intro p
  exact (eq_sub_iff_add_eq).mp
    (logGaussian_zero_tail_eq_residue_sub_error X V tau (riemannXiDivisorZeroValue p) hX hVPos)

theorem logGaussian_xi_physical_sum_eq_residues_sub_errors
    (X V tau : Real) (hX : 0 < X) (hV : 1 <= V) :
    tsum (fun p : RiemannXiDivisorZeroIndex =>
        (1 / riemannXiDivisorZeroValue p) *
          logGaussianSpectralTail X V tau 1 (riemannXiDivisorZeroValue p)) =
      tsum (fun p : RiemannXiDivisorZeroIndex =>
        logGaussianZeroResidue X V tau (riemannXiDivisorZeroValue p)) -
      tsum (fun p : RiemannXiDivisorZeroIndex =>
        logGaussianLeftZeroError X V tau (riemannXiDivisorZeroValue p)) := by
  have hVPos : 0 < V := lt_of_lt_of_le Real.zero_lt_one hV
  have hFull := logGaussian_zero_residue_xi_summable X V tau hX hV
  have hError := logGaussianLeftZeroError_xi_summable X V tau hX hV
  calc
    _ = tsum (fun p : RiemannXiDivisorZeroIndex =>
        logGaussianZeroResidue X V tau (riemannXiDivisorZeroValue p) -
          logGaussianLeftZeroError X V tau (riemannXiDivisorZeroValue p)) := by
      apply tsum_congr
      intro p
      exact logGaussian_zero_tail_eq_residue_sub_error X V tau (riemannXiDivisorZeroValue p) hX hVPos
    _ = _ := hFull.tsum_sub hError

end PrimeFactorOscillations.PrimeClassDeletion

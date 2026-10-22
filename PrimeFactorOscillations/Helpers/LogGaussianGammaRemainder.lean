/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.LogGaussianGammaPairing
import PrimeFactorOscillations.Helpers.LogGaussianRightTail

/-!
# A uniform summable bound for the complete Gaussian gamma remainder

The full archimedean series is absolutely convergent and bounded by an
explicit finite constant times exp(V/2)/(X*sqrt(2*pi*V)).
-/

set_option autoImplicit false
set_option Elab.async false

open MeasureTheory

namespace PrimeFactorOscillations.PrimeClassDeletion

noncomputable def logGaussianGammaTailWeight (k : Nat) : Real :=
  1 / ((2 * ((k : Real) + 1)) * (2 * ((k : Real) + 1) - 1))

theorem logGaussianGammaTailWeight_nonneg (k : Nat) :
    0 <= logGaussianGammaTailWeight k := by
  have hk : 0 <= (k : Real) := Nat.cast_nonneg k
  unfold logGaussianGammaTailWeight
  have hLast : 0 < 2 * ((k : Real) + 1) - 1 := by linarith
  exact div_nonneg zero_le_one (mul_nonneg (by positivity) hLast.le)

theorem logGaussianGammaTailWeight_le_inverse_square (k : Nat) :
    logGaussianGammaTailWeight k <= (Inv.inv ((k : Real) + 1)) ^ (2 : Nat) := by
  have hk : 0 <= (k : Real) := Nat.cast_nonneg k
  have hDen : ((k : Real) + 1) ^ (2 : Nat) <=
      (2 * ((k : Real) + 1)) * (2 * ((k : Real) + 1) - 1) := by nlinarith
  calc
    _ <= 1 / (((k : Real) + 1) ^ (2 : Nat)) :=
      one_div_le_one_div_of_le (by positivity) hDen
    _ = _ := by rw [one_div, inv_pow]

theorem logGaussianGammaTailWeight_summable : Summable logGaussianGammaTailWeight := by
  have hSource := (Real.summable_one_div_nat_add_rpow 1 2).mpr (by norm_num)
  have hSquare : Summable (fun k : Nat => (Inv.inv ((k : Real) + 1)) ^ (2 : Nat)) := by
    apply hSource.congr
    intro k
    norm_num [abs_of_pos (by positivity : (0 : Real) < k + 1), one_div, inv_pow]
  exact Summable.of_nonneg_of_le logGaussianGammaTailWeight_nonneg
    logGaussianGammaTailWeight_le_inverse_square hSquare

theorem logGaussian_gamma_tail_summable
    (X V tau : Real) (hX : 0 < X) (hV : 0 < V) :
    Summable (fun k : Nat =>
      logGaussianSpectralTail X V tau 1 (-(2 * ((k : Complex) + 1))) /
        (2 * ((k : Complex) + 1))) := by
  apply Summable.of_norm_bounded
    (logGaussianGammaTailWeight_summable.mul_left (logGaussianTailScale V / X))
  intro k
  exact logGaussian_negative_even_atom_norm_bound X V tau hX hV k

theorem logGaussian_gamma_tail_sum_norm_bound
    (X V tau : Real) (hX : 0 < X) (hV : 0 < V) :
    norm (tsum (fun k : Nat =>
      logGaussianSpectralTail X V tau 1 (-(2 * ((k : Complex) + 1))) /
        (2 * ((k : Complex) + 1)))) <=
      (logGaussianTailScale V / X) * tsum logGaussianGammaTailWeight := by
  have hSum := logGaussian_gamma_tail_summable X V tau hX hV
  have hMajor := logGaussianGammaTailWeight_summable.mul_left (logGaussianTailScale V / X)
  calc
    _ <= tsum (fun k : Nat =>
        norm (logGaussianSpectralTail X V tau 1 (-(2 * ((k : Complex) + 1))) /
          (2 * ((k : Complex) + 1)))) := norm_tsum_le_tsum_norm hSum.norm
    _ <= tsum (fun k : Nat =>
        (logGaussianTailScale V / X) * logGaussianGammaTailWeight k) :=
      Summable.tsum_le_tsum (fun k => logGaussian_negative_even_atom_norm_bound X V tau hX hV k)
        hSum.norm hMajor
    _ = _ := tsum_mul_left

theorem logGaussian_complete_gamma_norm_bound
    (X V tau : Real) (hX : 0 < X) (hV : 0 < V) :
    norm ((((1 / (2 * Real.pi) : Real) : Complex)) *
      integral volume (fun t : Real =>
        logGaussianVerticalKernel X V tau t * logGaussianGammaMultiplier t)) <=
      (logGaussianTailScale V / X) * tsum logGaussianGammaTailWeight := by
  rw [logGaussian_complete_gamma_pairing X V tau hX hV]
  exact logGaussian_gamma_tail_sum_norm_bound X V tau hX hV

end PrimeFactorOscillations.PrimeClassDeletion

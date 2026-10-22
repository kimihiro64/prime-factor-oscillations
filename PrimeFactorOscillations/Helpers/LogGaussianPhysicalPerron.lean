/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import Mathlib.NumberTheory.Chebyshev
import PrimeFactorOscillations.Helpers.LogGaussianPrimePowerStep
import PrimeFactorOscillations.Helpers.LogGaussianXiInterchange

/-!
# Perron's formula for the actual physical Gaussian psi integral

The proof reconstructs every prime-power threshold, proves absolute
sum-integral interchange, and identifies the integral in the paper.
No additional analytic hypothesis is introduced.
-/

set_option autoImplicit false
set_option Elab.async false

open MeasureTheory

namespace PrimeFactorOscillations.PrimeClassDeletion

theorem logGaussianPrimePowerStep_tsum
    (X V tau u : Real) (hX : 0 < X) :
    tsum (fun m : Nat => logGaussianPrimePowerStep X V tau m u) =
      (Chebyshev.psi (X * Real.exp u) : Complex) * logGaussianWave V tau u := by
  have hy : 0 <= X * Real.exp u := (mul_pos hX (Real.exp_pos u)).le
  have hSupport : forall m : Nat,
      Not (Membership.mem (Finset.Icc 0 (Nat.floor (X * Real.exp u))) m) ->
      logGaussianPrimePowerStep X V tau m u = 0 := by
    intro m hm
    have hmFloor : Not (m <= Nat.floor (X * Real.exp u)) := by
      intro hmLe
      exact hm (Finset.mem_Icc.mpr (And.intro (Nat.zero_le m) hmLe))
    have hmY : Not ((m : Real) <= X * Real.exp u) := by
      intro hmLe
      exact hmFloor ((Nat.le_floor_iff hy).mpr hmLe)
    simp only [logGaussianPrimePowerStep, if_neg hmY]
  rw [tsum_eq_sum hSupport]
  calc
    Finset.sum (Finset.Icc 0 (Nat.floor (X * Real.exp u)))
        (fun m : Nat => logGaussianPrimePowerStep X V tau m u) =
      Finset.sum (Finset.Icc 0 (Nat.floor (X * Real.exp u)))
        (fun m : Nat => (ArithmeticFunction.vonMangoldt m : Complex) *
          logGaussianWave V tau u) := by
      apply Finset.sum_congr rfl
      intro m hm
      have hmY : (m : Real) <= X * Real.exp u :=
        (Nat.le_floor_iff hy).mp (Finset.mem_Icc.mp hm).2
      simp only [logGaussianPrimePowerStep, if_pos hmY]
    _ = _ := by
      rw [<- Finset.sum_mul, Chebyshev.psi_eq_sum_Icc]
      push_cast
      rfl

theorem logGaussian_physical_psi_integrable
    (X V tau : Real) (hX : 0 < X) (hV : 0 < V) :
    Integrable (fun u : Real =>
      (Chebyshev.psi (X * Real.exp u) : Complex) * logGaussianWave V tau u) := by
  have hF := fun m : Nat => logGaussianPrimePowerStep_integrable X V tau m hX hV
  have hSum := logGaussianPrimePowerStep_summable_integral_norm X V tau hX hV
  have hInt := Robin1984.integrable_complex_series_of_integral_norm hF hSum
  apply hInt.congr
  exact Filter.Eventually.of_forall fun u => logGaussianPrimePowerStep_tsum X V tau u hX

theorem logGaussian_physical_psi_eq_arithmetic_sum
    (X V tau : Real) (hX : 0 < X) (hV : 0 < V) :
    (integral volume fun u : Real =>
      (Chebyshev.psi (X * Real.exp u) : Complex) * logGaussianWave V tau u) =
      tsum (fun m : Nat => (ArithmeticFunction.vonMangoldt m : Complex) *
        logGaussianSpectralTail X V tau (m : Real) 0) := by
  have hF := fun m : Nat => logGaussianPrimePowerStep_integrable X V tau m hX hV
  have hSum := logGaussianPrimePowerStep_summable_integral_norm X V tau hX hV
  have hSwap := integral_tsum_of_summable_integral_norm hF hSum
  calc
    _ = integral volume (fun u : Real =>
        tsum (fun m : Nat => logGaussianPrimePowerStep X V tau m u)) := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun u =>
        (logGaussianPrimePowerStep_tsum X V tau u hX).symm
    _ = tsum (fun m : Nat => integral volume (logGaussianPrimePowerStep X V tau m)) := hSwap.symm
    _ = _ := by
      apply tsum_congr
      intro m
      exact logGaussianPrimePowerStep_integral X V tau m hX

theorem logGaussian_physical_psi_eq_safeLineIntegral
    (X V tau sigma : Real) (hX : 0 < X) (hV : 0 < V) (hSigma : 1 < sigma) :
    (integral volume fun u : Real =>
      (Chebyshev.psi (X * Real.exp u) : Complex) * logGaussianWave V tau u) =
      (((1 / (2 * Real.pi) : Real) : Complex)) *
        (integral volume fun t : Real =>
          (-deriv riemannZeta ((sigma : Complex) + (t : Complex) * Complex.I) /
            riemannZeta ((sigma : Complex) + (t : Complex) * Complex.I)) *
              logGaussianMellinKernel X V tau
                ((sigma : Complex) + (t : Complex) * Complex.I)) := by
  rw [logGaussian_physical_psi_eq_arithmetic_sum X V tau hX hV]
  exact logGaussian_vonMangoldt_weight_eq_safeLineIntegral X V tau sigma hX hV hSigma

end PrimeFactorOscillations.PrimeClassDeletion

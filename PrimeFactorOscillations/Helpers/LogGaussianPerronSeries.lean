/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.LogGaussianIntegrability
import PrimeFactorOscillations.Helpers.LogGaussianPerronWeight

/-!
# Absolute arithmetic Gaussian Perron series

The actual cumulative Gaussian weight is summed against von Mangoldt.
Every positive X,V and real frequency is retained. The safe line may be
any sigma>1. Absolute convergence is proved, not assumed.
-/

set_option autoImplicit false
set_option Elab.async false

open MeasureTheory

namespace PrimeFactorOscillations.PrimeClassDeletion

theorem logGaussian_vonMangoldt_weight_integral
    (X V tau sigma : Real) (hX : 0 < X) (hV : 0 < V)
    (hSigma : 0 < sigma) (m : Nat) :
    (ArithmeticFunction.vonMangoldt m : Complex) *
        logGaussianSpectralTail X V tau (m : Real) 0 =
      (((1 / (2 * Real.pi) : Real) : Complex)) *
        (integral volume fun t : Real =>
          ((ArithmeticFunction.vonMangoldt m : Complex) /
            (m : Complex) ^ ((sigma : Complex) + (t : Complex) * Complex.I)) *
              logGaussianMellinKernel X V tau
                ((sigma : Complex) + (t : Complex) * Complex.I)) := by
  by_cases hm : m = 0
  . simp [hm]
  . have hmPos : 0 < (m : Real) := by exact_mod_cast Nat.pos_of_ne_zero hm
    have hi := logGaussianMellinKernel_inverse_tail X V tau (m : Real) sigma
      hX hV hmPos hSigma
    rw [<- hi]
    rw [mul_left_comm, <- integral_const_mul]
    congr 1
    apply integral_congr_ae
    filter_upwards with t
    rw [Complex.ofReal_natCast, Complex.cpow_neg, div_eq_mul_inv]
    ring

theorem logGaussian_vonMangoldt_weight_summable
    (X V tau sigma : Real) (hX : 0 < X) (hV : 0 < V) (hSigma : 1 < sigma) :
    Summable (fun m : Nat => (ArithmeticFunction.vonMangoldt m : Complex) *
      logGaussianSpectralTail X V tau (m : Real) 0) := by
  let H : Real -> Complex := fun t : Real =>
    logGaussianMellinKernel X V tau ((sigma : Complex) + (t : Complex) * Complex.I)
  let A : Nat -> Real := fun m =>
    norm ((ArithmeticFunction.vonMangoldt m : Complex) / (m : Complex) ^ (sigma : Complex))
  let C : Complex := (((1 / (2 * Real.pi) : Real) : Complex))
  have hSigmaPos : 0 < sigma := lt_trans Real.zero_lt_one hSigma
  have hA : Summable A :=
    (Robin1984.robin_summable_vonMangoldt_cpow
      (s := (sigma : Complex)) (by simpa using hSigma)).norm
  have hNorm (m : Nat) (t : Real) :
      norm (((ArithmeticFunction.vonMangoldt m : Complex) /
        (m : Complex) ^ ((sigma : Complex) + (t : Complex) * Complex.I)) * H t) =
      A m * norm (H t) := by
    rw [norm_mul, Robin1984.norm_vonMangoldt_vertical_eq]
  have hBound (m : Nat) :
      norm ((ArithmeticFunction.vonMangoldt m : Complex) *
        logGaussianSpectralTail X V tau (m : Real) 0) <=
      A m * (norm C * integral volume (fun t : Real => norm (H t))) := by
    rw [logGaussian_vonMangoldt_weight_integral X V tau sigma hX hV hSigmaPos,
      norm_mul]
    change norm C * norm (integral volume fun t : Real =>
      ((ArithmeticFunction.vonMangoldt m : Complex) /
        (m : Complex) ^ ((sigma : Complex) + (t : Complex) * Complex.I)) * H t) <= _
    calc
      _ <= norm C * integral volume (fun t : Real =>
          norm (((ArithmeticFunction.vonMangoldt m : Complex) /
            (m : Complex) ^ ((sigma : Complex) + (t : Complex) * Complex.I)) * H t)) :=
        mul_le_mul_of_nonneg_left (norm_integral_le_integral_norm _) (norm_nonneg C)
      _ = _ := by
        simp_rw [hNorm]
        rw [integral_const_mul]
        ring
  exact Summable.of_norm_bounded (hA.mul_right _) hBound

theorem logGaussian_vonMangoldt_weight_eq_safeLineIntegral
    (X V tau sigma : Real) (hX : 0 < X) (hV : 0 < V) (hSigma : 1 < sigma) :
    tsum (fun m : Nat => (ArithmeticFunction.vonMangoldt m : Complex) *
        logGaussianSpectralTail X V tau (m : Real) 0) =
      (((1 / (2 * Real.pi) : Real) : Complex)) *
        (integral volume fun t : Real =>
          (-deriv riemannZeta ((sigma : Complex) + (t : Complex) * Complex.I) /
            riemannZeta ((sigma : Complex) + (t : Complex) * Complex.I)) *
              logGaussianMellinKernel X V tau
                ((sigma : Complex) + (t : Complex) * Complex.I)) := by
  have hSigmaPos : 0 < sigma := lt_trans Real.zero_lt_one hSigma
  have hH := logGaussianMellinKernel_integrable_vertical X V tau sigma hX hV hSigmaPos
  have hSwap := Robin1984.integral_vonMangoldt_series_mul hSigma hH
  calc
    _ = tsum (fun m : Nat =>
        (((1 / (2 * Real.pi) : Real) : Complex)) *
          (integral volume fun t : Real =>
            ((ArithmeticFunction.vonMangoldt m : Complex) /
              (m : Complex) ^ ((sigma : Complex) + (t : Complex) * Complex.I)) *
                logGaussianMellinKernel X V tau
                  ((sigma : Complex) + (t : Complex) * Complex.I))) := by
      apply tsum_congr
      intro m
      exact logGaussian_vonMangoldt_weight_integral X V tau sigma hX hV hSigmaPos m
    _ = _ := by rw [tsum_mul_left, hSwap]

end PrimeFactorOscillations.PrimeClassDeletion

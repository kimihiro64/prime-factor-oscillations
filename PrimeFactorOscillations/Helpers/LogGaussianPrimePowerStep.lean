/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.LogGaussianPerronSeries
import PrimeFactorOscillations.Helpers.LogGaussianPhysicalWeight

/-!
# Prime-power steps under the physical Gaussian

Each actual condition m<=X*exp(u) gives the correct Gaussian tail.
The integrated norm is dominated by the actual unmodulated arithmetic
weight, which supplies absolute Fubini without losing the signed probe.
-/

set_option autoImplicit false
set_option Elab.async false

open MeasureTheory Set

namespace PrimeFactorOscillations.PrimeClassDeletion

noncomputable def logGaussianPrimePowerStep
    (X V tau : Real) (m : Nat) (u : Real) : Complex :=
  if (m : Real) <= X * Real.exp u then
    (ArithmeticFunction.vonMangoldt m : Complex) * logGaussianWave V tau u
  else 0

theorem logGaussianPrimePowerStep_eq_indicator
    (X V tau : Real) (m : Nat) (hX : 0 < X) (hm : Not (m = 0)) (u : Real) :
    logGaussianPrimePowerStep X V tau m u =
      (Ici (Real.log (m : Real) - Real.log X)).indicator
        (fun v : Real => (ArithmeticFunction.vonMangoldt m : Complex) *
          logGaussianWave V tau v) u := by
  have hmPos : 0 < (m : Real) := by exact_mod_cast Nat.pos_of_ne_zero hm
  have hThreshold : (m : Real) <= X * Real.exp u <->
      Real.log (m : Real) - Real.log X <= u := by
    calc
      (m : Real) <= X * Real.exp u <-> (m : Real) / X <= Real.exp u := by
        constructor
        . intro h
          calc
            (m : Real) / X = (m : Real) * Inv.inv X := by ring
            _ <= (X * Real.exp u) * Inv.inv X :=
              mul_le_mul_of_nonneg_right h (inv_nonneg.mpr hX.le)
            _ = Real.exp u := by field_simp [hX.ne']
        . intro h
          calc
            (m : Real) = ((m : Real) / X) * X := by field_simp [hX.ne']
            _ <= Real.exp u * X := mul_le_mul_of_nonneg_right h hX.le
            _ = X * Real.exp u := mul_comm _ _
      _ <-> _ := by
        rw [<- Real.log_le_log_iff (div_pos hmPos hX) (Real.exp_pos u),
          Real.log_div hmPos.ne' hX.ne', Real.log_exp]
  simp only [logGaussianPrimePowerStep, Set.indicator, mem_Ici, hThreshold]

theorem logGaussianPrimePowerStep_integrable
    (X V tau : Real) (m : Nat) (hX : 0 < X) (hV : 0 < V) :
    Integrable (logGaussianPrimePowerStep X V tau m) := by
  by_cases hm : m = 0
  . subst m
    change Integrable (fun u : Real => logGaussianPrimePowerStep X V tau 0 u)
    simp [logGaussianPrimePowerStep]
  . have hBase := (logGaussianWave_integrable V tau hV).const_mul (ArithmeticFunction.vonMangoldt m : Complex)
    have h := hBase.indicator
      (measurableSet_Ici (a := Real.log (m : Real) - Real.log X))
    apply h.congr
    exact Filter.Eventually.of_forall fun u =>
      (logGaussianPrimePowerStep_eq_indicator X V tau m hX hm u).symm

theorem logGaussianPrimePowerStep_integral
    (X V tau : Real) (m : Nat) (hX : 0 < X) :
    (integral volume (logGaussianPrimePowerStep X V tau m)) =
      (ArithmeticFunction.vonMangoldt m : Complex) *
        logGaussianSpectralTail X V tau (m : Real) 0 := by
  by_cases hm : m = 0
  . subst m
    change (integral volume fun u : Real => logGaussianPrimePowerStep X V tau 0 u) = _
    simp [logGaussianPrimePowerStep]
  . have hmPos : 0 < (m : Real) := by exact_mod_cast Nat.pos_of_ne_zero hm
    have he : logGaussianPrimePowerStep X V tau m =
        (Ici (Real.log (m : Real) - Real.log X)).indicator
          (fun u : Real => (ArithmeticFunction.vonMangoldt m : Complex) *
            logGaussianWave V tau u) := by
      funext u
      exact logGaussianPrimePowerStep_eq_indicator X V tau m hX hm u
    rw [he, integral_indicator measurableSet_Ici, integral_Ici_eq_integral_Ioi,
      integral_const_mul, <- logGaussianSpectralTail_zero_eq_physical_tail X V tau (m : Real) hmPos]

theorem logGaussianPrimePowerStep_integral_norm_le
    (X V tau : Real) (m : Nat) (hX : 0 < X) (hV : 0 < V) :
    (integral volume fun u : Real => norm (logGaussianPrimePowerStep X V tau m u)) <=
      norm ((ArithmeticFunction.vonMangoldt m : Complex) *
        logGaussianSpectralTail X V 0 (m : Real) 0) := by
  have hPoint (u : Real) :
      ((norm (logGaussianPrimePowerStep X V tau m u) : Real) : Complex) =
        logGaussianPrimePowerStep X V 0 m u := by
    unfold logGaussianPrimePowerStep
    split_ifs with h
    . rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg ArithmeticFunction.vonMangoldt_nonneg,
        logGaussianWave_norm V tau u hV, Complex.ofReal_mul]
      simp [logGaussianWave]
    . simp
  have hIntegral :
      (((integral volume fun u : Real =>
        norm (logGaussianPrimePowerStep X V tau m u)) : Real) : Complex) =
      integral volume (logGaussianPrimePowerStep X V 0 m) := by
    rw [<- integral_complex_ofReal]
    apply integral_congr_ae
    exact Filter.Eventually.of_forall hPoint
  have hRe := congrArg Complex.re hIntegral
  simp only [Complex.ofReal_re] at hRe
  rw [hRe, logGaussianPrimePowerStep_integral X V 0 m hX]
  exact (le_abs_self _).trans (Complex.abs_re_le_norm _)

theorem logGaussianPrimePowerStep_summable_integral_norm
    (X V tau : Real) (hX : 0 < X) (hV : 0 < V) :
    Summable (fun m : Nat => integral volume fun u : Real =>
      norm (logGaussianPrimePowerStep X V tau m u)) := by
  have hMajor := (logGaussian_vonMangoldt_weight_summable X V 0 2 hX hV (by norm_num)).norm
  exact Summable.of_nonneg_of_le
    (fun m => integral_nonneg fun u => norm_nonneg (logGaussianPrimePowerStep X V tau m u))
    (fun m => logGaussianPrimePowerStep_integral_norm_le X V tau m hX hV) hMajor

end PrimeFactorOscillations.PrimeClassDeletion

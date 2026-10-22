/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.LogGaussianPerronWeight

/-!
# The physical cumulative Gaussian weight

The multiplicative Perron weight is exactly the Gaussian tail above
log(n)-log(X), with the same modulation and normalization as the paper.
-/

set_option autoImplicit false
set_option Elab.async false

open MeasureTheory Set

namespace PrimeFactorOscillations.PrimeClassDeletion

noncomputable def logGaussianWave (V tau u : Real) : Complex :=
  (logGaussianDensity V u : Complex) *
    Complex.exp (-(tau : Complex) * Complex.I * (u : Complex))

theorem logGaussianWave_integrable (V tau : Real) (hV : 0 < V) :
    Integrable (logGaussianWave V tau) := by
  exact logGaussianDensity_integrable_complex_moment V hV (-(tau : Complex) * Complex.I)

theorem logGaussianWave_norm (V tau u : Real) (hV : 0 < V) :
    norm (logGaussianWave V tau u) = logGaussianDensity V u := by
  have hd : 0 < logGaussianDensity V u :=
    div_pos (Real.exp_pos _) (Real.sqrt_pos.mpr (by positivity))
  have hp : (-(tau : Complex) * Complex.I * (u : Complex)).re = 0 := by
    simp [Complex.mul_re, Complex.mul_im]
  rw [logGaussianWave, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hd,
    Complex.norm_exp, hp, Real.exp_zero, mul_one]

theorem logGaussianSpectralTail_zero_eq_physical_tail
    (X V tau n : Real) (hn : 0 < n) :
    logGaussianSpectralTail X V tau n 0 =
      integral (volume.restrict (Ioi (Real.log n - Real.log X))) (logGaussianWave V tau) := by
  let a : Real := Real.log n - Real.log X
  let g : Real -> Complex := fun w => logGaussianWave V tau (w + a)
  have hLog := integral_comp_log_Ioi g (a := (1 : Real)) (by norm_num)
  have hFirst : logGaussianSpectralTail X V tau n 0 =
      integral (volume.restrict (Ioi (1 : Real))) (fun u : Real =>
        ((Inv.inv u : Real) : Complex) * g (Real.log u)) := by
    unfold logGaussianSpectralTail
    apply setIntegral_congr_fun measurableSet_Ioi
    intro u hu
    dsimp only
    have huPos : 0 < u := lt_trans Real.zero_lt_one hu
    rw [Real.log_mul hn.ne' huPos.ne']
    simp only [zero_sub, Complex.cpow_neg_one]
    have he : Real.log n + Real.log u - Real.log X = Real.log u + a := by
      dsimp [a]
      ring
    rw [he]
    simp only [g, logGaussianWave, Complex.ofReal_inv]
  have hMiddle : integral (volume.restrict (Ioi (1 : Real))) (fun u : Real =>
      ((Inv.inv u : Real) : Complex) * g (Real.log u)) =
      integral (volume.restrict (Ioi (0 : Real))) g := by
    simpa only [Real.log_one, RCLike.real_smul_eq_coe_mul] using! hLog
  let F : Real -> Complex := (Ioi a).indicator (logGaussianWave V tau)
  have hShift : integral volume (fun w : Real => F (w + a)) = integral volume F :=
    integral_add_right_eq_self F a
  have hPoint (w : Real) :
      F (w + a) = (Ioi (0 : Real)).indicator g w := by
    have he : a < w + a <-> 0 < w := by constructor <;> intro h <;> linarith
    simp only [F, Set.indicator, mem_Ioi, he, g]
  have hLast : integral (volume.restrict (Ioi (0 : Real))) g =
      integral (volume.restrict (Ioi a)) (logGaussianWave V tau) := by
    calc
      _ = integral volume ((Ioi (0 : Real)).indicator g) :=
        (integral_indicator measurableSet_Ioi).symm
      _ = integral volume (fun w : Real => F (w + a)) := by
        apply integral_congr_ae
        exact Filter.Eventually.of_forall fun w => (hPoint w).symm
      _ = integral volume F := hShift
      _ = _ := integral_indicator measurableSet_Ioi
  exact hFirst.trans (hMiddle.trans hLast)

end PrimeFactorOscillations.PrimeClassDeletion

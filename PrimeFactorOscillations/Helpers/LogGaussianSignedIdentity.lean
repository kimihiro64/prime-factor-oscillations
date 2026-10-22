/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.LogGaussianXiInterchange

/-!
# The complete signed safe-line identity for the actual Gaussian Mellin test

The constant, paired multiplicity-counted xi sum, reference pole and gamma
term remain coupled. Integrability and sum interchange are proved for the
actual test. This unnormalized vertical integral is not yet identified
with the physical prime-error probe, and no left-contour error is asserted.
-/

set_option autoImplicit false
set_option Elab.async false

namespace PrimeFactorOscillations.PrimeClassDeletion

open MeasureTheory Complex

noncomputable def logGaussianVerticalKernel (X V tau t : Real) : Complex :=
  logGaussianMellinKernel X V tau ((3 / 2 : Complex) + (t : Complex) * Complex.I)

noncomputable def logGaussianXiConstant : Complex :=
  -logDeriv Complex.riemannXi 0 - (1 / 2 : Complex) * (Real.log Real.pi : Complex) -
    (Real.eulerMascheroniConstant : Complex) / 2

noncomputable def logGaussianGammaMultiplier (t : Real) : Complex :=
  (1 / 2 : Complex) * Complex.digamma
    (((3 / 2 : Complex) + (t : Complex) * Complex.I) / 2 + 1) +
      (Real.eulerMascheroniConstant : Complex) / 2

theorem logGaussian_safeLine_signed_identity (X V tau : Real) (hX : 0 < X) (hV : 0 < V) :
    let H : Real -> Complex := logGaussianVerticalKernel X V tau
    And (Integrable (fun t : Real =>
        (-deriv riemannZeta ((3 / 2 : Complex) + (t : Complex) * Complex.I) /
          riemannZeta ((3 / 2 : Complex) + (t : Complex) * Complex.I)) * H t))
      (integral volume (fun t : Real =>
        (-deriv riemannZeta ((3 / 2 : Complex) + (t : Complex) * Complex.I) /
          riemannZeta ((3 / 2 : Complex) + (t : Complex) * Complex.I)) * H t) =
        logGaussianXiConstant * integral volume H -
          tsum (fun p : RiemannXiDivisorZeroIndex => integral volume (fun t : Real =>
            H t * (1 / ((3 / 2 : Complex) + (t : Complex) * Complex.I - riemannXiDivisorZeroValue p) +
              1 / riemannXiDivisorZeroValue p))) +
          integral volume (fun t : Real => H t /
            ((3 / 2 : Complex) + (t : Complex) * Complex.I - 1)) +
          integral volume (fun t : Real => H t * logGaussianGammaMultiplier t)) := by
  let H : Real -> Complex := logGaussianVerticalKernel X V tau
  let C : Real := logGaussianMajorant X V tau (3 / 2)
  let Z : Real -> Complex := fun t => H t *
    tsum (fun p : RiemannXiDivisorZeroIndex =>
      1 / ((3 / 2 : Complex) + (t : Complex) * Complex.I - riemannXiDivisorZeroValue p) +
        1 / riemannXiDivisorZeroValue p)
  let B : Real -> Complex := fun t => H t /
    ((3 / 2 : Complex) + (t : Complex) * Complex.I - 1)
  let G : Real -> Complex := fun t => H t * logGaussianGammaMultiplier t
  have hcast : ((3 / 2 : Real) : Complex) = (3 / 2 : Complex) := by norm_num
  have hH : Integrable H := by
    change Integrable (fun t : Real => logGaussianMellinKernel X V tau
      ((3 / 2 : Complex) + (t : Complex) * Complex.I))
    simpa only [hcast] using
      logGaussianMellinKernel_integrable_vertical X V tau (3 / 2) hX hV (by norm_num)
  have hC : 0 <= C := (logGaussianMajorant_pos X V tau (3 / 2) hX hV).le
  have hBound (t : Real) : norm (H t) <= C *
      (Inv.inv (norm ((3 / 2 : Complex) + (t : Complex) * Complex.I))) ^ (2 : Nat) := by
    simpa only [H, C, logGaussianVerticalKernel, hcast] using
      logGaussianMellinKernel_inverse_square_bound X V tau (3 / 2) t hX hV (by norm_num)
  have hZ : Integrable Z := logGaussian_xi_series_integrable X V tau hX hV
  have hB : Integrable B := by
    have h := Robin1984.integrable_vertical_resolvent hH (c := (3 / 2 : Real))
      (rho := (1 : Complex)) (by norm_num)
    simpa only [B, hcast] using h
  have hG : Integrable G := Robin1984.integrable_shifted_gamma_test hH hC hBound
  have hConst : Integrable (fun t : Real => logGaussianXiConstant * H t) :=
    hH.const_mul logGaussianXiConstant
  have hSource (t : Real) :
      (-deriv riemannZeta ((3 / 2 : Complex) + (t : Complex) * Complex.I) /
        riemannZeta ((3 / 2 : Complex) + (t : Complex) * Complex.I)) * H t =
      logGaussianXiConstant * H t - Z t + B t + G t := by
    rw [Robin1984.neg_riemannZeta_logDeriv_eq_xiDivisor_tsum (by norm_num)]
    dsimp only [logGaussianXiConstant, logGaussianGammaMultiplier, Z, B, G]
    ring
  have hQ : Integrable (fun t : Real =>
      (-deriv riemannZeta ((3 / 2 : Complex) + (t : Complex) * Complex.I) /
        riemannZeta ((3 / 2 : Complex) + (t : Complex) * Complex.I)) * H t) := by
    apply (((hConst.sub hZ).add hB).add hG).congr
    exact Filter.Eventually.of_forall (fun t => (hSource t).symm)
  have hIntegral : integral volume (fun t : Real =>
      (-deriv riemannZeta ((3 / 2 : Complex) + (t : Complex) * Complex.I) /
        riemannZeta ((3 / 2 : Complex) + (t : Complex) * Complex.I)) * H t) =
      logGaussianXiConstant * integral volume H - integral volume Z +
        integral volume B + integral volume G := by
    calc
      _ = integral volume (fun t : Real => logGaussianXiConstant * H t - Z t + B t + G t) :=
        integral_congr_ae (Filter.Eventually.of_forall hSource)
      _ = _ := by
        have hAdd := integral_add ((hConst.sub hZ).add hB) hG
        have hMid := integral_add (hConst.sub hZ) hB
        have hSub := integral_sub hConst hZ
        simp only [Pi.add_apply, Pi.sub_apply] at hAdd hMid hSub
        rw [hAdd, hMid, hSub, integral_const_mul]
  have hZeros : integral volume Z =
      tsum (fun p : RiemannXiDivisorZeroIndex => integral volume (fun t : Real =>
        H t * (1 / ((3 / 2 : Complex) + (t : Complex) * Complex.I - riemannXiDivisorZeroValue p) +
          1 / riemannXiDivisorZeroValue p))) := by
    have hswap := logGaussian_xi_integral_tsum X V tau hX hV
    dsimp only [H, logGaussianVerticalKernel]
    rw [hswap]
    apply integral_congr_ae
    exact Filter.Eventually.of_forall (fun t => by
      dsimp only [Z, H, logGaussianVerticalKernel]
      rw [tsum_mul_left])
  refine And.intro hQ ?_
  rw [hIntegral, hZeros]

end PrimeFactorOscillations.PrimeClassDeletion

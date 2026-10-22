/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.LogGaussianGammaRemainder
import PrimeFactorOscillations.Helpers.LogGaussianLeftMomentBound
import PrimeFactorOscillations.Helpers.LogGaussianPhysicalResidues

/-!
# The unconditional full physical Gaussian explicit formula

The actual psi probe equals the complete absolutely convergent xi-residue
series, the exact archimedean constant and a uniformly bounded remainder.
All multiplicities are retained through the canonical divisor-zero index.
-/

set_option autoImplicit false
set_option Elab.async false

open MeasureTheory

namespace PrimeFactorOscillations.PrimeClassDeletion

noncomputable def logGaussianExplicitRemainder (X V tau : Real) : Complex :=
  tsum (fun p : RiemannXiDivisorZeroIndex =>
    logGaussianLeftZeroError X V tau (riemannXiDivisorZeroValue p)) +
  (Real.log (2 * Real.pi) : Complex) * logGaussianLeftMoment X V tau 0 -
    logGaussianLeftMoment X V tau 1 +
  tsum (fun k : Nat =>
    logGaussianSpectralTail X V tau 1 (-(2 * ((k : Complex) + 1))) /
      (2 * ((k : Complex) + 1)))

noncomputable def logGaussianExplicitErrorConstant (tau : Real) : Real :=
  (5 + abs tau) * tsum (fun p : RiemannXiDivisorZeroIndex =>
    (Inv.inv (norm (riemannXiDivisorZeroValue p))) ^ (2 : Nat)) +
    abs (Real.log (2 * Real.pi)) + 1 / 2 + tsum logGaussianGammaTailWeight

theorem logGaussian_zero_frequency_moment (V tau : Real) :
    Complex.exp ((V : Complex) / 2 * ((0 : Complex) - (tau : Complex) * Complex.I) ^ 2) =
      (Real.exp (-V * tau ^ 2 / 2) : Complex) := by
  have he : (V : Complex) / 2 * ((0 : Complex) - (tau : Complex) * Complex.I) ^ 2 =
      ((-V * tau ^ 2 / 2 : Real) : Complex) := by
    simp only [zero_sub, neg_sq, mul_pow, Complex.I_sq]
    push_cast
    ring
  rw [he, Complex.ofReal_exp]

theorem logGaussianPsiProbe_eq_explicit_formula
    (X V tau : Real) (hX : 0 < X) (hV : 1 <= V) :
    logGaussianPsiProbe X V tau =
      -tsum (fun p : RiemannXiDivisorZeroIndex =>
        logGaussianZeroResidue X V tau (riemannXiDivisorZeroValue p)) -
      (Real.log (2 * Real.pi) : Complex) * (Real.exp (-V * tau ^ 2 / 2) : Complex) +
      logGaussianExplicitRemainder X V tau := by
  have hVPos : 0 < V := lt_of_lt_of_le Real.zero_lt_one hV
  let H : Real -> Complex := logGaussianVerticalKernel X V tau
  let C : Complex := (((1 / (2 * Real.pi) : Real) : Complex))
  have h0 := logGaussian_constant_pairing X V tau hX hVPos
  have h1 := logGaussian_reference_pole_pairing X V tau hX hVPos
  have hGamma := logGaussian_complete_gamma_pairing X V tau hX hVPos
  have hPhysical := logGaussianPsiProbe_eq_full_signed_zero_residues X V tau hX hV
  dsimp only at hPhysical
  have hReference :
      C * (logGaussianXiConstant * integral volume H +
        integral volume (fun t : Real => H t /
          ((3 / 2 : Complex) + (t : Complex) * Complex.I - 1))) -
      (X : Complex) * Complex.exp ((V : Complex) / 2 *
        ((1 : Complex) - (tau : Complex) * Complex.I) ^ 2) =
      -(Real.log (2 * Real.pi) : Complex) *
        (Real.exp (-V * tau ^ 2 / 2) : Complex) +
      (Real.log (2 * Real.pi) : Complex) * logGaussianLeftMoment X V tau 0 -
        logGaussianLeftMoment X V tau 1 := by
    have hComm : C * (logGaussianXiConstant * integral volume H) =
      logGaussianXiConstant * (C * integral volume H) := by ring
    rw [mul_add, hComm]
    change logGaussianXiConstant *
      ((((1 / (2 * Real.pi) : Real) : Complex)) *
        integral volume (logGaussianVerticalKernel X V tau)) +
      (((1 / (2 * Real.pi) : Real) : Complex)) *
        integral volume (fun t : Real => logGaussianVerticalKernel X V tau t /
          ((3 / 2 : Complex) + (t : Complex) * Complex.I - 1)) - _ = _
    rw [h0, h1, logGaussian_centered_reference_identity X V tau hX hVPos,
      logGaussian_zero_frequency_moment]
  calc
    logGaussianPsiProbe X V tau =
      (C * (logGaussianXiConstant * integral volume H +
        integral volume (fun t : Real => H t /
          ((3 / 2 : Complex) + (t : Complex) * Complex.I - 1))) -
        (X : Complex) * Complex.exp ((V : Complex) / 2 *
          ((1 : Complex) - (tau : Complex) * Complex.I) ^ 2)) -
      tsum (fun p : RiemannXiDivisorZeroIndex =>
        logGaussianZeroResidue X V tau (riemannXiDivisorZeroValue p)) +
      tsum (fun p : RiemannXiDivisorZeroIndex =>
        logGaussianLeftZeroError X V tau (riemannXiDivisorZeroValue p)) +
      C * integral volume (fun t : Real => H t * logGaussianGammaMultiplier t) := by
        rw [hPhysical]
        dsimp only [H, C]
        ring
    _ = _ := by
      rw [hReference]
      dsimp only [H, C]
      rw [hGamma]
      dsimp only [logGaussianExplicitRemainder]
      ring

theorem logGaussianExplicitRemainder_norm_bound
    (X V tau : Real) (hX : 0 < X) (hV : 1 <= V) :
    norm (logGaussianExplicitRemainder X V tau) <=
      logGaussianExplicitErrorConstant tau * logGaussianTailScale V / X := by
  have hVPos : 0 < V := lt_of_lt_of_le Real.zero_lt_one hV
  let E : Complex := tsum (fun p : RiemannXiDivisorZeroIndex =>
    logGaussianLeftZeroError X V tau (riemannXiDivisorZeroValue p))
  let L : Complex := (Real.log (2 * Real.pi) : Complex) * logGaussianLeftMoment X V tau 0
  let A : Complex := logGaussianLeftMoment X V tau 1
  let G : Complex := tsum (fun k : Nat =>
    logGaussianSpectralTail X V tau 1 (-(2 * ((k : Complex) + 1))) /
      (2 * ((k : Complex) + 1)))
  have hE := logGaussianLeftZeroError_xi_sum_norm_bound X V tau hX hV
  have h0 : norm (logGaussianLeftMoment X V tau 0) <= logGaussianTailScale V / X := by
    simpa only [Complex.zero_re, zero_add, mul_one] using
      logGaussianLeftMoment_norm_bound X V tau 0 hX hVPos (by norm_num)
  have h1 : norm A <= logGaussianTailScale V / (X * 2) := by
    simpa only [A, Complex.one_re, show (1 : Real) + 1 = 2 by norm_num] using
      logGaussianLeftMoment_norm_bound X V tau 1 hX hVPos (by norm_num)
  have hL : norm L <= abs (Real.log (2 * Real.pi)) * (logGaussianTailScale V / X) := by
    dsimp only [L]
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_left h0 (abs_nonneg _)
  have hG := logGaussian_gamma_tail_sum_norm_bound X V tau hX hVPos
  change norm (E + L - A + G) <= _
  calc
    _ <= norm (E + L - A) + norm G := norm_add_le _ _
    _ <= (norm (E + L) + norm A) + norm G :=
      add_le_add (norm_sub_le (E + L) A) (le_refl (norm G))
    _ <= ((norm E + norm L) + norm A) + norm G :=
      add_le_add (add_le_add (norm_add_le E L) (le_refl (norm A))) (le_refl (norm G))
    _ <= ((((5 + abs tau) * logGaussianTailScale V / X) *
        tsum (fun p : RiemannXiDivisorZeroIndex =>
          (Inv.inv (norm (riemannXiDivisorZeroValue p))) ^ (2 : Nat)) +
        abs (Real.log (2 * Real.pi)) * (logGaussianTailScale V / X)) +
        logGaussianTailScale V / (X * 2)) +
        (logGaussianTailScale V / X) * tsum logGaussianGammaTailWeight :=
      add_le_add (add_le_add (add_le_add hE hL) h1) hG
    _ = _ := by
      dsimp only [logGaussianExplicitErrorConstant]
      ring

theorem logGaussianExplicitErrorConstant_nonneg (tau : Real) :
    0 <= logGaussianExplicitErrorConstant tau := by
  unfold logGaussianExplicitErrorConstant
  have hXi : 0 <= tsum (fun p : RiemannXiDivisorZeroIndex =>
      (Inv.inv (norm (riemannXiDivisorZeroValue p))) ^ (2 : Nat)) :=
    tsum_nonneg fun p => sq_nonneg _
  have hGamma : 0 <= tsum logGaussianGammaTailWeight :=
    tsum_nonneg logGaussianGammaTailWeight_nonneg
  positivity

theorem logGaussianExplicitRemainder_log_scale_bound
    (X c tau : Real) (hX : 0 < X) (hV : 1 <= c * Real.log X) :
    norm (logGaussianExplicitRemainder X (c * Real.log X) tau) <=
      logGaussianExplicitErrorConstant tau * X ^ (-1 + c / 2) := by
  let V : Real := c * Real.log X
  have hProduct : 2 * Real.pi <= 2 * Real.pi * V := by
    have h := mul_le_mul_of_nonneg_left hV (by positivity : 0 <= 2 * Real.pi)
    simpa only [mul_one] using h
  have hInside : (1 : Real) <= 2 * Real.pi * V := by
    linarith only [hProduct, Real.pi_gt_three]
  have hDen : (1 : Real) <= Real.sqrt (2 * Real.pi * V) := by
    simpa only [Real.sqrt_one] using Real.sqrt_le_sqrt hInside
  have hScale : logGaussianTailScale V <= Real.exp (V / 2) :=
    div_le_self (Real.exp_pos _).le hDen
  have hExp : Real.exp (V / 2) / X = X ^ (-1 + c / 2) := by
    apply (div_eq_iff hX.ne').mpr
    rw [Real.rpow_def_of_pos hX]
    calc
      Real.exp (V / 2) =
          Real.exp (Real.log X * (-1 + c / 2)) * Real.exp (Real.log X) := by
        rw [<- Real.exp_add]
        congr 1
        dsimp only [V]
        ring
      _ = _ := by rw [Real.exp_log hX]
  calc
    _ <= logGaussianExplicitErrorConstant tau * logGaussianTailScale V / X :=
      logGaussianExplicitRemainder_norm_bound X V tau hX hV
    _ <= logGaussianExplicitErrorConstant tau * Real.exp (V / 2) / X :=
      div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_left hScale (logGaussianExplicitErrorConstant_nonneg tau)) hX.le
    _ = _ := by rw [mul_div_assoc, hExp]

end PrimeFactorOscillations.PrimeClassDeletion

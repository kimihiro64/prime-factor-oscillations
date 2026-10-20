/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/

import PrimeFactorOscillations.Assembly.DetectorPackets.GaussianCenteredPoisson

/-!
# GaussianMellinWavelet

Maintained extraction of completed detector/packet proof components.
All original theorem hypotheses and retained proof bodies are preserved.
This module alone asserts no improved zero-free boundary.
-/

set_option autoImplicit false
set_option Elab.async false

/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/

/-!
# A zero-preserving three-scale probe with no Fourier zero mode

The normalized coefficients have total absolute mass one. The construction
kills the origin and Fourier zero mode, while its Mellin multiplier has
no zeros in the open critical strip. The actual masked principal packet
therefore equals its signed nonzero Fourier kernel. No arithmetic moment
bound or zero-free improvement is asserted.
-/


noncomputable section
namespace PrimeFactorOscillations.GaussianMellinWavelet

open GaussianMobiusDivisors GaussianIdealPoisson GaussianCoprimePoisson
open GaussianCenteredPoisson
open OAI.EisensteinSchwartzPoisson
open scoped BigOperators FourierTransform SchwartzMap Classical

def dilation (f : SchwartzMap Complex Complex) (r : Real) (hr : 0 < r) :
    SchwartzMap Complex Complex :=
  affinePullback f (complexMulEquiv (Real.sqrt r : Complex)
    (Complex.ofReal_ne_zero.mpr (ne_of_gt (Real.sqrt_pos.mpr hr)))) 0

theorem dilation_apply (f : SchwartzMap Complex Complex) (r : Real) (hr : 0 < r)
    (z : Complex) : dilation f r hr z = f ((Real.sqrt r : Complex) * z) := by
  simp only [dilation, affinePullback_apply, complexMulEquiv_apply, add_zero]

theorem dilation_fourier_zero (f : SchwartzMap Complex Complex) (r : Real) (hr : 0 < r) :
    (FourierTransform.fourier (dilation f r hr)) 0 =
      (r : Complex) ^ (-1 : Int) * (FourierTransform.fourier f) 0 := by
  let A := complexMulEquiv (Real.sqrt r : Complex)
    (Complex.ofReal_ne_zero.mpr (ne_of_gt (Real.sqrt_pos.mpr hr)))
  have hj : inverseJacobian A = Inv.inv r := by
    unfold inverseJacobian
    dsimp only [A]
    rw [complexMulEquiv_det, Complex.normSq_ofReal, <- pow_two,
      Real.sq_sqrt hr.le, abs_of_pos (inv_pos.mpr hr)]
  have h := fourier_affinePullback f A 0 0
  have hz : dualMap A 0 = 0 := (dualMap A).map_zero
  rw [hj, hz] at h
  simpa [dilation, A, Algebra.smul_def] using h

def window (W : Real -> Complex) (x : Real) : Complex :=
  (W x - 3 * W (2 * x) + 2 * W (4 * x)) / 6

def wavelet (f : SchwartzMap Complex Complex) : SchwartzMap Complex Complex :=
  HSMul.hSMul (1 / 6 : Complex) (f - HSMul.hSMul (3 : Complex) (dilation f 2 (by norm_num)) +
    HSMul.hSMul (2 : Complex) (dilation f 4 (by norm_num)))

theorem wavelet_apply (f : SchwartzMap Complex Complex) (z : Complex) :
    wavelet f z = (f z - 3 * dilation f 2 (by norm_num) z +
      2 * dilation f 4 (by norm_num) z) / 6 := by
  change (1 / 6 : Complex) * (f z - 3 * dilation f 2 (by norm_num) z +
    2 * dilation f 4 (by norm_num) z) = _
  ring

theorem window_zero (W : Real -> Complex) : window W 0 = 0 := by
  simp only [window, mul_zero]
  ring

theorem wavelet_zero (f : SchwartzMap Complex Complex) : wavelet f 0 = 0 := by
  rw [wavelet_apply, dilation_apply, dilation_apply]
  simp only [mul_zero]
  ring

theorem dilation_radial (f : SchwartzMap Complex Complex) (W : Real -> Complex)
    (hW : forall z : Complex, f z = W (Complex.normSq z))
    (r : Real) (hr : 0 < r) (z : Complex) :
    dilation f r hr z = W (r * Complex.normSq z) := by
  rw [dilation_apply, hW, Complex.normSq_mul, Complex.normSq_ofReal,
    <- pow_two, Real.sq_sqrt hr.le]

theorem wavelet_radial (f : SchwartzMap Complex Complex) (W : Real -> Complex)
    (hW : forall z : Complex, f z = W (Complex.normSq z)) :
    forall z : Complex, wavelet f z = window W (Complex.normSq z) := by
  intro z
  rw [wavelet_apply, dilation_radial f W hW, dilation_radial f W hW, hW]
  rfl

theorem wavelet_fourier_zero (f : SchwartzMap Complex Complex) :
    (FourierTransform.fourier (wavelet f)) 0 = 0 := by
  have h2 : ((SchwartzMap.fourierTransformCLM Complex)
      (dilation f 2 (by norm_num))) 0 =
      (1 / 2 : Complex) * ((SchwartzMap.fourierTransformCLM Complex) f) 0 := by
    simpa using dilation_fourier_zero f 2 (by norm_num)
  have h4 : ((SchwartzMap.fourierTransformCLM Complex)
      (dilation f 4 (by norm_num))) 0 =
      (1 / 4 : Complex) * ((SchwartzMap.fourierTransformCLM Complex) f) 0 := by
    simpa using dilation_fourier_zero f 4 (by norm_num)
  change ((SchwartzMap.fourierTransformCLM Complex) (wavelet f)) 0 = 0
  simp only [wavelet, map_smul, map_add, map_sub, smul_apply, sub_apply, add_apply,
    smul_eq_mul]
  rw [h2, h4]
  ring

def dyadicPhase (s : Complex) : Complex :=
  Complex.exp (-(s * (Real.log 2 : Real)))

def multiplier (s : Complex) : Complex :=
  ((1 - dyadicPhase s) * (1 - 2 * dyadicPhase s)) / 6

theorem dyadicPhase_norm (s : Complex) :
    norm (dyadicPhase s) = Real.exp (-(s.re * Real.log 2)) := by
  rw [dyadicPhase, Complex.norm_exp]
  congr 1
  simp only [Complex.neg_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    mul_zero, sub_zero]

theorem phase_norm_range (s : Complex) (hlo : 0 < s.re) (hhi : s.re < 1) :
    (1 / 2 : Real) < norm (dyadicPhase s) /\ norm (dyadicPhase s) < 1 := by
  have hl : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have he : Real.exp (-(Real.log 2)) = (1 / 2 : Real) := by
    rw [Real.exp_neg, Real.exp_log (by norm_num : (0 : Real) < 2)]
    norm_num
  simp only [dyadicPhase_norm]
  constructor
  . rw [<- he]
    apply Real.exp_lt_exp.mpr
    nlinarith
  . apply Real.exp_lt_one_iff.mpr
    nlinarith

theorem multiplier_ne_zero (s : Complex) (hlo : 0 < s.re) (hhi : s.re < 1) :
    Not (multiplier s = 0) := by
  have hr := phase_norm_range s hlo hhi
  have h1 : Not ((1 : Complex) - dyadicPhase s = 0) := by
    intro h
    have he := (sub_eq_zero.mp h).symm
    have hn := hr.2
    rw [he, norm_one] at hn
    linarith
  have h2 : Not ((1 : Complex) - 2 * dyadicPhase s = 0) := by
    intro h
    have he := (sub_eq_zero.mp h).symm
    have hn := congrArg norm he
    rw [norm_mul] at hn
    norm_num at hn
    nlinarith [hr.1]
  exact div_ne_zero (mul_ne_zero h1 h2) (by norm_num)

def powerWave (s : Complex) (D : Real) : Complex :=
  Complex.exp (s * (Real.log D : Real))

def filterValue (A : Real -> Complex) (D : Real) : Complex :=
  (A D - 3 * A (D / 2) + 2 * A (D / 4)) / 6

theorem powerWave_half (s : Complex) (D : Real) (hD : 0 < D) :
    powerWave s (D / 2) = powerWave s D * dyadicPhase s := by
  unfold powerWave dyadicPhase
  rw [Real.log_div hD.ne' (by norm_num : Not ((2 : Real) = 0)), Complex.ofReal_sub]
  have he : s * ((Real.log D : Complex) - (Real.log 2 : Complex)) =
      s * (Real.log D : Complex) + -(s * (Real.log 2 : Complex)) := by ring
  rw [he, Complex.exp_add]

theorem powerWave_filter (s : Complex) (D : Real) (hD : 0 < D) :
    filterValue (powerWave s) D = powerWave s D * multiplier s := by
  have h4 : powerWave s (D / 4) = powerWave s D * dyadicPhase s ^ 2 := by
    rw [show D / 4 = (D / 2) / 2 by ring,
      powerWave_half s (D / 2) (div_pos hD (by norm_num)), powerWave_half s D hD]
    ring
  rw [filterValue, powerWave_half s D hD, h4, multiplier]
  ring

theorem filtered_principal_packet (S : Finset Pair) (H : Ideal G) (hH : Not (H = 0))
    (D : Real) (hD : 0 < D) (f : SchwartzMap Complex Complex) (W : Real -> Complex)
    (hW : forall z : Complex, f z = W (Complex.normSq z)) :
    pairPacket S H D (window W) = pairTail S H D (wavelet f) := by
  have h := packet_exact S H hH D hD (wavelet f) (window W)
    (wavelet_radial f W hW) (window_zero W)
  rw [wavelet_fourier_zero] at h
  simpa only [mul_zero, zero_mul, zero_add] using h

theorem window_bound (W : Real -> Complex) (B : Real)
    (hW : forall x : Real, norm (W x) <= B) (x : Real) :
    norm (window W x) <= B := by
  have h3 : norm ((3 : Complex) * W (2 * x)) <= 3 * B := by
    calc
      _ = 3 * norm (W (2 * x)) := by rw [norm_mul]; norm_num
      _ <= 3 * B := mul_le_mul_of_nonneg_left (hW (2 * x)) (by norm_num)
  have h2 : norm ((2 : Complex) * W (4 * x)) <= 2 * B := by
    calc
      _ = 2 * norm (W (4 * x)) := by rw [norm_mul]; norm_num
      _ <= 2 * B := mul_le_mul_of_nonneg_left (hW (4 * x)) (by norm_num)
  have hn : norm (W x - 3 * W (2 * x) + 2 * W (4 * x)) <=
      B + 3 * B + 2 * B :=
    (norm_add_le _ _).trans (add_le_add
      ((norm_sub_le _ _).trans (add_le_add (hW x) h3)) h2)
  calc
    _ = norm (W x - 3 * W (2 * x) + 2 * W (4 * x)) / 6 := by
      rw [window, norm_div]
      norm_num
    _ <= (B + 3 * B + 2 * B) / 6 :=
      div_le_div_of_nonneg_right hn (by norm_num)
    _ = B := by ring

def gap (s : Complex) : Real :=
  (1 - norm (dyadicPhase s)) * (2 * norm (dyadicPhase s) - 1) / 6

theorem gap_pos (s : Complex) (hlo : 0 < s.re) (hhi : s.re < 1) :
    0 < gap s := by
  have hr := phase_norm_range s hlo hhi
  unfold gap
  apply div_pos _ (by norm_num)
  apply mul_pos (by linarith : 0 < 1 - norm (dyadicPhase s))
  linarith

theorem multiplier_norm_lower (s : Complex) (hlo : 0 < s.re) (hhi : s.re < 1) :
    gap s <= norm (multiplier s) := by
  have hr := phase_norm_range s hlo hhi
  have h1 : 1 - norm (dyadicPhase s) <= norm (1 - dyadicPhase s) := by
    have ht := norm_add_le ((1 : Complex) - dyadicPhase s) (dyadicPhase s)
    rw [sub_add_cancel, norm_one] at ht
    linarith
  have h2 : 2 * norm (dyadicPhase s) - 1 <= norm (1 - 2 * dyadicPhase s) := by
    have ht := norm_sub_le (1 : Complex) (1 - 2 * dyadicPhase s)
    have he : (1 : Complex) - (1 - 2 * dyadicPhase s) = 2 * dyadicPhase s := by ring
    rw [he, norm_mul] at ht
    norm_num at ht
    linarith
  have hp := mul_le_mul h1 h2
    (by linarith : 0 <= 2 * norm (dyadicPhase s) - 1)
    (norm_nonneg ((1 : Complex) - dyadicPhase s))
  unfold gap multiplier
  rw [norm_div, norm_mul]
  have h6 : norm (6 : Complex) = (6 : Real) := by norm_num
  rw [h6]
  exact div_le_div_of_nonneg_right hp (by norm_num)

end PrimeFactorOscillations.GaussianMellinWavelet

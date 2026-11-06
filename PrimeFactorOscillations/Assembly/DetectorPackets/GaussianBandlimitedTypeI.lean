/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/

import PrimeFactorOscillations.Assembly.DetectorPackets.GaussianMellinWavelet

/-!
# Exact vanishing of bandlimited Gaussian Type I rows

Mean-zero Fourier support inside the unit disk annihilates every affine
Gaussian lattice sum at mesh norm at most one. Every shifted congruence coset
is covered; norm-character weights are kept exactly. Radial windows with zero
origin then annihilate the complete coprimality-masked principal Type I block.
The existing three-scale wavelet supplies both origin cancellations and needs
only half-unit Fourier support before its dilations.

Physical truncation corrections, nonzero Mellin witnesses in this window
class, and the retained Type II packet remain separate consumers.
No improved zero-free boundary or novelty priority is asserted.
-/

set_option autoImplicit false
set_option Elab.async false

noncomputable section
namespace PrimeFactorOscillations.GaussianBandlimitedTypeI

open GaussianMobiusDivisors GaussianPoisson GaussianIdealPoisson
open GaussianCoprimePoisson GaussianCenteredPoisson
open GaussianIdealPrincipalPacket (idealSum)
open OAI.EisensteinSchwartzPoisson
open scoped BigOperators FourierTransform SchwartzMap Classical

private theorem point_norm_one_le (p : Prod Int Int) (hp : Not (p = 0)) :
    1 <= norm (point p) := by
  have h := point_norm_sq_one_le p hp
  nlinarith [norm_nonneg (point p)]

private theorem dual_norm_one_le (c : Complex) (hc : Not (c = 0))
    (hsmall : norm c <= 1) (p : Prod Int Int) (hp : Not (p = 0)) :
    1 <= norm ((dualMap (complexMulEquiv c hc)) (point p)) := by
  rw [dual_mul_apply, norm_mul, norm_inv, Complex.norm_conj]
  rw [inv_mul_eq_div]
  have h := div_le_div_of_nonneg_right
    (hsmall.trans (point_norm_one_le p hp)) (norm_nonneg c)
  simpa only [div_self (ne_of_gt (norm_pos_iff.mpr hc))] using h

theorem affine_sum_zero (f : SchwartzMap Complex Complex)
    (hzero : (FourierTransform.fourier f) 0 = 0)
    (hband : forall z : Complex, 1 <= norm z -> (FourierTransform.fourier f) z = 0)
    (c : Complex) (hc : Not (c = 0)) (hsmall : norm c <= 1) (b : Complex) :
    (tsum fun p : Prod Int Int => f (c * point p + b)) = 0 := by
  have hz (p : Prod Int Int) :
      (FourierTransform.fourier f)
        ((dualMap (complexMulEquiv c hc)) (complexPoint (p.1 : Real) (p.2 : Real))) = 0 := by
    by_cases hp : p = 0
    . subst p
      have hp0 : complexPoint (((0 : Prod Int Int).1 : Int) : Real)
          (((0 : Prod Int Int).2 : Int) : Real) = 0 := by
        apply Complex.ext <;> simp [complexPoint]
      rw [hp0, (dualMap (complexMulEquiv c hc)).map_zero]
      exact hzero
    . exact hband _ (dual_norm_one_le c hc hsmall p hp)
  have h := affine_lattice_poisson f (complexMulEquiv c hc) b
  simp only [hz, smul_zero, tsum_zero] at h
  simpa only [complexMulEquiv_apply, point] using h

theorem scaled_coset_sum_zero (f : SchwartzMap Complex Complex)
    (hzero : (FourierTransform.fourier f) 0 = 0)
    (hband : forall z : Complex, 1 <= norm z -> (FourierTransform.fourier f) z = 0)
    (q X : Real) (hq : 0 < q) (hX : 0 < X) (hscale : q ^ 2 <= X)
    (r : Complex) :
    (tsum fun p : Prod Int Int =>
      f (Inv.inv (Real.sqrt X : Complex) * ((q : Complex) * point p + r))) = 0 := by
  have hs : 0 < Real.sqrt X := Real.sqrt_pos.mpr hX
  have hqroot : q <= Real.sqrt X := by
    nlinarith [Real.sq_sqrt hX.le, Real.sqrt_nonneg X]
  let c : Complex := Inv.inv (Real.sqrt X : Complex) * (q : Complex)
  have hc : Not (c = 0) := by
    exact mul_ne_zero (inv_ne_zero (Complex.ofReal_ne_zero.mpr hs.ne'))
      (Complex.ofReal_ne_zero.mpr hq.ne')
  have hn : norm c <= 1 := by
    dsimp only [c]
    rw [norm_mul, norm_inv, Complex.norm_real, Complex.norm_real,
      Real.norm_of_nonneg hs.le, Real.norm_of_nonneg hq.le, inv_mul_eq_div]
    exact (div_le_one hs).mpr hqroot
  have h := affine_sum_zero f hzero hband c hc hn
    (Inv.inv (Real.sqrt X : Complex) * r)
  convert h using 1
  congr 1
  funext p
  congr 1
  dsimp only [c]
  ring

private theorem ideal_sum_zero (f : SchwartzMap Complex Complex) (W : Real -> Complex)
    (hW : forall z : Complex, f z = W (Complex.normSq z)) (hWzero : W 0 = 0)
    (hzero : (FourierTransform.fourier f) 0 = 0)
    (hband : forall z : Complex, 1 <= norm z -> (FourierTransform.fourier f) z = 0)
    (X : Real) (hX : 1 <= X) :
    idealSum W X = 0 := by
  have hpos : 0 < X := lt_of_lt_of_le zero_lt_one hX
  have hr := radial_sum f W hW hWzero X hpos
  have he : (tsum fun z : G =>
      f (Inv.inv (Real.sqrt X : Complex) * embed z)) = 0 := by
    rw [gaussian_rescaled_poisson f X hpos]
    have hz (p : Prod Int Int) :
        (FourierTransform.fourier f) ((Real.sqrt X : Complex) * point p) = 0 := by
      by_cases hp : p = 0
      . subst p
        simpa only [point_zero, mul_zero] using hzero
      . apply hband
        rw [norm_mul, Complex.norm_real,
          Real.norm_of_nonneg (Real.sqrt_nonneg X)]
        have hs : 1 <= Real.sqrt X := by
          nlinarith [Real.sq_sqrt hpos.le, Real.sqrt_nonneg X]
        have hn := point_norm_one_le p hp
        nlinarith
    simp only [hz, tsum_zero, mul_zero]
  rw [he] at hr
  change (0 : Complex) = 4 * idealSum W X at hr
  exact (mul_eq_zero.mp hr.symm).resolve_left (by norm_num)

private theorem divisor_norm_le (H E : Ideal G) (hH : Not (H = 0))
    (hE : Membership.mem (divisors H) E) :
    (Ideal.absNorm E : Real) <= (Ideal.absNorm H : Real) := by
  have hp : 0 < Ideal.absNorm H :=
    Nat.pos_iff_ne_zero.mpr (fun hz => hH (Ideal.absNorm_eq_zero_iff.mp hz))
  have hd := map_dvd Ideal.absNorm ((mem_divisors hH).mp hE)
  exact_mod_cast Nat.le_of_dvd hp hd

private theorem masked_sum_zero (H : Ideal G) (hH : Not (H = 0))
    (f : SchwartzMap Complex Complex) (W : Real -> Complex)
    (hW : forall z : Complex, f z = W (Complex.normSq z)) (hWzero : W 0 = 0)
    (hzero : (FourierTransform.fourier f) 0 = 0)
    (hband : forall z : Complex, 1 <= norm z -> (FourierTransform.fourier f) z = 0)
    (X : Real) (hX : 0 < X) (hscale : (Ideal.absNorm H : Real) <= X) :
    maskedSum H W X = 0 := by
  rw [maskedSum_eq H hH W X hX (ideal_summable f W hW X hX)]
  apply Finset.sum_eq_zero
  intro E hE
  have hpos := GaussianCoprimePoisson.norm_pos E (divisor_ne_zero hH hE)
  have hle : 1 <= X / (Ideal.absNorm E : Real) := by
    have h := div_le_div_of_nonneg_right
      ((divisor_norm_le H E hH hE).trans hscale) hpos.le
    simpa only [div_self hpos.ne'] using h
  rw [ideal_sum_zero f W hW hWzero hzero hband _ hle, mul_zero]

theorem typeI_zero (A B : Finset NonzeroIdeal) (H : Ideal G)
    (hH : Not (H = 0)) (D : Real) (hD : 0 < D)
    (f : SchwartzMap Complex Complex) (W : Real -> Complex)
    (hW : forall z : Complex, f z = W (Complex.normSq z)) (hWzero : W 0 = 0)
    (hzero : (FourierTransform.fourier f) 0 = 0)
    (hband : forall z : Complex, 1 <= norm z -> (FourierTransform.fourier f) z = 0)
    (hscale : forall a, Membership.mem A a -> forall b, Membership.mem B b ->
      (Ideal.absNorm H : Real) *
        ((Ideal.absNorm a.val : Real) * (Ideal.absNorm b.val : Real)) <= D) :
    GaussianPrincipalTypeI.typeI A B H D W = 0 := by
  unfold GaussianPrincipalTypeI.typeI
  apply Finset.sum_eq_zero
  intro a ha
  apply Finset.sum_eq_zero
  intro b hb
  have hpos : 0 < (Ideal.absNorm a.val : Real) * (Ideal.absNorm b.val : Real) :=
    mul_pos (GaussianCoprimePoisson.norm_pos a.val a.property)
      (GaussianCoprimePoisson.norm_pos b.val b.property)
  have hsc := div_le_div_of_nonneg_right (hscale a ha b hb) hpos.le
  have he : ((Ideal.absNorm H : Real) *
      ((Ideal.absNorm a.val : Real) * (Ideal.absNorm b.val : Real))) /
      ((Ideal.absNorm a.val : Real) * (Ideal.absNorm b.val : Real)) =
      (Ideal.absNorm H : Real) := by
    field_simp [ne_of_gt (GaussianCoprimePoisson.norm_pos a.val a.property),
      ne_of_gt (GaussianCoprimePoisson.norm_pos b.val b.property)]
  rw [he] at hsc
  rw [masked_sum_zero H hH f W hW hWzero hzero hband _
    (div_pos hD hpos) hsc, mul_zero]

private theorem dilation_fourier_apply (f : SchwartzMap Complex Complex)
    (r : Real) (hr : 0 < r) (z : Complex) :
    (FourierTransform.fourier (GaussianMellinWavelet.dilation f r hr)) z =
      ((Inv.inv r : Real) : Complex) *
        (FourierTransform.fourier f) (Inv.inv (Real.sqrt r : Complex) * z) := by
  let A := complexMulEquiv (Real.sqrt r : Complex)
    (Complex.ofReal_ne_zero.mpr (ne_of_gt (Real.sqrt_pos.mpr hr)))
  have hj : inverseJacobian A = Inv.inv r := by
    unfold inverseJacobian
    dsimp only [A]
    rw [complexMulEquiv_det, Complex.normSq_ofReal, <- pow_two,
      Real.sq_sqrt hr.le, abs_of_pos (inv_pos.mpr hr)]
  have hd : dualMap A z = Inv.inv (Real.sqrt r : Complex) * z := by
    dsimp only [A]
    rw [dual_mul_apply]
    simp
  have h := fourier_affinePullback f A 0 z
  rw [hj, hd] at h
  simpa [GaussianMellinWavelet.dilation, A, Algebra.smul_def] using h

private theorem scaled_frequency_half_le (r : Real) (hr : 0 < r)
    (hr4 : r <= 4) (z : Complex) (hz : 1 <= norm z) :
    (1 / 2 : Real) <= norm (Inv.inv (Real.sqrt r : Complex) * z) := by
  have hs : 0 < Real.sqrt r := Real.sqrt_pos.mpr hr
  have hs2 : Real.sqrt r <= 2 := by
    nlinarith [Real.sq_sqrt hr.le, Real.sqrt_nonneg r]
  rw [norm_mul, norm_inv, Complex.norm_real,
    Real.norm_of_nonneg hs.le, inv_mul_eq_div]
  have h := div_le_div_of_nonneg_right
    (show (1 / 2 : Real) * Real.sqrt r <= norm z by linarith) hs.le
  have he : ((1 / 2 : Real) * Real.sqrt r) / Real.sqrt r = 1 / 2 := by
    field_simp [hs.ne']
  simpa only [he] using h

theorem wavelet_bandlimited (f : SchwartzMap Complex Complex)
    (hband : forall z : Complex, (1 / 2 : Real) <= norm z ->
      (FourierTransform.fourier f) z = 0) :
    forall z : Complex, 1 <= norm z ->
      (FourierTransform.fourier (GaussianMellinWavelet.wavelet f)) z = 0 := by
  intro z hz
  have h0 : (FourierTransform.fourier f) z = 0 :=
    hband z (le_trans (by norm_num) hz)
  have h2 : (FourierTransform.fourier
      (GaussianMellinWavelet.dilation f 2 (by norm_num))) z = 0 := by
    rw [dilation_fourier_apply, hband _ (scaled_frequency_half_le 2
      (by norm_num) (by norm_num) z hz), mul_zero]
  have h4 : (FourierTransform.fourier
      (GaussianMellinWavelet.dilation f 4 (by norm_num))) z = 0 := by
    rw [dilation_fourier_apply, hband _ (scaled_frequency_half_le 4
      (by norm_num) (by norm_num) z hz), mul_zero]
  change ((SchwartzMap.fourierTransformCLM Complex) (GaussianMellinWavelet.wavelet f)) z = 0
  simp only [GaussianMellinWavelet.wavelet, map_smul, map_add, map_sub,
    smul_apply, sub_apply, add_apply, smul_eq_mul]
  change (1 / 6 : Complex) * ((FourierTransform.fourier f) z -
    3 * (FourierTransform.fourier
      (GaussianMellinWavelet.dilation f 2 (by norm_num))) z +
    2 * (FourierTransform.fourier
      (GaussianMellinWavelet.dilation f 4 (by norm_num))) z) = 0
  rw [h0, h2, h4]
  ring

theorem wavelet_typeI_zero (A B : Finset NonzeroIdeal) (H : Ideal G)
    (hH : Not (H = 0)) (D : Real) (hD : 0 < D)
    (f : SchwartzMap Complex Complex) (W : Real -> Complex)
    (hW : forall z : Complex, f z = W (Complex.normSq z))
    (hband : forall z : Complex, (1 / 2 : Real) <= norm z ->
      (FourierTransform.fourier f) z = 0)
    (hscale : forall a, Membership.mem A a -> forall b, Membership.mem B b ->
      (Ideal.absNorm H : Real) *
        ((Ideal.absNorm a.val : Real) * (Ideal.absNorm b.val : Real)) <= D) :
    GaussianPrincipalTypeI.typeI A B H D (GaussianMellinWavelet.window W) = 0 := by
  exact typeI_zero A B H hH D hD (GaussianMellinWavelet.wavelet f)
    (GaussianMellinWavelet.window W) (GaussianMellinWavelet.wavelet_radial f W hW)
    (GaussianMellinWavelet.window_zero W) (GaussianMellinWavelet.wavelet_fourier_zero f)
    (wavelet_bandlimited f hband) hscale

theorem character_coset_sum_zero {q : Nat} (chi : DirichletCharacter Complex q)
    (hq : 0 < q) (f : SchwartzMap Complex Complex)
    (hzero : (FourierTransform.fourier f) 0 = 0)
    (hband : forall z : Complex, 1 <= norm z -> (FourierTransform.fourier f) z = 0)
    (X : Real) (hX : 0 < X) (hscale : (q : Real) ^ 2 <= X) :
    (Finset.univ : Finset (Prod (Fin q) (Fin q))).sum (fun r =>
      chi (((r.1.val : ZMod q) ^ 2) + ((r.2.val : ZMod q) ^ 2)) *
        (tsum fun p : Prod Int Int =>
          f (Inv.inv (Real.sqrt X : Complex) * ((q : Complex) * point p +
            complexPoint (r.1.val : Real) (r.2.val : Real))))) = 0 := by
  apply Finset.sum_eq_zero
  intro r hr
  have hz : (tsum fun p : Prod Int Int =>
      f (Inv.inv (Real.sqrt X : Complex) * ((q : Complex) * point p +
        complexPoint (r.1.val : Real) (r.2.val : Real)))) = 0 := by
    simpa only [Complex.ofReal_natCast] using
      scaled_coset_sum_zero f hzero hband (q : Real) X
        (by exact_mod_cast hq) hX hscale
        (complexPoint (r.1.val : Real) (r.2.val : Real))
  rw [hz, mul_zero]

end PrimeFactorOscillations.GaussianBandlimitedTypeI

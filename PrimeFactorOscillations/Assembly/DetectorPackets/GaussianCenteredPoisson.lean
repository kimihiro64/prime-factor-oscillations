/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/

import PrimeFactorOscillations.Assembly.DetectorPackets.GaussianPrincipalTypeI

/-!
# GaussianCenteredPoisson

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
# Exact signed Fourier kernel for the centered principal Gaussian packet

The long-pair zero mode is retained after subtracting the short main.
All ideal-divisor Mobius masks and all nonzero Fourier modes stay signed.
This identity is valid at every positive cofactor scale. It supplies the
actual principal kernel to the centered Type II moment, not a moment bound.
-/


noncomputable section
namespace PrimeFactorOscillations.GaussianCenteredPoisson

open GaussianMobiusDivisors GaussianIdealNorm GaussianPoisson GaussianIdealPoisson
open GaussianCoprimePoisson GaussianIdealPrincipalPacket
open GaussianPrincipalTypeI (mu inverseSum)
open OAI.EisensteinSchwartzPoisson
open scoped BigOperators FourierTransform SchwartzMap Classical

def fourierTail (f : SchwartzMap Complex Complex) (X : Real) : Complex :=
  tsum fun k : Prod Int Int => if k = 0 then 0 else
    (FourierTransform.fourier f) ((Real.sqrt X : Complex) * point k)

theorem dual_summable (f : SchwartzMap Complex Complex) (X : Real) (hX : 0 < X) :
    Summable (fun k : Prod Int Int =>
      (FourierTransform.fourier f) ((Real.sqrt X : Complex) * point k)) := by
  let F : SchwartzMap Complex Complex := FourierTransform.fourier f
  let A := complexMulEquiv (Real.sqrt X : Complex)
    (Complex.ofReal_ne_zero.mpr (ne_of_gt (Real.sqrt_pos.mpr hX)))
  have hs := plane_lattice_summable_norm (affinePullback F A 0)
  apply Summable.of_norm
  simpa only [A, F, affinePullback_apply, complexMulEquiv_apply, add_zero, point] using hs

theorem dual_split (f : SchwartzMap Complex Complex) (X : Real) (hX : 0 < X) :
    (tsum fun k : Prod Int Int =>
      (FourierTransform.fourier f) ((Real.sqrt X : Complex) * point k)) =
      (FourierTransform.fourier f) 0 + fourierTail f X := by
  simpa only [point_zero, mul_zero, fourierTail] using
    (dual_summable f X hX).tsum_eq_add_tsum_ite (0 : Prod Int Int)

theorem idealSum_exact (f : SchwartzMap Complex Complex) (W : Real -> Complex)
    (hW : forall z : Complex, f z = W (Complex.normSq z)) (hzero : W 0 = 0)
    (X : Real) (hX : 0 < X) :
    idealSum W X = ((X : Complex) / 4) * (FourierTransform.fourier f) 0 +
      ((X : Complex) / 4) * fourierTail f X := by
  have hr := radial_sum f W hW hzero X hX
  change (tsum fun z : G => f (Inv.inv (Real.sqrt X : Complex) * embed z)) =
    (4 : Complex) * idealSum W X at hr
  have he : (4 : Complex) * idealSum W X =
      (X : Complex) * ((FourierTransform.fourier f) 0 + fourierTail f X) := by
    rw [<- hr, gaussian_rescaled_poisson f X hX, dual_split f X hX]
  calc
    _ = ((4 : Complex) * idealSum W X) / 4 := by ring
    _ = ((X : Complex) * ((FourierTransform.fourier f) 0 + fourierTail f X)) / 4 :=
      congrArg (fun z : Complex => z / 4) he
    _ = _ := by ring

def maskedTail (H : Ideal G) (f : SchwartzMap Complex Complex) (X : Real) : Complex :=
  (divisors H).sum fun E => (UniqueFactorizationMonoid.moebius E : Complex) *
    (((X / (Ideal.absNorm E : Real) : Real) : Complex) / 4) *
      fourierTail f (X / (Ideal.absNorm E : Real))

theorem masked_exact (H : Ideal G) (hH : Not (H = 0))
    (f : SchwartzMap Complex Complex) (W : Real -> Complex)
    (hW : forall z : Complex, f z = W (Complex.normSq z)) (hzero : W 0 = 0)
    (X : Real) (hX : 0 < X) :
    maskedSum H W X = ((X : Complex) / 4) * (FourierTransform.fourier f) 0 *
      density H + maskedTail H f X := by
  rw [maskedSum_eq H hH W X hX (ideal_summable f W hW X hX)]
  have hm : (divisors H).sum (fun E =>
      (UniqueFactorizationMonoid.moebius E : Complex) *
      (((X / (Ideal.absNorm E : Real) : Real) : Complex) / 4) *
        (FourierTransform.fourier f) 0) =
      ((X : Complex) / 4) * (FourierTransform.fourier f) 0 * density H := by
    unfold density
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro E hE
    simp only [div_eq_mul_inv, Complex.ofReal_mul, Complex.ofReal_inv,
      Complex.ofReal_natCast]
    ring
  calc
    _ = (divisors H).sum (fun E =>
        (UniqueFactorizationMonoid.moebius E : Complex) *
          (((X / (Ideal.absNorm E : Real) : Real) : Complex) / 4) *
            (FourierTransform.fourier f) 0 +
        (UniqueFactorizationMonoid.moebius E : Complex) *
          (((X / (Ideal.absNorm E : Real) : Real) : Complex) / 4) *
            fourierTail f (X / (Ideal.absNorm E : Real))) := by
      apply Finset.sum_congr rfl
      intro E hE
      rw [idealSum_exact f W hW hzero _
        (div_pos hX (GaussianCoprimePoisson.norm_pos E (divisor_ne_zero hH hE)))]
      ring
    _ = _ := by rw [Finset.sum_add_distrib, hm]; rfl

abbrev Pair := Prod NonzeroIdeal NonzeroIdeal

def pairNorm (t : Pair) : Real :=
  (Ideal.absNorm t.1.val : Real) * (Ideal.absNorm t.2.val : Real)

def pairMu (t : Pair) : Complex := mu t.1 * mu t.2

theorem pairNorm_pos (t : Pair) : 0 < pairNorm t :=
  mul_pos (GaussianCoprimePoisson.norm_pos t.1.val t.1.property)
    (GaussianCoprimePoisson.norm_pos t.2.val t.2.property)

def pairMass (S : Finset Pair) : Complex :=
  S.sum fun t => pairMu t / (pairNorm t : Complex)

def pairPacket (S : Finset Pair) (H : Ideal G) (D : Real) (W : Real -> Complex) : Complex :=
  S.sum fun t => pairMu t * maskedSum H W (D / pairNorm t)

def pairTail (S : Finset Pair) (H : Ideal G) (D : Real)
    (f : SchwartzMap Complex Complex) : Complex :=
  S.sum fun t => pairMu t * maskedTail H f (D / pairNorm t)

theorem pairPacket_product (A B : Finset NonzeroIdeal) (H : Ideal G) (D : Real)
    (W : Real -> Complex) :
    pairPacket (SProd.sprod A B) H D W = GaussianPrincipalTypeI.typeI A B H D W := by
  unfold pairPacket GaussianPrincipalTypeI.typeI
  have h := Finset.sum_product A B
    (fun t : Pair => pairMu t * maskedSum H W (D / pairNorm t))
  simpa only [pairMu, pairNorm] using h

theorem packet_exact (S : Finset Pair) (H : Ideal G) (hH : Not (H = 0))
    (D : Real) (hD : 0 < D) (f : SchwartzMap Complex Complex) (W : Real -> Complex)
    (hW : forall z : Complex, f z = W (Complex.normSq z)) (hzero : W 0 = 0) :
    pairPacket S H D W = ((D : Complex) / 4) * (FourierTransform.fourier f) 0 *
      density H * pairMass S + pairTail S H D f := by
  have hm : S.sum (fun t => pairMu t *
      (((D / pairNorm t : Real) : Complex) / 4) *
        (FourierTransform.fourier f) 0 * density H) =
      ((D : Complex) / 4) * (FourierTransform.fourier f) 0 * density H * pairMass S := by
    unfold pairMass
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro t ht
    simp only [div_eq_mul_inv, Complex.ofReal_mul, Complex.ofReal_inv]
    ring
  unfold pairPacket
  calc
    _ = S.sum (fun t => pairMu t *
        (((D / pairNorm t : Real) : Complex) / 4) *
          (FourierTransform.fourier f) 0 * density H +
        pairMu t * maskedTail H f (D / pairNorm t)) := by
      apply Finset.sum_congr rfl
      intro t ht
      rw [masked_exact H hH f W hW hzero _ (div_pos hD (pairNorm_pos t))]
      ring
    _ = _ := by rw [Finset.sum_add_distrib, hm]; rfl

def centeredZeroMode (S : Finset Pair) (A B : Finset NonzeroIdeal)
    (H : Ideal G) (D : Real) (f : SchwartzMap Complex Complex) : Complex :=
  ((D : Complex) / 4) * (FourierTransform.fourier f) 0 * density H *
    (pairMass S - inverseSum A * inverseSum B)

theorem centered_exact (S : Finset Pair) (A B : Finset NonzeroIdeal)
    (H : Ideal G) (hH : Not (H = 0)) (D : Real) (hD : 0 < D)
    (f : SchwartzMap Complex Complex) (W : Real -> Complex)
    (hW : forall z : Complex, f z = W (Complex.normSq z)) (hzero : W 0 = 0) :
    pairPacket S H D W - GaussianPrincipalTypeI.mainTerm A B H D f =
      centeredZeroMode S A B H D f + pairTail S H D f := by
  rw [packet_exact S H hH D hD f W hW hzero,
    GaussianPrincipalTypeI.mainTerm_factored]
  unfold centeredZeroMode
  ring

theorem centered_energy (S : Finset Pair) (A B : Finset NonzeroIdeal)
    (H : Ideal G) (hH : Not (H = 0)) (D : Real) (hD : 0 < D)
    (f : SchwartzMap Complex Complex) (W : Real -> Complex)
    (hW : forall z : Complex, f z = W (Complex.normSq z)) (hzero : W 0 = 0) :
    Complex.normSq (pairPacket S H D W - GaussianPrincipalTypeI.mainTerm A B H D f) =
      Complex.normSq (centeredZeroMode S A B H D f) +
      Complex.normSq (pairTail S H D f) +
      2 * ((centeredZeroMode S A B H D f).re * (pairTail S H D f).re +
        (centeredZeroMode S A B H D f).im * (pairTail S H D f).im) := by
  rw [centered_exact S A B H hH D hD f W hW hzero]
  simp only [Complex.normSq_apply, Complex.add_re, Complex.add_im]
  ring

end PrimeFactorOscillations.GaussianCenteredPoisson

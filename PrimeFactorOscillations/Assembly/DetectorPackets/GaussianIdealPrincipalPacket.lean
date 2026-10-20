/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/

import PrimeFactorOscillations.Assembly.DetectorPackets.GaussianIdealPoisson
import PrimeFactorOscillations.Assembly.DetectorPackets.GaussianPrincipalPacket

/-!
# GaussianIdealPrincipalPacket

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
# Principal Gaussian ideal packet with a finite Mobius mask

Both short inverse factors and the finite divisor mask remain signed.
The main term is the exact finite Euler sum times the Fourier zero mode.
Identification with a specified coprimality mask and its radial pi value
remain separate consumers.
-/


noncomputable section
namespace PrimeFactorOscillations.GaussianIdealPrincipalPacket

open GaussianMobiusDivisors GaussianPoisson GaussianIdealPoisson
open GaussianPrincipalPacket (Triple tripleNorm tripleMu tripleMu_norm_le_one)
open scoped BigOperators

def idealSum (W : Real -> Complex) (X : Real) : Complex :=
  tsum fun I : NonzeroIdeal => W ((Ideal.absNorm I.val : Real) / X)

def packet (S : Finset Triple) (D : Real) (W : Real -> Complex) : Complex :=
  S.sum fun t => tripleMu t * idealSum W (D / tripleNorm t)

def mainTerm (S : Finset Triple) (D : Real) (f : SchwartzMap Complex Complex) : Complex :=
  S.sum fun t => tripleMu t * (((D / tripleNorm t : Real) : Complex) / 4) *
    (FourierTransform.fourier f) 0

theorem mainTerm_factored (S : Finset Triple) (D : Real) (f : SchwartzMap Complex Complex) :
    mainTerm S D f = ((D : Complex) / 4) * (FourierTransform.fourier f) 0 *
      (S.sum fun t => tripleMu t / (tripleNorm t : Complex)) := by
  unfold mainTerm
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro t ht
  rw [Complex.ofReal_div]
  ring

theorem packet_error (S : Finset Triple) (D : Real)
    (f : SchwartzMap Complex Complex) (W : Real -> Complex)
    (hW : forall z : Complex, f z = W (Complex.normSq z)) (hzero : W 0 = 0)
    (hD : 0 < D) (hNorm : forall t, Membership.mem S t -> 0 < tripleNorm t) :
    norm (packet S D W - mainTerm S D f) <= (poissonBound f / 4) * (S.card : Real) := by
  have heq : packet S D W - mainTerm S D f =
      S.sum (fun t => tripleMu t * (idealSum W (D / tripleNorm t) -
        (((D / tripleNorm t : Real) : Complex) / 4) * (FourierTransform.fourier f) 0)) := by
    unfold packet mainTerm
    rw [<- Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro t ht
    ring
  have hp (t : Triple) (ht : Membership.mem S t) :
      norm (tripleMu t * (idealSum W (D / tripleNorm t) -
        (((D / tripleNorm t : Real) : Complex) / 4) * (FourierTransform.fourier f) 0)) <=
        poissonBound f / 4 := by
    have hh := uniform_ideal_error f W hW hzero (D / tripleNorm t) (div_pos hD (hNorm t ht))
    rw [norm_mul]
    exact (mul_le_mul (tripleMu_norm_le_one t) hh (norm_nonneg _) zero_le_one).trans_eq
      (one_mul _)
  rw [heq]
  calc
    _ <= S.sum (fun t => norm (tripleMu t * (idealSum W (D / tripleNorm t) -
        (((D / tripleNorm t : Real) : Complex) / 4) * (FourierTransform.fourier f) 0))) :=
      norm_sum_le _ _
    _ <= S.sum (fun _ => poissonBound f / 4) := Finset.sum_le_sum hp
    _ = _ := by simp [mul_comm]

end PrimeFactorOscillations.GaussianIdealPrincipalPacket

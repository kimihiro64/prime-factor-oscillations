/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/

import Mathlib.Tactic.Ring
import PrimeFactorOscillations.Assembly.DetectorPackets.GaussianPoisson

/-!
# GaussianPrincipalPacket

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
# Independent principal estimate for the Gaussian Mobius packet

The two short Mobius factors and a finite Mobius mask are retained together.
This is the Gaussian-element cofactor kernel. Passage to nonzero ideal
generators, the four units, the odd-prime mask and the radial pi factor must
be verified before identifying it with the normalized ideal Type I packet.
No nonprincipal character estimate or centered Type II bound is asserted.
-/


noncomputable section
namespace PrimeFactorOscillations.GaussianPrincipalPacket

open GaussianMobiusDivisors GaussianPoisson
open scoped BigOperators

abbrev Triple := Prod (Ideal G) (Prod (Ideal G) (Ideal G))

def tripleNorm (t : Triple) : Real :=
  (Ideal.absNorm t.1 : Real) * (Ideal.absNorm t.2.1 : Real) * (Ideal.absNorm t.2.2 : Real)

def tripleMu (t : Triple) : Complex :=
  ((UniqueFactorizationMonoid.moebius t.1 : Int) : Complex) *
  ((UniqueFactorizationMonoid.moebius t.2.1 : Int) : Complex) *
  ((UniqueFactorizationMonoid.moebius t.2.2 : Int) : Complex)

theorem tripleMu_norm_le_one (t : Triple) : norm (tripleMu t) <= 1 := by
  have ha := mobius_norm_le_one t.1
  have hb := mobius_norm_le_one t.2.1
  have hc := mobius_norm_le_one t.2.2
  have hab := mul_le_mul ha hb (norm_nonneg _) zero_le_one
  rw [one_mul] at hab
  have habc := mul_le_mul hab hc (norm_nonneg _) zero_le_one
  simpa only [tripleMu, norm_mul, one_mul] using habc

def latticeSum (f : SchwartzMap Complex Complex) (X : Real) : Complex :=
  tsum fun z : G => f (Inv.inv (Real.sqrt X : Complex) * embed z)

def packet (S : Finset Triple) (D : Real) (f : SchwartzMap Complex Complex) : Complex :=
  S.sum fun t => tripleMu t * latticeSum f (D / tripleNorm t)

def mainTerm (S : Finset Triple) (D : Real) (f : SchwartzMap Complex Complex) : Complex :=
  S.sum fun t => tripleMu t * ((D / tripleNorm t : Real) : Complex) *
    (FourierTransform.fourier f) 0

theorem mainTerm_factored (S : Finset Triple) (D : Real) (f : SchwartzMap Complex Complex) :
    mainTerm S D f = (D : Complex) * (FourierTransform.fourier f) 0 *
      (S.sum fun t => tripleMu t / (tripleNorm t : Complex)) := by
  unfold mainTerm
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro t ht
  rw [Complex.ofReal_div]
  ring

/-- The scale is arbitrary; every cofactor in the finite packet is covered. -/
theorem packet_error (S : Finset Triple) (D : Real) (f : SchwartzMap Complex Complex)
    (hD : 0 < D) (hNorm : forall t, Membership.mem S t -> 0 < tripleNorm t) :
    norm (packet S D f - mainTerm S D f) <= poissonBound f * (S.card : Real) := by
  have hC : 0 <= poissonBound f :=
    (norm_nonneg _).trans (uniform_gaussian_error f 1 zero_lt_one)
  have heq : packet S D f - mainTerm S D f =
      S.sum (fun t => tripleMu t *
        (latticeSum f (D / tripleNorm t) -
          ((D / tripleNorm t : Real) : Complex) * (FourierTransform.fourier f) 0)) := by
    unfold packet mainTerm
    rw [<- Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro t ht
    ring
  have hp (t : Triple) (ht : Membership.mem S t) :
      norm (tripleMu t *
        (latticeSum f (D / tripleNorm t) -
          ((D / tripleNorm t : Real) : Complex) * (FourierTransform.fourier f) 0)) <=
      poissonBound f := by
    have hh := uniform_gaussian_error f (D / tripleNorm t) (div_pos hD (hNorm t ht))
    rw [norm_mul]
    change norm (tripleMu t) *
      norm ((tsum fun z : G => f (Inv.inv (Real.sqrt (D / tripleNorm t) : Complex) * embed z)) -
        ((D / tripleNorm t : Real) : Complex) * (FourierTransform.fourier f) 0) <= poissonBound f
    exact (mul_le_mul (tripleMu_norm_le_one t) hh (norm_nonneg _) zero_le_one).trans_eq
      (one_mul _)
  rw [heq]
  calc
    _ <= S.sum (fun t => norm (tripleMu t *
        (latticeSum f (D / tripleNorm t) -
          ((D / tripleNorm t : Real) : Complex) * (FourierTransform.fourier f) 0))) :=
      norm_sum_le _ _
    _ <= S.sum (fun _ => poissonBound f) := Finset.sum_le_sum hp
    _ = _ := by simp [mul_comm]

end PrimeFactorOscillations.GaussianPrincipalPacket

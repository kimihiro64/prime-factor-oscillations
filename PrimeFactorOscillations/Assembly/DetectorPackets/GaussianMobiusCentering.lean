/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/

import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import PrimeFactorOscillations.Assembly.DetectorPackets.GaussianMobiusConvolution

/-!
# GaussianMobiusCentering

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
# Signal-preserving centering of the actual Gaussian Mobius packet

The centering term is the same in both cutoff pieces. The original packet is
the centered long piece minus the centered short error. This file does not
assume a bound for either piece or any zero-free strip.
-/


noncomputable section
namespace PrimeFactorOscillations.GaussianMobiusCentering
open GaussianMobiusDivisors GaussianMobiusConvolution UniqueFactorizationMonoid

theorem centered_energy_upper (x y main : Complex) :
    Complex.normSq (-x + y) <=
      2 * Complex.normSq (y - main) + 2 * Complex.normSq (x - main) := by
  have he :
      2 * Complex.normSq (y - main) + 2 * Complex.normSq (x - main) -
        Complex.normSq (-x + y) =
          Complex.normSq ((x - main) + (y - main)) := by
    simp only [Complex.normSq_apply, Complex.add_re, Complex.sub_re,
      Complex.neg_re, Complex.add_im, Complex.sub_im, Complex.neg_im]
    ring
  have hn : 0 <= Complex.normSq ((x - main) + (y - main)) := by
    rw [Complex.normSq_apply]
    nlinarith [sq_nonneg (((x - main) + (y - main)).re),
      sq_nonneg (((x - main) + (y - main)).im)]
  linarith

theorem centered_energy_lower (x y main : Complex) :
    Complex.normSq (-x + y) / 2 - Complex.normSq (x - main) <=
      Complex.normSq (y - main) := by
  have h := centered_energy_upper x y main
  linarith

def shortPacket (S : Finset (Ideal G)) (U V : Nat) (K : Ideal G -> Complex) :
    Complex :=
  S.sum (fun I => rectangle I (low U) (low V) * K I)

def longPacket (S : Finset (Ideal G)) (U V : Nat) (K : Ideal G -> Complex) :
    Complex :=
  S.sum (fun I => rectangle I (high U) (high V) * K I)

theorem centered_packet_identity (S : Finset (Ideal G)) (U V : Nat)
    (K : Ideal G -> Complex) (main : Complex)
    (hS : forall I, Membership.mem S I ->
      And (Not (I = 0)) (And (U < Ideal.absNorm I) (V < Ideal.absNorm I))) :
    S.sum (fun I => (moebius I : Complex) * K I) =
      (longPacket S U V K - main) - (shortPacket S U V K - main) := by
  rw [long_packet_split S U V K hS]
  change -(shortPacket S U V K) + longPacket S U V K = _
  ring

theorem centered_moment_upper {R : Type} (rows : Finset R)
    (S : Finset (Ideal G)) (U V : Nat) (K : R -> Ideal G -> Complex)
    (main : R -> Complex) (w : R -> Real)
    (hw : forall r, Membership.mem rows r -> 0 <= w r)
    (hS : forall I, Membership.mem S I ->
      And (Not (I = 0)) (And (U < Ideal.absNorm I) (V < Ideal.absNorm I))) :
    rows.sum (fun r => w r * Complex.normSq
      (S.sum (fun I => (moebius I : Complex) * K r I))) <=
      2 * rows.sum (fun r => w r * Complex.normSq
        (longPacket S U V (K r) - main r)) +
      2 * rows.sum (fun r => w r * Complex.normSq
        (shortPacket S U V (K r) - main r)) := by
  rw [Finset.mul_sum, Finset.mul_sum, <-Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro r hr
  have h := centered_energy_upper
    (shortPacket S U V (K r)) (longPacket S U V (K r)) (main r)
  have hs := long_packet_split S U V (K r) hS
  change S.sum (fun I => (moebius I : Complex) * K r I) =
    -(shortPacket S U V (K r)) + longPacket S U V (K r) at hs
  rw [hs]
  have hm := mul_le_mul_of_nonneg_left h (hw r hr)
  nlinarith only [hm]

theorem centered_moment_lower {R : Type} (rows : Finset R)
    (S : Finset (Ideal G)) (U V : Nat) (K : R -> Ideal G -> Complex)
    (main : R -> Complex) (w : R -> Real)
    (hw : forall r, Membership.mem rows r -> 0 <= w r)
    (hS : forall I, Membership.mem S I ->
      And (Not (I = 0)) (And (U < Ideal.absNorm I) (V < Ideal.absNorm I))) :
    (rows.sum (fun r => w r * Complex.normSq
      (S.sum (fun I => (moebius I : Complex) * K r I)))) / 2 -
      rows.sum (fun r => w r * Complex.normSq
        (shortPacket S U V (K r) - main r)) <=
      rows.sum (fun r => w r * Complex.normSq
        (longPacket S U V (K r) - main r)) := by
  have h := centered_moment_upper rows S U V K main w hw hS
  linarith

end PrimeFactorOscillations.GaussianMobiusCentering

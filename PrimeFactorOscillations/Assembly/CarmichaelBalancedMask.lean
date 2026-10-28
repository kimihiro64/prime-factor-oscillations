/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Assembly.CarmichaelMarkedWindow

/-!
# Balanced local inducing compensation

The auxiliary two-dimensional origin profile has exact Fourier eigenvalue
minus the rational prime. Its signed correction is kept intact. This local
identity supplies neither a prime-weighted inverse-L transfer nor a new
arithmetic exponent.
-/

set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace PrimeFactorOscillations.CarmichaelBalancedMask

def originDelta (p : Nat) [NeZero p] (z : Prod (ZMod p) (ZMod p)) : Complex := by
  classical
  exact if z = Prod.mk 0 0 then 1 else 0

def balancedPair (p : Nat) [NeZero p] (z : Prod (ZMod p) (ZMod p)) : Complex :=
  1 - (p : Complex) * originDelta p z

theorem origin_transform (p : Nat) [NeZero p] [Fact (Nat.Prime p)]
    (psi : AddChar (ZMod p) Complex) (c d : ZMod p) :
    Finset.univ.sum (fun z : Prod (ZMod p) (ZMod p) =>
      originDelta p z * psi (CubicNormFourier.traceForm z.1 z.2 c d)) = 1 := by
  classical
  simp [originDelta, ite_mul, CubicNormFourier.traceForm]

theorem constant_transform (p : Nat) [NeZero p] [Fact (Nat.Prime p)]
    (psi : AddChar (ZMod p) Complex) (hpsi : psi.IsPrimitive) (c d : ZMod p) :
    Finset.univ.sum (fun z : Prod (ZMod p) (ZMod p) =>
      psi (CubicNormFourier.traceForm z.1 z.2 c d)) =
      (p : Complex) ^ 2 * originDelta p (Prod.mk c d) := by
  have h := CarmichaelNormPacket.constant_trace_transform p psi hpsi c d
  have hDelta :
      (if And (c = 0) (d = 0) then (1 : Complex) else 0) =
        originDelta p (Prod.mk c d) := by
    simp only [originDelta, Prod.mk.injEq]
  simpa only [ZMod.card, hDelta] using h

theorem balanced_pair_transform (p : Nat) [NeZero p] [Fact (Nat.Prime p)]
    (psi : AddChar (ZMod p) Complex) (hpsi : psi.IsPrimitive) (c d : ZMod p) :
    Finset.univ.sum (fun z : Prod (ZMod p) (ZMod p) =>
      balancedPair p z * psi (CubicNormFourier.traceForm z.1 z.2 c d)) =
      -(p : Complex) * balancedPair p (Prod.mk c d) := by
  unfold balancedPair
  simp_rw [sub_mul, one_mul, mul_assoc]
  rw [Finset.sum_sub_distrib, <- Finset.mul_sum,
    constant_transform p psi hpsi c d, origin_transform p psi c d]
  ring

end PrimeFactorOscillations.CarmichaelBalancedMask

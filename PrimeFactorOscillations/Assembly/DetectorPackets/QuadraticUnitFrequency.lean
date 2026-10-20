/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/

import PrimeFactorOscillations.Assembly.DetectorPackets.QuadraticPhysicalUnit

/-!
# QuadraticUnitFrequency

Maintained extraction of completed detector/packet proof components.
All original theorem hypotheses and retained proof bodies are preserved.
This module alone asserts no improved zero-free boundary.
-/

set_option autoImplicit false
set_option Elab.async false

/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described by LICENSE.
Authors: Prime Factor Oscillations contributors
-/


noncomputable section
open scoped BigOperators Classical

namespace PrimeFactorOscillations.QuadraticUnitFrequency

open IntegerQuadraticPrefix QuadraticDivisorMean QuadraticPhysicalUnit
open CoprimeSchwartzRemainder

theorem physical_unit_frequency_sum (F : SchwartzMap Real Complex)
    (A : Nat) (eps : Real) (heps : 0 < eps) :
    exists C : Real, 0 < C /\
      forall (M N1 N2 : Nat) (R S T : Finset Nat) (a b : Nat -> Complex),
      (forall r, Membership.mem R r -> Membership.mem (columns M) r) ->
      (forall n, Membership.mem S n -> Membership.mem (columns N1) n) ->
      (forall m, Membership.mem T m -> Membership.mem (columns N2) m) ->
      forall (L : Nat) (e X B U V : Real), 0 < e -> 0 < X ->
        0 < B -> 0 < U -> 0 < V ->
        (forall r, Membership.mem R r -> B <= (r : Real) /\ (r : Real) <= 2 * B) ->
        (forall n, Membership.mem S n -> U <= (n : Real) /\ (n : Real) <= 2 * U) ->
        (forall m, Membership.mem T m -> V <= (m : Real) /\ (m : Real) <= 2 * V) ->
        (Finset.Ioc 0 L).sum (fun ell => physicalUnitMean R S T a b F (ell : Real) e X) <=
          C * (L : Real) * ((max N1 N2 : Nat) : Real) ^ eps *
            Real.sqrt (prefixNorm M N1 * maskedMass 1 S a) *
            Real.sqrt (prefixNorm M N2 * maskedMass 1 T b) := by
  choose C hC hc using physical_unit_divisor_mean F A eps heps
  refine Exists.intro C (And.intro hC ?_)
  intro M N1 N2 R S T a b hR hS hT L e X B U V he hX hB hU hV hRows hNs hMs
  let H : Real := C * ((max N1 N2 : Nat) : Real) ^ eps *
    Real.sqrt (prefixNorm M N1 * maskedMass 1 S a) *
    Real.sqrt (prefixNorm M N2 * maskedMass 1 T b)
  have hrow (ell : Nat) : physicalUnitMean R S T a b F (ell : Real) e X <= H := by
    let q : Real := (ell : Real) * Real.sqrt (e * U * V / (X * B))
    have hq : 0 <= q := by dsimp only [q]; positivity
    have hp : 1 <= (1 + q) ^ A := by
      simpa only [one_pow] using
        nonneg_nat_power_mono 1 (1 + q) (by norm_num) (by linarith) A
    have hquot : C * ((max N1 N2 : Nat) : Real) ^ eps / (1 + q) ^ A <=
        C * ((max N1 N2 : Nat) : Real) ^ eps := by
      calc
        _ <= (C * ((max N1 N2 : Nat) : Real) ^ eps) / 1 :=
          div_le_div_of_nonneg_left (by positivity) (by norm_num) hp
        _ = _ := div_one _
    exact (hc M N1 N2 R S T a b hR hS hT (ell : Real) e X B U V
      (by positivity) he hX hB hU hV hRows hNs hMs).trans
      (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right hquot (Real.sqrt_nonneg _)) (Real.sqrt_nonneg _))
  calc
    _ <= (Finset.Ioc 0 L).sum (fun _ => H) := by
      apply Finset.sum_le_sum
      intro ell hell
      exact hrow ell
    _ = (L : Real) * H := by
      simp only [Finset.sum_const, nsmul_eq_mul, Nat.card_Ioc, Nat.sub_zero]
    _ = _ := by dsimp only [H]; ring

end PrimeFactorOscillations.QuadraticUnitFrequency


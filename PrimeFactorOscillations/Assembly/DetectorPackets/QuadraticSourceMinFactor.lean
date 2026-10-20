/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/

import PrimeFactorOscillations.Assembly.DetectorPackets.QuadraticLowDivisorRange

/-!
# QuadraticSourceMinFactor

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

namespace PrimeFactorOscillations.QuadraticSourceMinFactor

open QuadraticGaussCoefficient IntegerQuadraticPrefix QuadraticLowDivisorRange

theorem min_factor_lower (H N Q P : Real) (hH : 1 <= H)
    (hN : 0 < N) (hQ : 0 < Q) (hP : 0 < P)
    (hRange : P <= 2 * H * N / Q) :
    1 <= (2 * H) * min 1 (N / (Q * P)) := by
  have hMain : (2 * H * N / Q) * Q = 2 * H * N := by field_simp
  have hQP : Q * P <= 2 * H * N := by
    have h := mul_le_mul_of_nonneg_right hRange hQ.le
    rw [hMain] at h
    simpa only [mul_comm] using h
  by_cases hr : 1 <= N / (Q * P)
  . rw [min_eq_left hr]
    nlinarith
  . rw [min_eq_right (le_of_not_ge hr)]
    have hDivide : (N / (Q * P)) * (Q * P) = N := by field_simp
    apply le_of_mul_le_mul_right _ (mul_pos hQ hP)
    nlinarith [hDivide]

theorem envelope_nonneg (C eps : Real) (M N1 N2 L1 L2 : Nat) (U : Real)
    (S T : Finset Nat) (a b : Nat -> Complex) (hC : 0 <= C) (hU : 0 < U) :
    0 <= envelope C eps M N1 N2 L1 L2 U S T a b := by
  unfold envelope
  positivity

theorem low_inverse_source_minimum (eps : Real) (heps : 0 < eps) :
    exists C : Real, 0 < C /\
      forall (Z M N1 N2 : Nat) (k1 k2 : Int) (R S T : Finset Nat)
        (a b : Nat -> Complex), 0 < Z -> 0 < N1 -> 0 < N2 ->
      (forall r, Membership.mem R r -> Membership.mem (columns M) r) ->
      (forall n, Membership.mem S n -> Membership.mem (columns N1) n) ->
      (forall m, Membership.mem T m -> Membership.mem (columns N2) m) ->
      exists L1 L2 : Nat, 0 < L1 /\ 0 < L2 /\ L1 * L2 <= 2 * Z /\
      forall (U H N Q : Real), 0 < U -> 1 <= H -> 0 < N -> 0 < Q ->
      (Z : Real) <= H * N / Q ->
      (forall n, Membership.mem S n -> U <= (n : Real)) ->
      (forall m, Membership.mem T m -> U <= (m : Real)) ->
      lowDivisorMean Z R S T (inverseCoefficient a k1) (inverseCoefficient b k2) <=
        ((Z.log2 + 2 : Nat) : Real) *
          ((2 * H) * min 1 (N / (Q * ((L1 : Real) * (L2 : Real))))) *
          envelope C eps M N1 N2 L1 L2 U S T a b := by
  choose C hC hc using low_inverse_divisor_mean eps heps
  refine Exists.intro C (And.intro hC ?_)
  intro Z M N1 N2 k1 k2 R S T a b hZ hN1 hN2 hR hS hT
  choose L1 L2 hL using hc Z M N1 N2 k1 k2 R S T a b hZ hN1 hN2 hR hS hT
  refine Exists.intro L1 (Exists.intro L2
    (And.intro hL.1 (And.intro hL.2.1 (And.intro hL.2.2.1 ?_))))
  intro U H N Q hU hH hN hQ hZrange hSU hTU
  have hp : 0 < (L1 : Real) * (L2 : Real) := by
    exact_mod_cast Nat.mul_pos hL.1 hL.2.1
  have hPair : (L1 : Real) * (L2 : Real) <= 2 * (Z : Real) := by
    exact_mod_cast hL.2.2.1
  have hRange : (L1 : Real) * (L2 : Real) <= 2 * H * N / Q := by
    calc
      _ <= 2 * (Z : Real) := hPair
      _ <= 2 * (H * N / Q) := mul_le_mul_of_nonneg_left hZrange (by norm_num)
      _ = _ := by ring
  have hMin := min_factor_lower H N Q ((L1 : Real) * (L2 : Real))
    hH hN hQ hp hRange
  have hEnv := envelope_nonneg C eps M N1 N2 L1 L2 U S T a b hC.le hU
  have hStep := mul_le_mul_of_nonneg_right hMin hEnv
  simp only [one_mul] at hStep
  calc
    _ <= ((Z.log2 + 2 : Nat) : Real) * envelope C eps M N1 N2 L1 L2 U S T a b :=
      hL.2.2.2 U hU hSU hTU
    _ <= ((Z.log2 + 2 : Nat) : Real) *
        (((2 * H) * min 1 (N / (Q * ((L1 : Real) * (L2 : Real))))) *
          envelope C eps M N1 N2 L1 L2 U S T a b) :=
      mul_le_mul_of_nonneg_left hStep (Nat.cast_nonneg _)
    _ = _ := by ring

end PrimeFactorOscillations.QuadraticSourceMinFactor


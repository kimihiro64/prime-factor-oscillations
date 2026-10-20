/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/

import PrimeFactorOscillations.Assembly.DetectorPackets.GaussianMellinWavelet
import PrimeFactorOscillations.Proof.DetectorPackets.UniformCarrierPairedProbe

/-!
# GaussianWaveletCarrier

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
# Actual probability pairs tested against the three-scale window

The data retain both coefficient observations and the same inverse/plain
character parameters. The constant is the original carrier constant, with
no extra dependence on conductor, height, or the window sampling maps.
This transfers error only: the signed arithmetic covariance is retained.
-/


noncomputable section
namespace PrimeFactorOscillations.GaussianMellinWavelet.Carrier

open UniformCarrier.PairedProbe UniformCarrier.PairedProbe.DirichletPair

private theorem weighted_error (a b z : Complex) (delta : Real)
    (hdelta : 0 <= delta) (hab : norm (a - b) <= delta) (hz : norm z <= 1) :
    norm (a * z - b * z) <= delta := by
  rw [<- sub_mul, norm_mul]
  exact (mul_le_mul hab hz (norm_nonneg _) hdelta).trans_eq (mul_one _)

theorem paired_error {n0 d q r k : Nat} {C : Real}
    (xi : DirichletCharacter Complex q) (chi : DirichletCharacter Complex r)
    (eta : DirichletCharacter Complex k) (data : Data n0 d C xi chi eta)
    (hC : 0 <= C) (hd : 2 <= d)
    (N : Nat) (hN : 1 <= N) (S : Finset Nat) (hcard : S.card <= N)
    (hrange : forall n : Nat, Membership.mem S n -> N <= n)
    (WI WP : Real -> Complex)
    (hWI : forall x : Real, norm (WI x) <= 1)
    (hWP : forall x : Real, norm (WP x) <= 1)
    (xI xP : Nat -> Real) :
    norm (value S N
        (fun n => data.inverseData n * window WI (xI n))
        (fun n => data.plainData n * window WP (xP n)) -
      value S N
        (fun n => inverseCoefficient xi n * window WI (xI n))
        (fun n => plainCoefficient chi eta n * window WP (xP n))) <=
      (2 * C + C ^ 2) / (N : Real) ^ (d - 2) := by
  apply power_pair_error d N hd hN S hcard hrange
    (fun n => data.inverseData n * window WI (xI n))
    (fun n => data.plainData n * window WP (xP n))
    (fun n => inverseCoefficient xi n * window WI (xI n))
    (fun n => plainCoefficient chi eta n * window WP (xP n)) C hC
  . intro n hn
    rw [norm_mul]
    exact (mul_le_mul (inverse_norm_le_one xi n) (window_bound WI 1 hWI (xI n))
      (norm_nonneg _) zero_le_one).trans_eq (one_mul _)
  . intro n hn
    rw [norm_mul]
    exact (mul_le_mul (plain_norm_le_one chi eta n) (window_bound WP 1 hWP (xP n))
      (norm_nonneg _) zero_le_one).trans_eq (one_mul _)
  . intro n hn
    have hn1 : 1 <= n := hN.trans (hrange n hn)
    exact weighted_error _ _ _ _ (div_nonneg hC (pow_nonneg (Nat.cast_nonneg n) _))
      (data.inverse_error n (by omega)) (window_bound WI 1 hWI (xI n))
  . intro n hn
    have hn1 : 1 <= n := hN.trans (hrange n hn)
    exact weighted_error _ _ _ _ (div_nonneg hC (pow_nonneg (Nat.cast_nonneg n) _))
      (data.plain_error n (by omega)) (window_bound WP 1 hWP (xP n))

end PrimeFactorOscillations.GaussianMellinWavelet.Carrier


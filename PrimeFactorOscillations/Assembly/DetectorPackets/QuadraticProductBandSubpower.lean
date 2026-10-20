/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/

import PrimeFactorOscillations.Assembly.DetectorPackets.QuadraticProductBandEstimate

/-!
# QuadraticProductBandSubpower

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

namespace PrimeFactorOscillations.QuadraticProductBandSubpower

open QuadraticCarrierPacket QuadraticCoprimeMean IntegerQuadraticPrefix
open QuadraticDivisorMean QuadraticDivisorBand QuadraticProductDivisor
open QuadraticProductBand QuadraticDyadicBand QuadraticProductBandEstimate

theorem indexBound_subpower (eps : Real) (heps : 0 < eps) :
    exists A : Real, 0 < A /\
      forall D : Nat, 0 < D ->
      (indexBound D : Real) ^ 2 <= A * (D : Real) ^ eps := by
  choose C hC hc using divisor_card_subpower (eps / 2) (by linarith)
  refine Exists.intro (C ^ 2 * (4 : Real) ^ eps) (And.intro (by positivity) ?_)
  intro D hD
  let k := indexBound D
  let u := 2 ^ k
  have hu : 0 < u := by dsimp only [u]; positivity
  have huR : 0 < (u : Real) := by exact_mod_cast hu
  have hupper : u <= 4 * D := by
    calc
      _ = 2 * 2 ^ (2 * D).log2 := by dsimp only [u, k, indexBound]; rw [pow_succ]; ring
      _ <= 2 * (2 * D) := Nat.mul_le_mul_left 2
        (Nat.log2_self_le (by omega : Not (2 * D = 0)))
      _ = _ := by ring
  have hcard : u.divisors.card = k + 1 := by
    dsimp only [u]
    rw [Nat.divisors_prime_pow Nat.prime_two, Finset.card_map, Finset.card_range]
  have hkcard : (k : Real) <= (u.divisors.card : Real) := by
    rw [hcard]
    exact_mod_cast Nat.le_succ k
  have hk : (k : Real) <= C * (u : Real) ^ (eps / 2) := hkcard.trans (hc u hu)
  have hpow : ((u : Real) ^ (eps / 2)) ^ 2 = (u : Real) ^ eps := by
    rw [sq, <- Real.rpow_add huR]
    congr 1
    ring
  have hu4 : (u : Real) <= 4 * (D : Real) := by exact_mod_cast hupper
  calc
    _ <= (C * (u : Real) ^ (eps / 2)) ^ 2 := by
      simpa only [sq] using
        mul_self_le_mul_self (show (0 : Real) <= (k : Real) by positivity) hk
    _ = C ^ 2 * (u : Real) ^ eps := by rw [mul_pow, hpow]
    _ <= C ^ 2 * (4 * (D : Real)) ^ eps :=
      mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow (Nat.cast_nonneg u) hu4 heps.le) (sq_nonneg C)
    _ = _ := by rw [Real.mul_rpow (by norm_num : (0 : Real) <= 4) (Nat.cast_nonneg D)]; ring

theorem uniform_product_divisor_mean (eps : Real) (heps : 0 < eps) :
    exists C : Real, 0 < C /\
      forall (D M N1 N2 : Nat) (R S T : Finset Nat) (a b : Nat -> Complex),
      0 < D -> 0 < N1 -> 0 < N2 ->
      (forall r, Membership.mem R r -> Membership.mem (columns M) r) ->
      (forall n, Membership.mem S n -> Membership.mem (columns N1) n) ->
      (forall m, Membership.mem T m -> Membership.mem (columns N2) m) ->
      exists L1 L2 : Nat,
        0 < L1 /\ 0 < L2 /\ D < 4 * (L1 * L2) /\ L1 * L2 <= 2 * D /\
        productBandMean D R S T a b <=
          C * ((D * max N1 N2 : Nat) : Real) ^ eps *
            Real.sqrt ((L1 : Real) * (L2 : Real)) *
            Real.sqrt (prefixNorm M (N1 / L1) * maskedMass 1 S a) *
            Real.sqrt (prefixNorm M (N2 / L2) * maskedMass 1 T b) := by
  choose C hC hc using product_divisor_band_estimate eps heps
  choose A hA ha using indexBound_subpower eps heps
  refine Exists.intro (C * A) (And.intro (mul_pos hC hA) ?_)
  intro D M N1 N2 R S T a b hD hN1 hN2 hR hS hT
  choose L1 L2 h1 h2 hlo hhi hb using
    hc D M N1 N2 R S T a b hD hN1 hN2 hR hS hT
  refine Exists.intro L1 (Exists.intro L2
    (And.intro h1 (And.intro h2 (And.intro hlo (And.intro hhi ?_)))))
  let J := max N1 N2
  let Q := Real.sqrt ((L1 : Real) * (L2 : Real)) *
    Real.sqrt (prefixNorm M (N1 / L1) * maskedMass 1 S a) *
    Real.sqrt (prefixNorm M (N2 / L2) * maskedMass 1 T b)
  have hQ : 0 <= Q := by dsimp only [Q]; positivity
  have hscale : 0 <= C * (J : Real) ^ eps := by positivity
  calc
    _ <= C * (J : Real) ^ eps * (indexBound D : Real) ^ 2 * Q := by
      calc
        _ <= _ := hb
        _ = _ := by dsimp only [Q, J]; ring
    _ <= C * (J : Real) ^ eps * (A * (D : Real) ^ eps) * Q :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (ha D hD) hscale) hQ
    _ = (C * A) * ((D * J : Nat) : Real) ^ eps * Q := by
      rw [Nat.cast_mul, Real.mul_rpow (Nat.cast_nonneg D) (Nat.cast_nonneg J)]
      ring
    _ = _ := by dsimp only [Q, J]; ring

theorem productBandMean_zero_large (D N1 N2 : Nat)
    (R S T : Finset Nat) (a b : Nat -> Complex)
    (hD : N1 * N2 <= D)
    (hS : forall n, Membership.mem S n -> Membership.mem (columns N1) n)
    (hT : forall m, Membership.mem T m -> Membership.mem (columns N2) m) :
    productBandMean D R S T a b = 0 := by
  unfold productBandMean
  apply Finset.sum_eq_zero
  intro d hd
  apply Finset.sum_eq_zero
  intro r hr
  apply norm_eq_zero.mpr
  unfold divisorRow
  apply Finset.sum_eq_zero
  intro n hn
  apply Finset.sum_eq_zero
  intro m hm
  apply if_neg
  intro hc
  have hnb := columns_bounds N1 n (hS n hn)
  have hmb := columns_bounds N2 m (hT m hm)
  have hle : d <= D := (Nat.le_of_dvd (Nat.mul_pos hnb.1 hmb.1) hc.2).trans
    ((Nat.mul_le_mul hnb.2 hmb.2).trans hD)
  exact (Nat.not_lt.mpr hle) (Finset.mem_Ioc.mp hd).1

theorem source_product_divisor_mean (eps : Real) (heps : 0 < eps) :
    exists C : Real, 0 < C /\
      forall (D M N1 N2 : Nat) (R S T : Finset Nat) (a b : Nat -> Complex),
      0 < D -> 0 < N1 -> 0 < N2 ->
      (forall r, Membership.mem R r -> Membership.mem (columns M) r) ->
      (forall n, Membership.mem S n -> Membership.mem (columns N1) n) ->
      (forall m, Membership.mem T m -> Membership.mem (columns N2) m) ->
      exists L1 L2 : Nat,
        0 < L1 /\ 0 < L2 /\ D < 4 * (L1 * L2) /\ L1 * L2 <= 2 * D /\
        productBandMean D R S T a b <=
          C * ((max N1 N2 : Nat) : Real) ^ eps *
            Real.sqrt ((L1 : Real) * (L2 : Real)) *
            Real.sqrt (prefixNorm M (N1 / L1) * maskedMass 1 S a) *
            Real.sqrt (prefixNorm M (N2 / L2) * maskedMass 1 T b) := by
  choose C hC hc using uniform_product_divisor_mean (eps / 3) (by linarith)
  refine Exists.intro C (And.intro hC ?_)
  intro D M N1 N2 R S T a b hD hN1 hN2 hR hS hT
  by_cases hlarge : N1 * N2 <= D
  . refine Exists.intro D (Exists.intro 1
      (And.intro hD (And.intro (by decide) (And.intro ?_ (And.intro ?_ ?_)))))
    . simp only [mul_one]
      omega
    . simp only [mul_one]
      omega
    . rw [productBandMean_zero_large D N1 N2 R S T a b hlarge hS hT]
      positivity
  . choose L1 L2 h1 h2 hlo hhi hb using
      hc D M N1 N2 R S T a b hD hN1 hN2 hR hS hT
    refine Exists.intro L1 (Exists.intro L2
      (And.intro h1 (And.intro h2 (And.intro hlo (And.intro hhi ?_)))))
    let J := max N1 N2
    have hDJ : D <= J ^ 2 := by
      calc
        _ <= N1 * N2 := (Nat.lt_of_not_ge hlarge).le
        _ <= J * J := Nat.mul_le_mul (le_max_left _ _) (le_max_right _ _)
        _ = _ := by ring
    have hbaseN : D * J <= J ^ 3 := by
      calc
        _ <= J ^ 2 * J := Nat.mul_le_mul_right J hDJ
        _ = _ := by ring
    have hbase : ((D * J : Nat) : Real) <= (J : Real) ^ 3 := by exact_mod_cast hbaseN
    have hp : ((D * J : Nat) : Real) ^ (eps / 3) <= (J : Real) ^ eps := by
      calc
        _ <= ((J : Real) ^ 3) ^ (eps / 3) :=
          Real.rpow_le_rpow (Nat.cast_nonneg _) hbase (by linarith)
        _ = _ := by
          rw [<- Real.rpow_natCast_mul (Nat.cast_nonneg J) 3 (eps / 3)]
          congr 1
          norm_num
          ring
    let Q := Real.sqrt ((L1 : Real) * (L2 : Real)) *
      Real.sqrt (prefixNorm M (N1 / L1) * maskedMass 1 S a) *
      Real.sqrt (prefixNorm M (N2 / L2) * maskedMass 1 T b)
    have hQ : 0 <= Q := by dsimp only [Q]; positivity
    calc
      _ <= C * ((D * J : Nat) : Real) ^ (eps / 3) * Q := by
        calc
          _ <= _ := hb
          _ = _ := by dsimp only [Q, J]; ring
      _ <= C * (J : Real) ^ eps * Q :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hp hC.le) hQ
      _ = _ := by dsimp only [Q, J]; ring

theorem divisorRow_one (S T : Finset Nat) (a b : Nat -> Complex) (r : Nat) :
    divisorRow 1 S T a b r =
      coprimeForm S T (fun n => a n * kernel r n) (fun m => b m * kernel r m) := by
  unfold divisorRow coprimeForm
  apply Finset.sum_congr rfl
  intro n hn
  apply Finset.sum_congr rfl
  intro m hm
  by_cases hc : Nat.Coprime n m
  . rw [if_pos (And.intro hc (Nat.one_dvd _)), if_pos hc]
  . rw [if_neg (fun h => hc h.1), if_neg hc]

theorem unit_divisor_mean (eps : Real) (heps : 0 < eps) :
    exists C : Real, 0 < C /\
      forall (M N1 N2 : Nat) (R S T : Finset Nat) (a b : Nat -> Complex),
      (forall r, Membership.mem R r -> Membership.mem (columns M) r) ->
      (forall n, Membership.mem S n -> Membership.mem (columns N1) n) ->
      (forall m, Membership.mem T m -> Membership.mem (columns N2) m) ->
      R.sum (fun r => norm (divisorRow 1 S T a b r)) <=
        C * ((max N1 N2 : Nat) : Real) ^ eps *
          Real.sqrt (prefixNorm M N1 * maskedMass 1 S a) *
          Real.sqrt (prefixNorm M N2 * maskedMass 1 T b) := by
  choose C hC hc using coprime_mean_subpower eps heps
  refine Exists.intro C (And.intro hC ?_)
  intro M N1 N2 R S T a b hR hS hT
  simpa only [divisorRow_one, Nat.one_dvd, ite_true, Nat.div_one] using
    hc M N1 N2 1 1 (by decide) (by decide) R S T a b hR hS hT

end PrimeFactorOscillations.QuadraticProductBandSubpower

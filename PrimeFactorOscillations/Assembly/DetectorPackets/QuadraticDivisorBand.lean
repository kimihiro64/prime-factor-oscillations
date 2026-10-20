/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/

import PrimeFactorOscillations.Assembly.DetectorPackets.QuadraticDivisorMean

/-!
# QuadraticDivisorBand

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

namespace PrimeFactorOscillations.QuadraticDivisorBand

open QuadraticCarrierPacket QuadraticCoprimeMean IntegerQuadraticPrefix
open QuadraticDivisorMean

theorem masked_mass_sum (eps : Real) (heps : 0 < eps) :
    exists C : Real, 0 < C /\
      forall (E S : Finset Nat) (J : Nat) (a : Nat -> Complex),
      (forall n, Membership.mem S n -> 0 < n /\ n <= J) ->
      E.sum (fun e => maskedMass e S a) <=
        C * (J : Real) ^ eps * maskedMass 1 S a := by
  choose C hC hc using divisor_card_subpower eps heps
  refine Exists.intro C (And.intro hC ?_)
  intro E S J a hS
  unfold maskedMass
  rw [Finset.sum_comm]
  simp only [Nat.one_dvd, ite_true]
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro n hn
  have hn0 := (hS n hn).1
  have hf : (E.filter (fun e => Dvd.dvd e n)).card <= n.divisors.card := by
    apply Finset.card_le_card
    intro e he
    exact Nat.mem_divisors.mpr (And.intro (Finset.mem_filter.mp he).2 (Nat.ne_of_gt hn0))
  have hnr : (n : Real) <= (J : Real) := Nat.cast_le.mpr (hS n hn).2
  have hcount : ((E.filter (fun e => Dvd.dvd e n)).card : Real) <=
      C * (J : Real) ^ eps := by
    calc
      _ <= (n.divisors.card : Real) := Nat.cast_le.mpr hf
      _ <= C * (n : Real) ^ eps := hc n hn0
      _ <= _ := mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow (Nat.cast_nonneg n) hnr heps.le) hC.le
  calc
    _ = (E.filter (fun e => Dvd.dvd e n)).sum (fun _ => norm (a n) ^ 2) := by
      rw [Finset.sum_filter]
    _ = ((E.filter (fun e => Dvd.dvd e n)).card : Real) * norm (a n) ^ 2 := by
      simp only [Finset.sum_const, nsmul_eq_mul]
    _ <= _ := mul_le_mul_of_nonneg_right hcount (sq_nonneg _)

theorem sqrt_mask_sum (E S : Finset Nat) (a : Nat -> Complex) :
    E.sum (fun e => Real.sqrt (maskedMass e S a)) <=
      Real.sqrt (E.card : Real) * Real.sqrt (E.sum (fun e => maskedMass e S a)) := by
  have h := Real.sum_mul_le_sqrt_mul_sqrt E (fun _ => (1 : Real))
    (fun e => Real.sqrt (maskedMass e S a))
  have hs (e : Nat) : (Real.sqrt (maskedMass e S a)) ^ 2 = maskedMass e S a :=
    Real.sq_sqrt (maskedMass_nonneg e S a)
  simpa only [one_mul, one_pow, Finset.sum_const, nsmul_eq_mul, mul_one, hs] using h

theorem weighted_sqrt_mask_sum (E S : Finset Nat) (a : Nat -> Complex)
    (B scale : Real) (hB : 0 <= B) (hscale : 0 <= scale)
    (hmass : E.sum (fun e => maskedMass e S a) <= scale * maskedMass 1 S a) :
    E.sum (fun e => Real.sqrt (B * maskedMass e S a)) <=
      Real.sqrt (E.card : Real) * Real.sqrt scale *
        Real.sqrt (B * maskedMass 1 S a) := by
  calc
    _ = Real.sqrt B * E.sum (fun e => Real.sqrt (maskedMass e S a)) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro e he
      exact Real.sqrt_mul hB _
    _ <= Real.sqrt B *
        (Real.sqrt (E.card : Real) * Real.sqrt (E.sum (fun e => maskedMass e S a))) :=
      mul_le_mul_of_nonneg_left (sqrt_mask_sum E S a) (Real.sqrt_nonneg _)
    _ <= Real.sqrt B *
        (Real.sqrt (E.card : Real) * Real.sqrt (scale * maskedMass 1 S a)) :=
      mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hmass) (Real.sqrt_nonneg _))
        (Real.sqrt_nonneg _)
    _ = _ := by
      rw [Real.sqrt_mul hscale, Real.sqrt_mul hB]
      ring

def maskedRowMean (R S T : Finset Nat) (a b : Nat -> Complex) (e1 e2 : Nat) : Real :=
  R.sum (fun r => norm (coprimeForm S T
    (fun n => (if Dvd.dvd e1 n then a n else 0) * kernel r n)
    (fun m => (if Dvd.dvd e2 m then b m else 0) * kernel r m)))

theorem divisor_band_mean (eps : Real) (heps : 0 < eps) :
    exists C : Real, 0 < C /\
      forall (M N1 N2 L1 L2 : Nat) (R S T E1 E2 : Finset Nat)
        (a b : Nat -> Complex),
      0 < N1 -> 0 < N2 -> 0 < L1 -> 0 < L2 ->
      (forall e, Membership.mem E1 e -> L1 <= e) ->
      (forall e, Membership.mem E2 e -> L2 <= e) ->
      (forall r, Membership.mem R r -> Membership.mem (columns M) r) ->
      (forall n, Membership.mem S n -> Membership.mem (columns N1) n) ->
      (forall m, Membership.mem T m -> Membership.mem (columns N2) m) ->
      E1.sum (fun e1 => E2.sum (fun e2 => maskedRowMean R S T a b e1 e2)) <=
        C * ((max N1 N2 : Nat) : Real) ^ eps *
          Real.sqrt ((E1.card : Real) * (E2.card : Real)) *
          Real.sqrt (prefixNorm M (N1 / L1) * maskedMass 1 S a) *
          Real.sqrt (prefixNorm M (N2 / L2) * maskedMass 1 T b) := by
  choose C1 hC1 hc using coprime_mean_subpower (eps / 2) (by linarith)
  choose C2 hC2 ha using masked_mass_sum (eps / 2) (by linarith)
  refine Exists.intro (C1 * C2) (And.intro (mul_pos hC1 hC2) ?_)
  intro M N1 N2 L1 L2 R S T E1 E2 a b hN1 hN2 hL1 hL2 hE1 hE2 hR hS hT
  let J := max N1 N2
  let P := C1 * (J : Real) ^ (eps / 2)
  let A := C2 * (J : Real) ^ (eps / 2)
  let B1 := prefixNorm M (N1 / L1)
  let B2 := prefixNorm M (N2 / L2)
  let f1 := fun e => Real.sqrt (B1 * maskedMass e S a)
  let f2 := fun e => Real.sqrt (B2 * maskedMass e T b)
  have hP : 0 <= P := by dsimp only [P]; positivity
  have hA : 0 <= A := by dsimp only [A]; positivity
  have hB1 : 0 <= B1 := by unfold B1 prefixNorm; exact sq_nonneg _
  have hB2 : 0 <= B2 := by unfold B2 prefixNorm; exact sq_nonneg _
  have hsJ : forall n, Membership.mem S n -> 0 < n /\ n <= J := by
    intro n hn
    have h := columns_bounds N1 n (hS n hn)
    exact And.intro h.1 (h.2.trans (le_max_left _ _))
  have htJ : forall n, Membership.mem T n -> 0 < n /\ n <= J := by
    intro n hn
    have h := columns_bounds N2 n (hT n hn)
    exact And.intro h.1 (h.2.trans (le_max_right _ _))
  have hsum1 := weighted_sqrt_mask_sum E1 S a B1 A hB1 hA (ha E1 S J a hsJ)
  have hsum2 := weighted_sqrt_mask_sum E2 T b B2 A hB2 hA (ha E2 T J b htJ)
  have hpoint (e1 : Nat) (he1 : Membership.mem E1 e1)
      (e2 : Nat) (he2 : Membership.mem E2 e2) :
      maskedRowMean R S T a b e1 e2 <= P * f1 e1 * f2 e2 := by
    have h1 : prefixNorm M (N1 / e1) <= B1 :=
      prefixNorm_monotone le_rfl (Nat.div_le_div_left (hE1 e1 he1) hL1)
    have h2 : prefixNorm M (N2 / e2) <= B2 :=
      prefixNorm_monotone le_rfl (Nat.div_le_div_left (hE2 e2 he2) hL2)
    have hr1 := Real.sqrt_le_sqrt
      (mul_le_mul_of_nonneg_right h1 (maskedMass_nonneg e1 S a))
    have hr2 := Real.sqrt_le_sqrt
      (mul_le_mul_of_nonneg_right h2 (maskedMass_nonneg e2 T b))
    calc
      _ <= P * Real.sqrt (prefixNorm M (N1 / e1) * maskedMass e1 S a) *
          Real.sqrt (prefixNorm M (N2 / e2) * maskedMass e2 T b) :=
        hc M N1 N2 e1 e2 (hL1.trans_le (hE1 e1 he1)) (hL2.trans_le (hE2 e2 he2))
          R S T a b hR hS hT
      _ <= _ := mul_le_mul (mul_le_mul_of_nonneg_left hr1 hP) hr2
        (Real.sqrt_nonneg _) (mul_nonneg hP (Real.sqrt_nonneg _))
  have hsum : E1.sum (fun e1 => E2.sum (fun e2 => maskedRowMean R S T a b e1 e2)) <=
      P * E1.sum f1 * E2.sum f2 := by
    calc
      _ <= E1.sum (fun e1 => E2.sum (fun e2 => P * f1 e1 * f2 e2)) := by
        apply Finset.sum_le_sum
        intro e1 he1
        apply Finset.sum_le_sum
        intro e2 he2
        exact hpoint e1 he1 e2 he2
      _ = _ := by
        simp only [Finset.mul_sum, Finset.sum_mul]
        rw [Finset.sum_comm (s := E1) (t := E2)]
  have hJ : 0 < (J : Real) := by
    exact_mod_cast (hN1.trans_le (le_max_left N1 N2))
  have hpow : (J : Real) ^ (eps / 2) * (J : Real) ^ (eps / 2) =
      (J : Real) ^ eps := by
    rw [<- Real.rpow_add hJ]
    congr 1
    ring
  calc
    _ <= P * E1.sum f1 * E2.sum f2 := hsum
    _ <= P * (Real.sqrt (E1.card : Real) * Real.sqrt A *
          Real.sqrt (B1 * maskedMass 1 S a)) *
        (Real.sqrt (E2.card : Real) * Real.sqrt A *
          Real.sqrt (B2 * maskedMass 1 T b)) := by
      exact mul_le_mul (mul_le_mul_of_nonneg_left hsum1 hP) hsum2
        (Finset.sum_nonneg (fun _ _ => Real.sqrt_nonneg _))
        (mul_nonneg hP (mul_nonneg
          (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)) (Real.sqrt_nonneg _)))
    _ = P * (Real.sqrt A * Real.sqrt A) *
        (Real.sqrt (E1.card : Real) * Real.sqrt (E2.card : Real)) *
          Real.sqrt (B1 * maskedMass 1 S a) *
            Real.sqrt (B2 * maskedMass 1 T b) := by ring
    _ = P * A * Real.sqrt ((E1.card : Real) * (E2.card : Real)) *
          Real.sqrt (B1 * maskedMass 1 S a) *
            Real.sqrt (B2 * maskedMass 1 T b) := by
      rw [Real.mul_self_sqrt hA, Real.sqrt_mul (Nat.cast_nonneg E1.card)]
    _ = _ := by
      dsimp only [P, A, B1, B2]
      calc
        _ = (C1 * C2) * ((J : Real) ^ (eps / 2) * (J : Real) ^ (eps / 2)) *
            Real.sqrt ((E1.card : Real) * (E2.card : Real)) *
              Real.sqrt (prefixNorm M (N1 / L1) * maskedMass 1 S a) *
                Real.sqrt (prefixNorm M (N2 / L2) * maskedMass 1 T b) := by ring
        _ = _ := by rw [hpow]

end PrimeFactorOscillations.QuadraticDivisorBand

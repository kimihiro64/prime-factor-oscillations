/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/

import PrimeFactorOscillations.Proof.DetectorPackets.UniformCarrierPairedProbe

/-!
# CarrierAmplifiedMoment

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
# Carrier error in an amplified joint moment

The row and column sets are finite. The amplifier is retained as one
factor, including its phases. These estimates transfer an independently
proved moment bound; they do not supply that arithmetic bound.
-/


noncomputable section
namespace PrimeFactorOscillations.UniformCarrier.AmplifiedMoment

def column {I J : Type} (S : Finset I) (a : I -> Complex)
    (K : J -> I -> Complex) (r : J) : Complex :=
  S.sum (fun n => a n * K r n)

def energy {I J : Type} (T : Finset J) (S : Finset I)
    (a : I -> Complex) (K : J -> I -> Complex) (P : J -> Complex) : Real :=
  T.sum (fun r => norm (column S a K r * P r) ^ 2)

theorem column_error {I J : Type} (S : Finset I) (a f : I -> Complex)
    (K : J -> I -> Complex) (r : J) (eps : Real)
    (heps : 0 <= eps)
    (herr : forall n, Membership.mem S n -> norm (f n - a n) <= eps)
    (hK : forall n, Membership.mem S n -> norm (K r n) <= 1) :
    norm (column S f K r - column S a K r) <= (S.card : Real) * eps := by
  calc
    norm (column S f K r - column S a K r) =
        norm (S.sum (fun n => (f n - a n) * K r n)) := by
      unfold column
      rw [<- Finset.sum_sub_distrib]
      congr 1
      apply Finset.sum_congr rfl
      intro n hn
      ring
    _ <= S.sum (fun n => norm ((f n - a n) * K r n)) := norm_sum_le _ _
    _ <= S.sum (fun _ => eps) := by
      apply Finset.sum_le_sum
      intro n hn
      rw [norm_mul]
      calc
        norm (f n - a n) * norm (K r n) <= eps * 1 :=
          mul_le_mul (herr n hn) (hK n hn) (norm_nonneg _) heps
        _ = eps := mul_one _
    _ = (S.card : Real) * eps := by simp

theorem energy_transfer {I J : Type} (T : Finset J) (S : Finset I)
    (a f : I -> Complex) (K : J -> I -> Complex) (P : J -> Complex)
    (eps B : Real) (heps : 0 <= eps) (hB : 0 <= B)
    (herr : forall n, Membership.mem S n -> norm (f n - a n) <= eps)
    (hK : forall r, Membership.mem T r ->
      forall n, Membership.mem S n -> norm (K r n) <= 1)
    (hP : forall r, Membership.mem T r -> norm (P r) <= B) :
    energy T S f K P <= 2 * energy T S a K P +
      2 * (T.card : Real) * ((S.card : Real) * eps * B) ^ 2 := by
  have hE : 0 <= (S.card : Real) * eps * B :=
    mul_nonneg (mul_nonneg (Nat.cast_nonneg _) heps) hB
  have hrow : forall r, Membership.mem T r ->
      norm (column S f K r * P r) ^ 2 <=
        2 * norm (column S a K r * P r) ^ 2 +
          2 * ((S.card : Real) * eps * B) ^ 2 := by
    intro r hr
    have hd : norm (column S f K r * P r - column S a K r * P r) <=
        (S.card : Real) * eps * B := by
      rw [<- sub_mul, norm_mul]
      exact mul_le_mul (column_error S a f K r eps heps herr (hK r hr))
        (hP r hr) (norm_nonneg _) (mul_nonneg (Nat.cast_nonneg _) heps)
    have ht : norm (column S f K r * P r) <=
        norm (column S a K r * P r) + (S.card : Real) * eps * B := by
      calc
        norm (column S f K r * P r) =
            norm (column S a K r * P r +
              (column S f K r * P r - column S a K r * P r)) := by
          congr 1
          ring
        _ <= norm (column S a K r * P r) +
            norm (column S f K r * P r - column S a K r * P r) :=
          norm_add_le _ _
        _ <= norm (column S a K r * P r) +
            (S.card : Real) * eps * B := _root_.add_le_add le_rfl hd
    have hs : norm (column S f K r * P r) ^ 2 <=
        (norm (column S a K r * P r) + (S.card : Real) * eps * B) ^ 2 := by
      gcongr
    nlinarith [sq_nonneg
      (norm (column S a K r * P r) - (S.card : Real) * eps * B)]
  calc
    energy T S f K P <= T.sum (fun r =>
        2 * norm (column S a K r * P r) ^ 2 +
          2 * ((S.card : Real) * eps * B) ^ 2) := Finset.sum_le_sum hrow
    _ = 2 * energy T S a K P +
        2 * (T.card : Real) * ((S.card : Real) * eps * B) ^ 2 := by
      simp only [energy, Finset.sum_add_distrib, Finset.mul_sum,
        Finset.sum_const, nsmul_eq_mul]
      ring

theorem quartic_error_budget {I J : Type} (T : Finset J) (S : Finset I)
    (a f : I -> Complex) (K : J -> I -> Complex) (P : J -> Complex)
    (D A B C R : Real) (hD : 0 < D)
    (hA : 0 <= A) (hB : 0 <= B) (hC : 0 <= C) (hR : 0 <= R)
    (hS : (S.card : Real) <= A * D)
    (hT : (T.card : Real) <= R * D ^ 4)
    (herr : forall n, Membership.mem S n -> norm (f n - a n) <= C / D ^ 3)
    (hK : forall r, Membership.mem T r ->
      forall n, Membership.mem S n -> norm (K r n) <= 1)
    (hP : forall r, Membership.mem T r -> norm (P r) <= B * D ^ 3) :
    energy T S f K P <= 2 * energy T S a K P +
      2 * R * A ^ 2 * B ^ 2 * C ^ 2 * D ^ 6 := by
  have hcancel : (S.card : Real) * (C / D ^ 3) * (B * D ^ 3) =
      (S.card : Real) * C * B := by
    field_simp [hD.ne'] <;> ring
  have hbound : (S.card : Real) * C * B <= A * D * C * B := by
    gcongr
  have hbase := energy_transfer T S a f K P (C / D ^ 3) (B * D ^ 3)
    (div_nonneg hC (pow_nonneg hD.le _)) (mul_nonneg hB (pow_nonneg hD.le _))
    herr hK hP
  rw [hcancel] at hbase
  calc
    energy T S f K P <= 2 * energy T S a K P +
        2 * (T.card : Real) * ((S.card : Real) * C * B) ^ 2 := hbase
    _ <= 2 * energy T S a K P +
        2 * (R * D ^ 4) * (A * D * C * B) ^ 2 := by
      gcongr
    _ = 2 * energy T S a K P +
        2 * R * A ^ 2 * B ^ 2 * C ^ 2 * D ^ 6 := by ring

end PrimeFactorOscillations.UniformCarrier.AmplifiedMoment

/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.EulerUniformTail

/-! # Finite signed Euler packets with a uniform analytic remainder -/

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 5000000

noncomputable section
namespace PrimeFactorOscillations

open Complex Robin1984
open scoped ComplexOrder

def compensatedEulerPoint (t : Real) : Complex :=
  zetaEulerLogDeriv (xiResolventPoint 2 t) -
    (2 / 3 : Complex) * zetaEulerLogDeriv (xiResolventPoint 3 t)

def compensatedEulerTerm (t : Real) (n : Nat) : Complex :=
  -(((1 - (2 / 3) / (n : Real)) : Real) : Complex) *
    LSeries.term (fun k : Nat => (ArithmeticFunction.vonMangoldt k : Complex))
      (xiResolventPoint 2 t) n

def compensatedEulerHead (N : Nat) (t : Real) : Complex :=
  Finset.sum (Finset.range (N + 1)) (compensatedEulerTerm t)

def compensatedEulerPacket (N : Nat) (t : Real) : Real :=
  ((compensatedEulerHead N t).re + (compensatedEulerHead N (-t)).re) / 2

theorem compensatedEulerTerm_eq (t : Real) (n : Nat) :
    compensatedEulerTerm t n =
      -(LSeries.term (fun k : Nat => (ArithmeticFunction.vonMangoldt k : Complex))
          (xiResolventPoint 2 t) n -
        (2 / 3 : Complex) *
          LSeries.term (fun k : Nat => (ArithmeticFunction.vonMangoldt k : Complex))
            (xiResolventPoint 3 t) n) := by
  by_cases hn : n = 0
  next => subst n; simp only [compensatedEulerTerm, LSeries.term_zero, mul_zero, sub_self, neg_zero]
  next =>
    have hnC : Not ((n : Complex) = 0) := by exact_mod_cast hn
    have hshift : xiResolventPoint 2 t + 1 = xiResolventPoint 3 t := by
      simp only [xiResolventPoint]
      push_cast
      ring
    have hh := eulerTerm_successor
      (fun k : Nat => (ArithmeticFunction.vonMangoldt k : Complex)) (xiResolventPoint 2 t) n hn
    rw [hshift] at hh
    rw [compensatedEulerTerm, hh]
    push_cast
    field_simp [hnC] <;> ring

theorem compensatedEulerTerm_norm_le (t : Real) (n : Nat) :
    norm (compensatedEulerTerm t n) <= eulerLogProfile n := by
  by_cases hn : n = 0
  next => subst n; norm_num [compensatedEulerTerm, LSeries.term_zero, eulerLogProfile]
  next =>
    have hn1 : (1 : Real) <= (n : Real) := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hn
    have hn0 : 0 < (n : Real) := by linarith only [hn1]
    have hd : (0 : Real) <= (2 / 3) / (n : Real) := div_nonneg (by norm_num) hn0.le
    have hd1 : (2 / 3 : Real) / (n : Real) <= 1 := by
      have hh : (2 / 3 : Real) <= (n : Real) := by linarith only [hn1]
      exact (div_le_one hn0).mpr hh
    have hw0 : (0 : Real) <= 1 - (2 / 3) / (n : Real) := sub_nonneg.mpr hd1
    have hw1 : (1 : Real) - (2 / 3) / (n : Real) <= 1 := by linarith only [hd]
    have hnorm : norm (LSeries.term
        (fun k : Nat => (ArithmeticFunction.vonMangoldt k : Complex))
        (xiResolventPoint 2 t) n) <= eulerLogProfile n := by
      rw [LSeries.norm_term_eq, if_neg hn]
      have hs : (xiResolventPoint 2 t).re = 5 / 2 := by norm_num [xiResolventPoint]
      rw [hs, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg ArithmeticFunction.vonMangoldt_nonneg]
      have hlog : ArithmeticFunction.vonMangoldt n <= Real.log (n : Real) :=
        ArithmeticFunction.vonMangoldt_le_log
      have hh := div_le_div_of_nonneg_right hlog
        (Real.rpow_nonneg (Nat.cast_nonneg n) (5 / 2 : Real))
      simpa only [eulerLogProfile, Real.rpow_neg (Nat.cast_nonneg n), div_eq_mul_inv] using hh
    rw [compensatedEulerTerm, norm_mul, norm_neg, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg hw0]
    exact (mul_le_of_le_one_left (norm_nonneg _) hw1).trans hnorm

theorem compensatedEulerTerm_summable (t : Real) : Summable (compensatedEulerTerm t) := by
  have hsa := ArithmeticFunction.LSeriesSummable_vonMangoldt
    (s := xiResolventPoint 2 t) (by norm_num [xiResolventPoint])
  have hsb := ArithmeticFunction.LSeriesSummable_vonMangoldt
    (s := xiResolventPoint 3 t) (by norm_num [xiResolventPoint])
  exact (hsa.sub (hsb.mul_left (2 / 3 : Complex))).neg.congr
    (fun n => (compensatedEulerTerm_eq t n).symm)

theorem compensatedEulerTerm_tsum (t : Real) :
    tsum (compensatedEulerTerm t) = compensatedEulerPoint t := by
  let f : Nat -> Complex := fun k => (ArithmeticFunction.vonMangoldt k : Complex)
  have hsa : LSeriesSummable f (xiResolventPoint 2 t) :=
    ArithmeticFunction.LSeriesSummable_vonMangoldt (by norm_num [xiResolventPoint])
  have hsb : LSeriesSummable f (xiResolventPoint 3 t) :=
    ArithmeticFunction.LSeriesSummable_vonMangoldt (by norm_num [xiResolventPoint])
  have hLa : LSeries f (xiResolventPoint 2 t) = -zetaEulerLogDeriv (xiResolventPoint 2 t) := by
    simpa only [zetaEulerLogDeriv, neg_div] using
      ArithmeticFunction.LSeries_vonMangoldt_eq_deriv_riemannZeta_div
        (s := xiResolventPoint 2 t) (by norm_num [xiResolventPoint])
  have hLb : LSeries f (xiResolventPoint 3 t) = -zetaEulerLogDeriv (xiResolventPoint 3 t) := by
    simpa only [zetaEulerLogDeriv, neg_div] using
      ArithmeticFunction.LSeries_vonMangoldt_eq_deriv_riemannZeta_div
        (s := xiResolventPoint 3 t) (by norm_num [xiResolventPoint])
  calc
    tsum (compensatedEulerTerm t) =
        tsum (fun n => -(LSeries.term f (xiResolventPoint 2 t) n -
          (2 / 3 : Complex) * LSeries.term f (xiResolventPoint 3 t) n)) :=
      tsum_congr (compensatedEulerTerm_eq t)
    _ = -(LSeries f (xiResolventPoint 2 t) - (2 / 3 : Complex) *
        LSeries f (xiResolventPoint 3 t)) := by
      rw [tsum_neg, hsa.tsum_sub (hsb.mul_left (2 / 3 : Complex)), tsum_mul_left]
      rfl
    _ = compensatedEulerPoint t := by rw [hLa, hLb]; dsimp only [compensatedEulerPoint]; ring

theorem compensatedEulerPacket_error (N : Nat) (t : Real) (hN : 6 <= N) :
    norm (compensatedEulerPoint t - compensatedEulerHead N t) <= eulerUniformTail N := by
  have hs := compensatedEulerTerm_summable t
  have ht : Summable (fun n => compensatedEulerTerm t (n + (N + 1))) :=
    hs.comp_injective (fun _ _ h => Nat.add_right_cancel h)
  have hp : Summable (fun n : Nat => eulerLogProfile (n + (N + 1) : Nat)) :=
    eulerLogProfile_summable.comp_injective (fun _ _ h => Nat.add_right_cancel h)
  have hsplit := hs.sum_add_tsum_nat_add (N + 1)
  have he : compensatedEulerPoint t - compensatedEulerHead N t =
      tsum (fun n => compensatedEulerTerm t (n + (N + 1))) := by
    rw [<- compensatedEulerTerm_tsum t, <- hsplit]
    dsimp only [compensatedEulerHead]
    ring
  rw [he]
  exact ((norm_tsum_le_tsum_norm ht.norm).trans
    (ht.norm.tsum_le_tsum (fun n => compensatedEulerTerm_norm_le t (n + (N + 1))) hp)).trans
      (eulerLogProfile_tsum_tail_from N hN)

theorem compensatedEulerPacket_upper (N : Nat) (t : Real) (hN : 6 <= N) :
    (compensatedEulerPoint t).re <= (compensatedEulerHead N t).re + eulerUniformTail N := by
  have hh := (Complex.re_le_norm (compensatedEulerPoint t - compensatedEulerHead N t)).trans
    (compensatedEulerPacket_error N t hN)
  simp only [Complex.sub_re] at hh
  linarith only [hh]

theorem compensatedEulerPacket_even (N : Nat) (t : Real) :
    compensatedEulerPacket N (-t) = compensatedEulerPacket N t := by
  simp only [compensatedEulerPacket, neg_neg]
  ring

end PrimeFactorOscillations

/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import Mathlib.Analysis.Complex.Trigonometric
import PrimeFactorOscillations.Helpers.CompensatedEulerPacket

/-! # Exact real phases of the retained compensated Euler packet -/

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 5000000

noncomputable section
namespace PrimeFactorOscillations

open Complex Robin1984

def compensatedEulerWeight (n : Nat) : Real :=
  ArithmeticFunction.vonMangoldt n * (1 - (2 / 3) / (n : Real)) *
    (n : Real) ^ (-(5 / 2) : Real)

def compensatedEulerCosPacket (N : Nat) (t : Real) : Real :=
  Finset.sum (Finset.range (N + 1))
    (fun n => -compensatedEulerWeight n * Real.cos (t * Real.log (n : Real)))

theorem compensatedEulerTerm_re (t : Real) (n : Nat) :
    (compensatedEulerTerm t n).re =
      -compensatedEulerWeight n * Real.cos (t * Real.log (n : Real)) := by
  by_cases hn : n = 0
  next => subst n; norm_num [compensatedEulerTerm, LSeries.term_zero, compensatedEulerWeight]
  next =>
    have hnR : 0 < (n : Real) := by exact_mod_cast Nat.pos_of_ne_zero hn
    have hnC : Not ((n : Complex) = 0) := by exact_mod_cast hn
    have hTerm : LSeries.term
        (fun k : Nat => (ArithmeticFunction.vonMangoldt k : Complex))
        (xiResolventPoint 2 t) n =
        (ArithmeticFunction.vonMangoldt n : Complex) *
          (n : Complex) ^ (-xiResolventPoint 2 t) := by
      rw [LSeries.term_of_ne_zero hn, Complex.cpow_neg, div_eq_mul_inv]
    rw [compensatedEulerTerm, hTerm, Complex.cpow_def_of_ne_zero hnC]
    simp only [<- Complex.natCast_log]
    norm_num [Complex.mul_re, Complex.mul_im, Complex.exp_re, xiResolventPoint,
      compensatedEulerWeight, Real.rpow_def_of_pos hnR, mul_neg, neg_mul, Real.cos_neg,
      mul_comm] <;> ring

theorem compensatedEulerHead_re_cos (N : Nat) (t : Real) :
    (compensatedEulerHead N t).re = compensatedEulerCosPacket N t := by
  simp [compensatedEulerHead, compensatedEulerCosPacket, compensatedEulerTerm_re]

theorem compensatedEulerPacket_cos (N : Nat) (t : Real) :
    compensatedEulerPacket N t = compensatedEulerCosPacket N t := by
  simp only [compensatedEulerPacket, compensatedEulerHead_re_cos,
    compensatedEulerCosPacket, neg_mul, Real.cos_neg]
  ring

theorem compensatedEulerWeight_nonneg (n : Nat) : 0 <= compensatedEulerWeight n := by
  by_cases hn : n = 0
  next => subst n; norm_num [compensatedEulerWeight]
  next =>
    have hn1 : (1 : Real) <= (n : Real) := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hn
    have hn0 : 0 < (n : Real) := by linarith only [hn1]
    have hc : (2 / 3 : Real) / (n : Real) <= 1 := by
      exact (div_le_one hn0).mpr (by linarith only [hn1])
    exact mul_nonneg
      (mul_nonneg ArithmeticFunction.vonMangoldt_nonneg (sub_nonneg.mpr hc))
      (Real.rpow_nonneg (Nat.cast_nonneg n) _)

end PrimeFactorOscillations

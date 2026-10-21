/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.PrimeClassDecoderHalfInteger
import PrimeFactorOscillations.Helpers.PrimeClassDecoderPrimeMass

/-!
# Finite signed factors before the half-integer product limit

The finite product keeps the exact negative-factor parity. Its early
separation and late logarithmic supply enter one product inequality.
-/

set_option autoImplicit false
set_option Elab.async false

namespace PrimeFactorOscillations.PrimeClassSampling

open PrimeFactorOscillations.PrimeClassDecoder

theorem lateHalfInteger_factor_ge_exp
    (R p n : Nat) (hR : 1 <= R) (hn : n <= R) (hpR : 4 * R + 2 < p) :
    Real.exp (-5 * (R : Real) / (p : Real)) <=
      ((p : Real) - (n : Real) - 3 / 2) / (p : Real) := by
  have hp : 0 < p := by omega
  have hpReal : (0 : Real) < (p : Real) := by exact_mod_cast hp
  have hRR : (1 : Real) <= (R : Real) := by exact_mod_cast hR
  have hnR : (n : Real) <= (R : Real) := by exact_mod_cast hn
  have hb := lateHalfInteger_ratio_bounds R p n hR hn hpR
  have hid : ((p : Real) - (n : Real) - 3 / 2) / (p : Real) =
      1 - ((n : Real) + 3 / 2) / (p : Real) := by field_simp; ring
  have hfpos : 0 < ((p : Real) - (n : Real) - 3 / 2) / (p : Real) := by
    rw [hid]
    linarith [hb.2]
  have hlog := log_one_sub_ge_neg_two_mul _ hb.1 hb.2.le
  have hnum : 2 * ((n : Real) + 3 / 2) <= 5 * (R : Real) := by linarith
  have hdiv := div_le_div_of_nonneg_right hnum hpReal.le
  have hmul : 2 * (((n : Real) + 3 / 2) / (p : Real)) <=
      5 * (R : Real) / (p : Real) := by
    calc
      _ = 2 * ((n : Real) + 3 / 2) / (p : Real) := by ring
      _ <= _ := hdiv
  have hbound : -5 * (R : Real) / (p : Real) <=
      Real.log (((p : Real) - (n : Real) - 3 / 2) / (p : Real)) := by
    rw [hid]
    have hneg : -5 * (R : Real) / (p : Real) = -(5 * (R : Real) / (p : Real)) := by ring
    rw [hneg]
    linarith
  exact (Real.exp_le_exp.mpr hbound).trans_eq (Real.exp_log hfpos)

theorem halfInteger_factor_abs_ge_exp
    (R p n : Nat) (hR : 1 <= R) (hn : n <= R) (hp : 0 < p) :
    Real.exp (if p <= 4 * R + 2 then -Real.log (12 * (R : Real)) else
      -5 * (R : Real) / (p : Real)) <=
        abs (((p : Real) - (n : Real) - 3 / 2) / (p : Real)) := by
  by_cases hpearly : p <= 4 * R + 2
  case pos =>
    rw [ite_eq_left hpearly, Real.exp_neg, Real.exp_log (by positivity : (0 : Real) < 12 * R)]
    simpa only [one_div] using earlyHalfInteger_factor_abs_ge R p n hR hp hpearly
  case neg =>
    rw [ite_eq_right hpearly]
    exact (lateHalfInteger_factor_ge_exp R p n hR hn (lt_of_not_ge hpearly)).trans
      (le_abs_self _)

theorem signed_halfInteger_prod_eq_prod_abs
    (s : Finset Nat) (n : Nat) (hpos : forall p : Nat, Membership.mem s p -> 0 < p) :
    (-1 : Real) ^ (s.filter (fun p => p <= n + 1)).card *
      s.prod (fun p => ((p : Real) - (n : Real) - 3 / 2) / (p : Real)) =
        s.prod (fun p => abs (((p : Real) - (n : Real) - 3 / 2) / (p : Real))) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert p s hp ih =>
    have hppos : 0 < p := hpos p (Finset.mem_insert_self p s)
    have hspos : forall q : Nat, Membership.mem s q -> 0 < q := by
      intro q hq
      exact hpos q (Finset.mem_insert_of_mem hq)
    have hif := ih hspos
    have hpfilter : Not (Membership.mem (s.filter (fun q => q <= n + 1)) p) := by
      intro h
      exact hp (Finset.mem_filter.mp h).1
    by_cases hpn : p <= n + 1
    case pos =>
      have hneg := (halfInteger_factor_neg_iff p n hppos).mpr hpn
      have hfilter : (insert p s).filter (fun q => q <= n + 1) =
          insert p (s.filter (fun q => q <= n + 1)) := by
        rw [Finset.filter_insert, ite_eq_left hpn]
      rw [hfilter, Finset.card_insert_of_notMem hpfilter, pow_succ,
        Finset.prod_insert hp, Finset.prod_insert hp, abs_of_neg hneg, <- hif]
      ring
    case neg =>
      have hnonneg : 0 <= ((p : Real) - (n : Real) - 3 / 2) / (p : Real) := by
        apply le_of_not_gt
        intro h
        exact hpn ((halfInteger_factor_neg_iff p n hppos).mp h)
      have hfilter : (insert p s).filter (fun q => q <= n + 1) =
          s.filter (fun q => q <= n + 1) := by
        rw [Finset.filter_insert, ite_eq_right hpn]
      rw [hfilter, Finset.prod_insert hp, Finset.prod_insert hp, abs_of_nonneg hnonneg, <- hif]
      ring

theorem signed_halfInteger_prod_ge_exp_sum
    (s : Finset Nat) (R n : Nat) (hR : 1 <= R) (hn : n <= R)
    (hpos : forall p : Nat, Membership.mem s p -> 0 < p) :
    Real.exp (s.sum (fun p => if p <= 4 * R + 2 then -Real.log (12 * (R : Real)) else
      -5 * (R : Real) / (p : Real))) <=
      (-1 : Real) ^ (s.filter (fun p => p <= n + 1)).card *
        s.prod (fun p => ((p : Real) - (n : Real) - 3 / 2) / (p : Real)) := by
  rw [signed_halfInteger_prod_eq_prod_abs s n hpos]
  induction s using Finset.induction_on with
  | empty => simp
  | @insert p s hp ih =>
    have hspos : forall q : Nat, Membership.mem s q -> 0 < q := by
      intro q hq
      exact hpos q (Finset.mem_insert_of_mem hq)
    rw [Finset.sum_insert hp, Real.exp_add, Finset.prod_insert hp]
    exact mul_le_mul (halfInteger_factor_abs_ge_exp R p n hR hn
      (hpos p (Finset.mem_insert_self p s))) (ih hspos) (Real.exp_nonneg _) (abs_nonneg _)

theorem sum_halfInteger_lowerExponents
    (s : Finset Nat) (R : Nat) :
    s.sum (fun p => if p <= 4 * R + 2 then -Real.log (12 * (R : Real)) else
      -5 * (R : Real) / (p : Real)) =
        -((s.filter (fun p => p <= 4 * R + 2)).card : Real) * Real.log (12 * (R : Real)) -
          5 * (R : Real) * (s.filter (fun p => 4 * R + 2 < p)).sum (fun p => 1 / (p : Real)) := by
  classical
  have hsplit : s.sum (fun p => if p <= 4 * R + 2 then -Real.log (12 * (R : Real)) else
      -5 * (R : Real) / (p : Real)) =
      (s.filter (fun p => p <= 4 * R + 2)).sum (fun _ => -Real.log (12 * (R : Real))) +
        (s.filter (fun p => 4 * R + 2 < p)).sum (fun p => -5 * (R : Real) / (p : Real)) := by
    rw [Finset.sum_filter, Finset.sum_filter, <- Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro p _
    by_cases hp : p <= 4 * R + 2
    case pos => simp [hp, not_lt_of_ge hp]
    case neg => simp [hp, lt_of_not_ge hp]
  have hlate : (s.filter (fun p => 4 * R + 2 < p)).sum
      (fun p => -5 * (R : Real) / (p : Real)) =
        (-5 * (R : Real)) * (s.filter (fun p => 4 * R + 2 < p)).sum
          (fun p => 1 / (p : Real)) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro p _
    ring
  rw [hsplit, hlate, Finset.sum_const, nsmul_eq_mul]
  ring

theorem primeClassPrefix_filter_le
    (P : Set Nat) (Y B : Nat) (hBY : B <= Y) :
    (primeClassPrefix P Y).filter (fun p => p <= B) = primeClassPrefix P B := by
  classical
  apply Finset.ext
  intro p
  simp only [primeClassPrefix, Finset.mem_filter, Finset.mem_Icc]
  constructor
  case mp =>
    intro h
    exact And.intro (And.intro h.1.1.1 h.2) h.1.2
  case mpr =>
    intro h
    exact And.intro (And.intro (And.intro h.1.1 (h.1.2.trans hBY)) h.2) h.1.2

end PrimeFactorOscillations.PrimeClassSampling

/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/

import PrimeFactorOscillations.Helpers.PrimeProfileFullWindowReadout
import PrimeFactorOscillations.Mathlib.Analysis.SpecialFunctions.Log.PolynomialReciprocalTransport

/-!
# Polynomial square-filter readout of prime transport

Only entering and leaving coordinates are tested against the filter window.
All common coordinates cancel exactly. The complete error is bounded by the
squared filter norm times the original transport, preserving its coefficient.
-/

set_option autoImplicit false
set_option Elab.async false

noncomputable section

namespace PrimeFactorOscillations.PrimeProfileRigidity

/-- The complete signed observable for a polynomial square filter. -/
def primePrefixSquareFilterTransport (H : Polynomial Real)
    (e : Equiv.Perm Nat) (n : Nat) : Real :=
  let r : Real := PrimeFactorUnimodality.primeAt n
  Finset.prefixDefect (fun j =>
    ((PrimeFactorUnimodality.primeAt j : Real) - r) *
      (1 - (Polynomial.eval (r / PrimeFactorUnimodality.primeAt j) H) ^ 2)) e (n + 1)

/-- A filter equal to one at zero really uses finitely many probability moments. -/
theorem primePrefixSquareFilterTransport_polynomial (H : Polynomial Real)
    (hH0 : Polynomial.eval 0 H = 1) (e : Equiv.Perm Nat) (n : Nat) :
    exists G : Polynomial Real,
      G.natDegree <= 2 * H.natDegree /\
      primePrefixSquareFilterTransport H e n =
        (PrimeFactorUnimodality.primeAt n : Real) *
          Finset.prefixDefect (fun j => Polynomial.eval
            ((PrimeFactorUnimodality.primeAt n : Real) /
              PrimeFactorUnimodality.primeAt j) G) e (n + 1) := by
  have hex := Polynomial.exists_square_filter_transport_polynomial H hH0
  let G := Classical.choose hex
  have hG := Classical.choose_spec hex
  refine Exists.intro G (And.intro hG.1 ?_)
  unfold primePrefixSquareFilterTransport Finset.prefixDefect
  dsimp only
  rw [mul_sub, Finset.mul_sum, Finset.mul_sum]
  congr 1 <;> apply Finset.sum_congr rfl
  all_goals
    intro j hj
    apply Eq.symm
    apply hG.2
    exact_mod_cast (PrimeFactorUnimodality.prime_primeAt _).ne_zero

/-- The squared filter norm controls the same full signed transport. -/
theorem primePrefixSquareFilterTransport_bounds
    (H : Polynomial Real) (eta : Real)
    (hwindow : forall x : Real, (1 / 2 : Real) <= x -> x <= 4 / 3 ->
      abs (Polynomial.eval x H) <= eta)
    (e : Equiv.Perm Nat) (t : Nat -> Real) (n : Nat) (C : Real)
    (ht : 0 < t n)
    (hC : C < (PrimeFactorUnimodality.primeAt n : Real) / 4)
    (hcost : normalizedPrimePrefixDefect e t n <= C) :
    (1 - eta ^ 2) *
        Finset.prefixDefect (fun j => (PrimeFactorUnimodality.primeAt j : Real))
          e (n + 1) <= primePrefixSquareFilterTransport H e n /\
      primePrefixSquareFilterTransport H e n <=
        Finset.prefixDefect (fun j => (PrimeFactorUnimodality.primeAt j : Real))
          e (n + 1) := by
  let p : Nat -> Real := fun j => PrimeFactorUnimodality.primeAt j
  let r : Real := p n
  let g : Nat -> Real := fun j =>
    (p j - r) * (1 - (Polynomial.eval (r / p j) H) ^ 2)
  let s := (Finset.range (n + 1)).image e
  let u := Finset.range (n + 1)
  have hc : s.card = u.card := Finset.card_image_iff.mpr
    (fun _ _ _ _ h => e.injective h)
  have hr : 0 < r := by
    dsimp only [r, p]
    exact_mod_cast (PrimeFactorUnimodality.prime_primeAt n).pos
  have hbudget : C < r / 4 := hC
  have hmono : Monotone p := by
    intro i j hij
    dsimp only [p]
    exact_mod_cast PrimeFactorUnimodality.primeAt_strictMono.monotone hij
  have hlocal := prime_prefix_coordinates_localized_of_cost_le e t n C ht hC hcost
  have hin : forall j, Membership.mem (s \ u) j ->
      (1 - eta ^ 2) * (p j - r) <= g j - 0 /\
        g j - 0 <= 1 * (p j - r) := by
    intro j hj
    have hn := (Finset.mem_sdiff.mp hj).2
    change Not (Membership.mem (Finset.range (n + 1)) j) at hn
    rw [Finset.mem_range] at hn
    have hidx : n <= j := by omega
    have hpr : r <= p j := hmono hidx
    have hp : 0 < p j := hr.trans_le hpr
    have hgap : p j - r <= 4 * C := hlocal.1 j hj
    have hid : r / p j * p j = r := by field_simp
    have hlo : (1 / 2 : Real) <= r / p j := by
      by_contra hnlo
      have hm := mul_lt_mul_of_pos_right (lt_of_not_ge hnlo) hp
      rw [hid] at hm
      linarith only [hm, hgap, hbudget]
    have hup : r / p j <= (4 / 3 : Real) := by
      by_contra hnup
      have hm := mul_lt_mul_of_pos_right (lt_of_not_ge hnup) hp
      rw [hid] at hm
      linarith only [hm, hpr, hp]
    have hb := Real.reciprocal_square_filter_mul_bounds (p j - r)
      (Polynomial.eval (r / p j) H) eta (sub_nonneg.mpr hpr) (hwindow _ hlo hup)
    simpa only [g, sub_zero, one_mul] using hb
  have hout : forall j, Membership.mem (u \ s) j ->
      (1 - eta ^ 2) * (r - p j) <= 0 - g j /\
        0 - g j <= 1 * (r - p j) := by
    intro j hj
    have hn := (Finset.mem_sdiff.mp hj).1
    change Membership.mem (Finset.range (n + 1)) j at hn
    rw [Finset.mem_range] at hn
    have hidx : j <= n := by omega
    have hpr : p j <= r := hmono hidx
    have hgap : r - p j <= C := hlocal.2 j hj
    have hp : 0 < p j := by linarith only [hgap, hbudget, hr]
    have hid : r / p j * p j = r := by field_simp
    have hlo : (1 / 2 : Real) <= r / p j := by
      by_contra hnlo
      have hm := mul_lt_mul_of_pos_right (lt_of_not_ge hnlo) hp
      rw [hid] at hm
      linarith only [hm, hpr, hp]
    have hup : r / p j <= (4 / 3 : Real) := by
      by_contra hnup
      have hm := mul_lt_mul_of_pos_right (lt_of_not_ge hnup) hp
      rw [hid] at hm
      linarith only [hm, hgap, hbudget]
    have hb := Real.reciprocal_square_filter_mul_bounds (r - p j)
      (Polynomial.eval (r / p j) H) eta (sub_nonneg.mpr hpr) (hwindow _ hlo hup)
    have hg : 0 - g j = (r - p j) *
        (1 - (Polynomial.eval (r / p j) H) ^ 2) := by dsimp only [g]; ring
    rw [hg, one_mul]
    exact hb
  have hb := Finset.reference_transport_comparison s u p g r 0
    (1 - eta ^ 2) 1 hc hin hout
  have hf : s.sum p - u.sum p = Finset.prefixDefect p e (n + 1) := by
    dsimp only [s, u]
    rw [Finset.sum_image (fun _ _ _ _ h => e.injective h)]
    rfl
  have hg : s.sum g - u.sum g = primePrefixSquareFilterTransport H e n := by
    dsimp only [s, u]
    rw [Finset.sum_image (fun _ _ _ _ h => e.injective h)]
    rfl
  rw [hf, hg, one_mul] at hb
  exact hb

/-- Keep the principal coefficient one and control the complete signed error. -/
theorem primePrefixSquareFilterTransport_error
    (H : Polynomial Real) (eta : Real)
    (hwindow : forall x : Real, (1 / 2 : Real) <= x -> x <= 4 / 3 ->
      abs (Polynomial.eval x H) <= eta)
    (e : Equiv.Perm Nat) (t : Nat -> Real) (n : Nat) (C : Real)
    (ht : 0 < t n) (hC0 : 0 <= C)
    (hC : C < (PrimeFactorUnimodality.primeAt n : Real) / 4)
    (hcost : normalizedPrimePrefixDefect e t n <= C) :
    0 <= Finset.prefixDefect (fun j => (PrimeFactorUnimodality.primeAt j : Real))
        e (n + 1) - primePrefixSquareFilterTransport H e n /\
      (Finset.prefixDefect (fun j => (PrimeFactorUnimodality.primeAt j : Real))
        e (n + 1) - primePrefixSquareFilterTransport H e n <= eta ^ 2 *
          Finset.prefixDefect (fun j => (PrimeFactorUnimodality.primeAt j : Real))
            e (n + 1)) /\
      (Finset.prefixDefect (fun j => (PrimeFactorUnimodality.primeAt j : Real))
        e (n + 1) - primePrefixSquareFilterTransport H e n <= 4 * C * eta ^ 2) := by
  let S : Real := Finset.prefixDefect
    (fun j => (PrimeFactorUnimodality.primeAt j : Real)) e (n + 1)
  have hb := primePrefixSquareFilterTransport_bounds H eta hwindow e t n C ht hC hcost
  have hSC : S <= 4 * C := prime_prefix_transport_le_four_mul_cost e t n C ht hC0 hC hcost
  have hm := mul_le_mul_of_nonneg_left hSC (sq_nonneg eta)
  have hlo : (1 - eta ^ 2) * S <= primePrefixSquareFilterTransport H e n := hb.1
  refine And.intro (sub_nonneg.mpr hb.2) (And.intro ?_ ?_)
  . nlinarith only [hlo]
  . nlinarith only [hlo, hm]

end PrimeFactorOscillations.PrimeProfileRigidity

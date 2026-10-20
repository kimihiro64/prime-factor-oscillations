/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/

import PrimeFactorOscillations.Helpers.PrimeProfileCostLocalization

/-!
# The same integer transport controls every positive probability probe

A bounded cost at one probe localizes the entire finite transport.
The resulting comparison keeps the exact signed transport sum and
holds for every new positive probe at the same cutoff.
-/

set_option autoImplicit false
set_option Elab.async false

noncomputable section

namespace PrimeFactorOscillations.PrimeProfileRigidity

theorem prime_prefix_transport_bounds_of_cost_le
    (e : Equiv.Perm Nat) (t : Nat -> Real) (n : Nat) (C : Real)
    (ht : 0 < t n) (hC0 : 0 <= C)
    (hC : C < (PrimeFactorUnimodality.primeAt n : Real) / 4)
    (hcost : normalizedPrimePrefixDefect e t n <= C)
    (v : Nat -> Real) (hv : 0 < v n) :
    Finset.prefixDefect (fun j => (PrimeFactorUnimodality.primeAt j : Real)) e (n + 1) *
        ((PrimeFactorUnimodality.primeAt n : Real) /
          ((PrimeFactorUnimodality.primeAt n : Real) + 4 * C)) ^ 2 <=
      normalizedPrimePrefixDefect e v n /\
    normalizedPrimePrefixDefect e v n <=
      Finset.prefixDefect (fun j => (PrimeFactorUnimodality.primeAt j : Real)) e (n + 1) *
        ((PrimeFactorUnimodality.primeAt n : Real) /
          ((PrimeFactorUnimodality.primeAt n : Real) - C)) ^ 2 := by
  let p : Nat -> Real := fun j => PrimeFactorUnimodality.primeAt j
  let r : Real := p n
  let c : Real := r ^ 2 * (r + v n) / (v n) ^ 2
  let g : Nat -> Real := fun j => c * primeLogWeight (v n) j
  let s := (Finset.range (n + 1)).image e
  let u := Finset.range (n + 1)
  have hc : s.card = u.card := Finset.card_image_iff.mpr
    (fun _ _ _ _ h => e.injective h)
  have hp : forall j, 0 < p j := by
    intro j
    dsimp only [p]
    exact_mod_cast (PrimeFactorUnimodality.prime_primeAt j).pos
  have hmono : Monotone p := by
    intro i j hij
    dsimp only [p]
    exact_mod_cast PrimeFactorUnimodality.primeAt_strictMono.monotone hij
  have hr : 0 < r := hp n
  have hbudget : C < r / 4 := hC
  have hL : 0 < r - C := by linarith only [hr, hbudget]
  have hlocal := prime_prefix_coordinates_localized_of_cost_le e t n C ht hC hcost
  have hin : forall j, Membership.mem (s \ u) j ->
      (r / (r + 4 * C)) ^ 2 * (p j - r) <= g j - g n /\
      g j - g n <= (r / (r - C)) ^ 2 * (p j - r) := by
    intro j hj
    have hn := (Finset.mem_sdiff.mp hj).2
    change Not (Membership.mem (Finset.range (n + 1)) j) at hn
    rw [Finset.mem_range] at hn
    have hidx : n <= j := by omega
    have hrq : r <= p j := hmono hidx
    have hbound : p j - r <= 4 * C := hlocal.1 j hj
    have hb := Real.normalized_pairLogDefect_window_bounds (v n) r (p j) r
      (r - C) (r + 4 * C) hv hL (by linarith only [hC0]) le_rfl hrq
      (by linarith only [hbound])
    have he : g j - g n =
        r ^ 2 * (r + v n) / (v n) ^ 2 * Real.pairLogDefect (v n) r (p j) := by
      dsimp only [g, c, primeLogWeight, Real.pairLogDefect, r, p]
      ring
    rw [he]
    exact And.intro (by simpa only [mul_comm] using hb.1)
      (by simpa only [mul_comm] using hb.2)
  have hout : forall j, Membership.mem (u \ s) j ->
      (r / (r + 4 * C)) ^ 2 * (r - p j) <= g n - g j /\
      g n - g j <= (r / (r - C)) ^ 2 * (r - p j) := by
    intro j hj
    have hn := (Finset.mem_sdiff.mp hj).1
    change Membership.mem (Finset.range (n + 1)) j at hn
    rw [Finset.mem_range] at hn
    have hidx : j <= n := by omega
    have hpr : p j <= r := hmono hidx
    have hbound : r - p j <= C := hlocal.2 j hj
    have hb := Real.normalized_pairLogDefect_window_bounds (v n) (p j) r r
      (r - C) (r + 4 * C) hv hL (by linarith only [hbound]) hpr le_rfl
      (by linarith only [hC0])
    have he : g n - g j =
        r ^ 2 * (r + v n) / (v n) ^ 2 * Real.pairLogDefect (v n) (p j) r := by
      dsimp only [g, c, primeLogWeight, Real.pairLogDefect, r, p]
      ring
    rw [he]
    exact And.intro (by simpa only [mul_comm] using hb.1)
      (by simpa only [mul_comm] using hb.2)
  have hb := Finset.reference_transport_comparison s u p g r (g n)
    ((r / (r + 4 * C)) ^ 2) ((r / (r - C)) ^ 2) hc hin hout
  have hf : s.sum p - u.sum p = Finset.prefixDefect p e (n + 1) := by
    dsimp only [s, u]
    rw [Finset.sum_image (fun _ _ _ _ h => e.injective h)]
    rfl
  have hg : s.sum g - u.sum g = normalizedPrimePrefixDefect e v n := by
    dsimp only [s, u, g]
    rw [Finset.sum_image (fun _ _ _ _ h => e.injective h),
      <- Finset.mul_sum, <- Finset.mul_sum, <- mul_sub]
    rfl
  rw [hf, hg] at hb
  exact And.intro (by simpa only [mul_comm] using hb.1)
    (by simpa only [mul_comm] using hb.2)

theorem prime_prefix_transport_nonneg (e : Equiv.Perm Nat) (n : Nat) :
    0 <= Finset.prefixDefect (fun j => (PrimeFactorUnimodality.primeAt j : Real))
      e (n + 1) := by
  let p : Nat -> Real := fun j => PrimeFactorUnimodality.primeAt j
  have hmono : Monotone p := by
    intro i j hij
    dsimp only [p]
    exact_mod_cast PrimeFactorUnimodality.primeAt_strictMono.monotone hij
  have hb := Finset.prefixDisplacement_mul_gap_le_prefixDefect p hmono e n
  have hnonneg : 0 <= (Finset.prefixDisplacement e (n + 1) : Real) *
      (p (n + 1) - p n) :=
    mul_nonneg (by positivity) (sub_nonneg.mpr (hmono (by omega)))
  exact hnonneg.trans hb

/-- The integer transport itself is bounded by the single-probe budget. -/
theorem prime_prefix_transport_le_four_mul_cost
    (e : Equiv.Perm Nat) (t : Nat -> Real) (n : Nat) (C : Real)
    (ht : 0 < t n) (hC0 : 0 <= C)
    (hC : C < (PrimeFactorUnimodality.primeAt n : Real) / 4)
    (hcost : normalizedPrimePrefixDefect e t n <= C) :
    Finset.prefixDefect (fun j => (PrimeFactorUnimodality.primeAt j : Real))
      e (n + 1) <= 4 * C := by
  let r : Real := PrimeFactorUnimodality.primeAt n
  let S : Real := Finset.prefixDefect
    (fun j => (PrimeFactorUnimodality.primeAt j : Real)) e (n + 1)
  have hr : 0 < r := by
    dsimp only [r]
    exact_mod_cast (PrimeFactorUnimodality.prime_primeAt n).pos
  have hbudget : C < r / 4 := hC
  have hden : r + 4 * C <= 2 * r := by linarith only [hbudget]
  have hpos : 0 < r + 4 * C := by positivity
  have hratio : (1 / 2 : Real) <= r / (r + 4 * C) := by
    have hb := div_le_div_of_nonneg_left hr.le hpos hden
    have he : r / (2 * r) = (1 / 2 : Real) := by field_simp [hr.ne']
    rw [he] at hb
    exact hb
  have hsquare : (1 / 4 : Real) <= (r / (r + 4 * C)) ^ 2 := by
    nlinarith only [hratio, sq_nonneg (r / (r + 4 * C) - 1 / 2)]
  have hS : 0 <= S := prime_prefix_transport_nonneg e n
  have hm := mul_le_mul_of_nonneg_left hsquare hS
  have hl : S * (r / (r + 4 * C)) ^ 2 <= normalizedPrimePrefixDefect e t n :=
    (prime_prefix_transport_bounds_of_cost_le e t n C ht hC0 hC hcost t ht).1
  linarith only [hm, hl, hcost]

/-- One bounded probe fixes the exact transport seen by all other positive probes. -/
theorem prime_prefix_transport_uniform_error
    (e : Equiv.Perm Nat) (t : Nat -> Real) (n : Nat) (C : Real)
    (ht : 0 < t n) (hC0 : 0 <= C)
    (hC : C < (PrimeFactorUnimodality.primeAt n : Real) / 4)
    (hcost : normalizedPrimePrefixDefect e t n <= C)
    (v : Nat -> Real) (hv : 0 < v n) :
    abs (normalizedPrimePrefixDefect e v n -
      Finset.prefixDefect (fun j => (PrimeFactorUnimodality.primeAt j : Real)) e (n + 1)) <=
        32 * C ^ 2 / (PrimeFactorUnimodality.primeAt n : Real) := by
  have hb := prime_prefix_transport_bounds_of_cost_le e t n C ht hC0 hC hcost v hv
  exact Real.reference_transport_sandwich_abs_error
    (PrimeFactorUnimodality.primeAt n : Real) C
    (Finset.prefixDefect (fun j => (PrimeFactorUnimodality.primeAt j : Real)) e (n + 1))
    (normalizedPrimePrefixDefect e v n) hC0 (by linarith only [hC])
    (prime_prefix_transport_nonneg e n)
    (prime_prefix_transport_le_four_mul_cost e t n C ht hC0 hC hcost) hb.1 hb.2

end PrimeFactorOscillations.PrimeProfileRigidity

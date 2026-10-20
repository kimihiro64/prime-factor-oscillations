/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/

import PrimeFactorOscillations.Helpers.PrimeProfileTransportParity
import PrimeFactorOscillations.Mathlib.Analysis.SpecialFunctions.Log.CubicReciprocalTransport

/-!
# Two-moment compensation and cubic-accuracy prime transport readout

The first two finite reciprocal moments recover the same exact signed
transport as every localized logarithmic probe, with a one-sided cubic
error. The finite readout threshold allows cost budgets of order p^(2/3).
No analytic zero-free boundary or prime-pattern infinitude is asserted.
-/

set_option autoImplicit false
set_option Elab.async false

noncomputable section

namespace PrimeFactorOscillations.PrimeProfileRigidity

/-- Compensation of the first two reciprocal probability powers. -/
def cubicPrimePrefixTransport (e : Equiv.Perm Nat) (n : Nat) : Real :=
  Finset.prefixDefect
    (fun j => Real.cubicReciprocalTransport
      (PrimeFactorUnimodality.primeAt n : Real)
      (PrimeFactorUnimodality.primeAt j : Real)) e (n + 1)

/-- The observable uses only the two indicated finite power sums. -/
theorem cubicPrimePrefixTransport_eq_moment_compensation
    (e : Equiv.Perm Nat) (n : Nat) :
    cubicPrimePrefixTransport e n =
      -3 * (PrimeFactorUnimodality.primeAt n : Real) ^ 2 *
        Finset.prefixDefect (fun j => 1 / (PrimeFactorUnimodality.primeAt j : Real))
          e (n + 1) +
      (PrimeFactorUnimodality.primeAt n : Real) ^ 3 *
        Finset.prefixDefect (fun j => 1 / (PrimeFactorUnimodality.primeAt j : Real) ^ 2)
          e (n + 1) := by
  unfold cubicPrimePrefixTransport
  simp only [Finset.prefixDefect, Real.cubicReciprocalTransport, div_eq_mul_inv,
    one_mul, Finset.sum_add_distrib, <- Finset.mul_sum]
  ring

/-- Compare the complete signed transport before estimating its remainder. -/
theorem cubicPrimePrefixTransport_bounds_of_cost_le
    (e : Equiv.Perm Nat) (t : Nat -> Real) (n : Nat) (C : Real)
    (ht : 0 < t n) (hC0 : 0 <= C)
    (hC : C < (PrimeFactorUnimodality.primeAt n : Real) / 4)
    (hcost : normalizedPrimePrefixDefect e t n <= C) :
    (1 - 16 * C ^ 2 / (PrimeFactorUnimodality.primeAt n : Real) ^ 2) *
        Finset.prefixDefect (fun j => (PrimeFactorUnimodality.primeAt j : Real))
          e (n + 1) <= cubicPrimePrefixTransport e n /\
      cubicPrimePrefixTransport e n <=
        Finset.prefixDefect (fun j => (PrimeFactorUnimodality.primeAt j : Real))
          e (n + 1) := by
  let p : Nat -> Real := fun j => PrimeFactorUnimodality.primeAt j
  let r : Real := p n
  let g : Nat -> Real := fun j => Real.cubicReciprocalTransport r (p j)
  let s := (Finset.range (n + 1)).image e
  let u := Finset.range (n + 1)
  have hc : s.card = u.card := Finset.card_image_iff.mpr
    (fun _ _ _ _ h => e.injective h)
  have hr : 0 < r := by
    dsimp only [r, p]
    exact_mod_cast (PrimeFactorUnimodality.prime_primeAt n).pos
  have hmono : Monotone p := by
    intro i j hij
    dsimp only [p]
    exact_mod_cast PrimeFactorUnimodality.primeAt_strictMono.monotone hij
  have hlocal := prime_prefix_coordinates_localized_of_cost_le e t n C ht hC hcost
  have hin : forall j, Membership.mem (s \ u) j ->
      (1 - 16 * C ^ 2 / r ^ 2) * (p j - r) <= g j - g n /\
        g j - g n <= 1 * (p j - r) := by
    intro j hj
    have hn := (Finset.mem_sdiff.mp hj).2
    change Not (Membership.mem (Finset.range (n + 1)) j) at hn
    rw [Finset.mem_range] at hn
    have hidx : n <= j := by omega
    have hb := Real.cubicReciprocalTransport_entering_bounds r (p j) C hr hC0
      (hmono hidx) (hlocal.1 j hj)
    exact And.intro hb.1 (by simpa only [one_mul] using hb.2)
  have hout : forall j, Membership.mem (u \ s) j ->
      (1 - 16 * C ^ 2 / r ^ 2) * (r - p j) <= g n - g j /\
        g n - g j <= 1 * (r - p j) := by
    intro j hj
    have hn := (Finset.mem_sdiff.mp hj).1
    change Membership.mem (Finset.range (n + 1)) j at hn
    rw [Finset.mem_range] at hn
    have hidx : j <= n := by omega
    have hb := Real.cubicReciprocalTransport_leaving_bounds r (p j) C hr hC0
      (hmono hidx) (hlocal.2 j hj) (by linarith only [hC])
    exact And.intro hb.1 (by simpa only [one_mul] using hb.2)
  have hb := Finset.reference_transport_comparison s u p g r (g n)
    (1 - 16 * C ^ 2 / r ^ 2) 1 hc hin hout
  have hf : s.sum p - u.sum p = Finset.prefixDefect p e (n + 1) := by
    dsimp only [s, u]
    rw [Finset.sum_image (fun _ _ _ _ h => e.injective h)]
    rfl
  have hg : s.sum g - u.sum g = cubicPrimePrefixTransport e n := by
    dsimp only [s, u]
    rw [Finset.sum_image (fun _ _ _ _ h => e.injective h)]
    rfl
  rw [hf, hg, one_mul] at hb
  exact hb

/-- Cubic accuracy follows from localization at one arbitrary positive probe. -/
theorem cubicPrimePrefixTransport_error_of_cost_le
    (e : Equiv.Perm Nat) (t : Nat -> Real) (n : Nat) (C : Real)
    (ht : 0 < t n) (hC0 : 0 <= C)
    (hC : C < (PrimeFactorUnimodality.primeAt n : Real) / 4)
    (hcost : normalizedPrimePrefixDefect e t n <= C) :
    0 <= Finset.prefixDefect (fun j => (PrimeFactorUnimodality.primeAt j : Real))
        e (n + 1) - cubicPrimePrefixTransport e n /\
      Finset.prefixDefect (fun j => (PrimeFactorUnimodality.primeAt j : Real))
        e (n + 1) - cubicPrimePrefixTransport e n <=
          64 * C ^ 3 / (PrimeFactorUnimodality.primeAt n : Real) ^ 2 := by
  let r : Real := PrimeFactorUnimodality.primeAt n
  let S : Real := Finset.prefixDefect
    (fun j => (PrimeFactorUnimodality.primeAt j : Real)) e (n + 1)
  have hr : 0 < r := by
    dsimp only [r]
    exact_mod_cast (PrimeFactorUnimodality.prime_primeAt n).pos
  have hb := cubicPrimePrefixTransport_bounds_of_cost_le e t n C ht hC0 hC hcost
  have hSC : S <= 4 * C := prime_prefix_transport_le_four_mul_cost e t n C ht hC0 hC hcost
  have hm := mul_le_mul_of_nonneg_left hSC
    (by positivity : 0 <= 16 * C ^ 2 / r ^ 2)
  have heq : 16 * C ^ 2 / r ^ 2 * (4 * C) = 64 * C ^ 3 / r ^ 2 := by ring
  rw [heq] at hm
  refine And.intro (sub_nonneg.mpr hb.2) ?_
  have hlo : (1 - 16 * C ^ 2 / r ^ 2) * S <= cubicPrimePrefixTransport e n := hb.1
  nlinarith only [hlo, hm]

/-- Two reciprocal moments identify the exact even transport throughout the
larger finite-accuracy range 32*C^3 < p_n^2. -/
theorem cubicPrimePrefixTransport_exact_even_readout
    (e : Equiv.Perm Nat) (t : Nat -> Real) (n : Nat) (C : Real)
    (ht : 0 < t n) (hC0 : 0 <= C)
    (hp3 : (3 : Real) <= PrimeFactorUnimodality.primeAt n)
    (hprecision : 32 * C ^ 3 < (PrimeFactorUnimodality.primeAt n : Real) ^ 2)
    (hcost : normalizedPrimePrefixDefect e t n <= C) :
    exists K : Nat,
      Finset.prefixDefect (fun j => (PrimeFactorUnimodality.primeAt j : Real))
        e (n + 1) = 2 * (K : Real) /\
      (0 <= 2 * (K : Real) - cubicPrimePrefixTransport e n /\
        2 * (K : Real) - cubicPrimePrefixTransport e n < 2) /\
      (forall j : Nat, 0 <= 2 * (j : Real) - cubicPrimePrefixTransport e n ->
        2 * (j : Real) - cubicPrimePrefixTransport e n < 2 -> j = K) := by
  let r : Real := PrimeFactorUnimodality.primeAt n
  have hr3 : 3 <= r := hp3
  have hr : 0 < r := by linarith only [hr3]
  have hprec : 32 * C ^ 3 < r ^ 2 := hprecision
  have hbudget : C < r / 4 := by
    by_contra hn
    have hCp : 0 <= 4 * C - r := by linarith only [le_of_not_gt hn]
    have hprod := mul_nonneg hCp
      (by positivity : 0 <= 16 * C ^ 2 + 4 * C * r + r ^ 2)
    have hcube := mul_nonneg (sq_nonneg r)
      (by linarith only [hr3] : 0 <= r - 2)
    nlinarith only [hprod, hcube, hprec]
  have hsmall : 2 < r - C := by linarith only [hbudget, hr3]
  have heven := prime_prefix_transport_even_of_cost_le e t n C ht hC0
    hbudget hcost hsmall
  let K := Classical.choose heven
  have hK : Finset.prefixDefect (fun j => (PrimeFactorUnimodality.primeAt j : Real))
      e (n + 1) = 2 * (K : Real) := Classical.choose_spec heven
  have hcancel : 64 * C ^ 3 / r ^ 2 * r ^ 2 = 64 * C ^ 3 := by
    field_simp [hr.ne']
  have herr : 64 * C ^ 3 / r ^ 2 < 2 := by
    by_contra hn
    have hm := mul_le_mul_of_nonneg_right (le_of_not_gt hn) (sq_nonneg r)
    rw [hcancel] at hm
    nlinarith only [hm, hprec]
  have he := cubicPrimePrefixTransport_error_of_cost_le e t n C ht hC0 hbudget hcost
  rw [hK] at he
  have hread : 0 <= 2 * (K : Real) - cubicPrimePrefixTransport e n /\
      2 * (K : Real) - cubicPrimePrefixTransport e n < 2 :=
    And.intro he.1 (he.2.trans_lt herr)
  refine Exists.intro K (And.intro hK (And.intro hread ?_))
  intro j hj0 hj2
  have hjK : (j : Real) < (K : Real) + 1 := by linarith only [hj2, hread.1]
  have hKj : (K : Real) < (j : Real) + 1 := by linarith only [hread.2, hj0]
  have hjKn : j < K + 1 := by exact_mod_cast hjK
  have hKjn : K < j + 1 := by exact_mod_cast hKj
  omega

end PrimeFactorOscillations.PrimeProfileRigidity

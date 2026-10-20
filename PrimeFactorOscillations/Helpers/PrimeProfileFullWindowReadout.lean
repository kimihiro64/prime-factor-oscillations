/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/

import PrimeFactorOscillations.Helpers.PrimeProfileMomentReadout
import PrimeFactorOscillations.Mathlib.Analysis.SpecialFunctions.Log.ReciprocalMomentWindow

/-!
# Uniform moment readout throughout the full localization window

The actual coordinate denominators give a half ratio for every budget
C<p_n/4. The complete signed error is at most S/2^m, independently of
how closely the budget approaches the localization endpoint.
-/

set_option autoImplicit false
set_option Elab.async false

noncomputable section

namespace PrimeFactorOscillations.PrimeProfileRigidity

/-- Retain the full transport with a uniform half-ratio comparison. -/
theorem primePrefixMomentTransport_half_window_bounds
    (e : Equiv.Perm Nat) (t : Nat -> Real) (n k : Nat) (C : Real)
    (ht : 0 < t n) (hC0 : 0 <= C)
    (hC : C < (PrimeFactorUnimodality.primeAt n : Real) / 4)
    (hcost : normalizedPrimePrefixDefect e t n <= C) :
    (1 - (1 / 2 : Real) ^ (2 * k)) *
        Finset.prefixDefect (fun j => (PrimeFactorUnimodality.primeAt j : Real))
          e (n + 1) <= primePrefixMomentTransport (2 * k) e n /\
      primePrefixMomentTransport (2 * k) e n <=
        Finset.prefixDefect (fun j => (PrimeFactorUnimodality.primeAt j : Real))
          e (n + 1) := by
  let p : Nat -> Real := fun j => PrimeFactorUnimodality.primeAt j
  let r : Real := p n
  let g : Nat -> Real := fun j => Real.reciprocalMomentTransport (2 * k) r (p j)
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
      (1 - (1 / 2 : Real) ^ (2 * k)) * (p j - r) <= g j - 0 /\
        g j - 0 <= 1 * (p j - r) := by
    intro j hj
    have hn := (Finset.mem_sdiff.mp hj).2
    change Not (Membership.mem (Finset.range (n + 1)) j) at hn
    rw [Finset.mem_range] at hn
    have hidx : n <= j := by omega
    have hgap : p j - r <= 4 * C := hlocal.1 j hj
    have hb := Real.reciprocalMomentTransport_entering_half_window_bounds
      (2 * k) r (p j) hr (hmono hidx) (by linarith only [hgap, hbudget])
    simpa only [sub_zero, one_mul] using hb
  have hout : forall j, Membership.mem (u \ s) j ->
      (1 - (1 / 2 : Real) ^ (2 * k)) * (r - p j) <= 0 - g j /\
        0 - g j <= 1 * (r - p j) := by
    intro j hj
    have hn := (Finset.mem_sdiff.mp hj).1
    change Membership.mem (Finset.range (n + 1)) j at hn
    rw [Finset.mem_range] at hn
    have hidx : j <= n := by omega
    have hgap : r - p j <= C := hlocal.2 j hj
    have hp : 0 < p j := by linarith only [hgap, hbudget, hr]
    have hb := Real.reciprocalMomentTransport_leaving_half_window_bounds
      k r (p j) hp (hmono hidx) (by linarith only [hgap, hbudget, hr])
    simpa only [zero_sub, one_mul] using hb
  have hb := Finset.reference_transport_comparison s u p g r 0
    (1 - (1 / 2 : Real) ^ (2 * k)) 1 hc hin hout
  have hf : s.sum p - u.sum p = Finset.prefixDefect p e (n + 1) := by
    dsimp only [s, u]
    rw [Finset.sum_image (fun _ _ _ _ h => e.injective h)]
    rfl
  have hg : s.sum g - u.sum g = primePrefixMomentTransport (2 * k) e n := by
    dsimp only [s, u]
    rw [Finset.sum_image (fun _ _ _ _ h => e.injective h)]
    rfl
  rw [hf, hg, one_mul] at hb
  exact hb

/-- The geometric error is uniform over the complete quarter-budget domain. -/
theorem primePrefixMomentTransport_half_window_error
    (e : Equiv.Perm Nat) (t : Nat -> Real) (n k : Nat) (C : Real)
    (ht : 0 < t n) (hC0 : 0 <= C)
    (hC : C < (PrimeFactorUnimodality.primeAt n : Real) / 4)
    (hcost : normalizedPrimePrefixDefect e t n <= C) :
    0 <= Finset.prefixDefect (fun j => (PrimeFactorUnimodality.primeAt j : Real))
        e (n + 1) - primePrefixMomentTransport (2 * k) e n /\
      (Finset.prefixDefect (fun j => (PrimeFactorUnimodality.primeAt j : Real))
        e (n + 1) - primePrefixMomentTransport (2 * k) e n <=
          (1 / 2 : Real) ^ (2 * k) *
            Finset.prefixDefect (fun j => (PrimeFactorUnimodality.primeAt j : Real))
              e (n + 1)) /\
      (Finset.prefixDefect (fun j => (PrimeFactorUnimodality.primeAt j : Real))
        e (n + 1) - primePrefixMomentTransport (2 * k) e n <=
          4 * C * (1 / 2 : Real) ^ (2 * k)) := by
  let S : Real := Finset.prefixDefect
    (fun j => (PrimeFactorUnimodality.primeAt j : Real)) e (n + 1)
  have hb := primePrefixMomentTransport_half_window_bounds e t n k C ht hC0 hC hcost
  have hSC : S <= 4 * C := prime_prefix_transport_le_four_mul_cost e t n C ht hC0 hC hcost
  have hm := mul_le_mul_of_nonneg_left hSC
    (by positivity : 0 <= (1 / 2 : Real) ^ (2 * k))
  have hlo : (1 - (1 / 2 : Real) ^ (2 * k)) * S <=
      primePrefixMomentTransport (2 * k) e n := hb.1
  refine And.intro (sub_nonneg.mpr hb.2) (And.intro ?_ ?_)
  . nlinarith only [hlo]
  . nlinarith only [hlo, hm]

/-- The same fixed observation-noise allowance holds for every localized budget.
The explicit logarithmic degree is independent of C within C<p_n/4. -/
theorem primePrefixMomentTransport_full_window_noisy_readout
    (e : Equiv.Perm Nat) (t : Nat -> Real) (n : Nat) (C : Real)
    (ht : 0 < t n) (hC0 : 0 <= C)
    (hp3 : (3 : Real) <= PrimeFactorUnimodality.primeAt n)
    (hC : C < (PrimeFactorUnimodality.primeAt n : Real) / 4)
    (hcost : normalizedPrimePrefixDefect e t n <= C) :
    let m : Nat := 2 * (Nat.log 4 (2 * PrimeFactorUnimodality.primeAt n) + 1)
    exists K : Nat,
      Finset.prefixDefect (fun j => (PrimeFactorUnimodality.primeAt j : Real))
        e (n + 1) = 2 * (K : Real) /\
      (forall y : Real, abs (y - primePrefixMomentTransport m e n) < (1 / 2 : Real) ->
        abs (y - 2 * (K : Real)) < 1 /\
        (forall j : Nat, abs (y - 2 * (j : Real)) < 1 -> j = K)) := by
  let r : Real := PrimeFactorUnimodality.primeAt n
  let k : Nat := Nat.log 4 (2 * PrimeFactorUnimodality.primeAt n) + 1
  have hr3 : 3 <= r := hp3
  have hbudget : 4 * C < r := by linarith only [hC]
  have hsmall : 2 < r - C := by linarith only [hC, hr3]
  have heven := prime_prefix_transport_even_of_cost_le e t n C
    ht hC0 hC hcost hsmall
  let K := Classical.choose heven
  have hK : Finset.prefixDefect (fun j => (PrimeFactorUnimodality.primeAt j : Real))
      e (n + 1) = 2 * (K : Real) := Classical.choose_spec heven
  have hdNat : 2 * PrimeFactorUnimodality.primeAt n <
      4 ^ (Nat.log 4 (2 * PrimeFactorUnimodality.primeAt n) + 1) :=
    Nat.lt_pow_succ_log_self (by decide) (2 * PrimeFactorUnimodality.primeAt n)
  have hd : 2 * r < (4 : Real) ^ k := by
    dsimp only [r, k]
    exact_mod_cast hdNat
  have hpower : (1 / 2 : Real) ^ (2 * k) * (4 : Real) ^ k = 1 := by
    rw [pow_mul, <- mul_pow]
    norm_num
  have hcancel : (4 * C * (1 / 2 : Real) ^ (2 * k)) * (4 : Real) ^ k = 4 * C := by
    calc
      _ = 4 * C * ((1 / 2 : Real) ^ (2 * k) * (4 : Real) ^ k) := by ring
      _ = _ := by rw [hpower, mul_one]
  have hprecision : 4 * C * (1 / 2 : Real) ^ (2 * k) < (1 / 2 : Real) := by
    by_contra hn
    have hm := mul_le_mul_of_nonneg_right (le_of_not_gt hn)
      (by positivity : 0 <= (4 : Real) ^ k)
    rw [hcancel] at hm
    linarith only [hm, hd, hbudget]
  have he := primePrefixMomentTransport_half_window_error e t n k C ht hC0 hC hcost
  rw [hK] at he
  have herror : 2 * (K : Real) - primePrefixMomentTransport (2 * k) e n < (1 / 2 : Real) :=
    he.2.2.trans_lt hprecision
  refine Exists.intro K (And.intro hK ?_)
  intro y hy
  change abs (y - primePrefixMomentTransport (2 * k) e n) < (1 / 2 : Real) at hy
  have hybounds := abs_lt.mp hy
  have hread : abs (y - 2 * (K : Real)) < 1 := by
    apply abs_lt.mpr
    constructor <;> linarith only [hybounds.1, hybounds.2, he.1, herror]
  refine And.intro hread ?_
  intro j hj
  have hKb := abs_lt.mp hread
  have hjb := abs_lt.mp hj
  have hjK : (j : Real) < (K : Real) + 1 := by linarith only [hjb.1, hKb.2]
  have hKj : (K : Real) < (j : Real) + 1 := by linarith only [hKb.1, hjb.2]
  have hjKn : j < K + 1 := by exact_mod_cast hjK
  have hKjn : K < j + 1 := by exact_mod_cast hKj
  omega

end PrimeFactorOscillations.PrimeProfileRigidity

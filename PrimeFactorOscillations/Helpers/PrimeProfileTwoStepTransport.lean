/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/

import PrimeFactorOscillations.Helpers.PrimeQuadrupletSupport

/-!
# Uniform cutoff costs for short-quadruplet transport

Only the two active distance-two edges remain after exact signed cancellation.
Their combined upper envelope tends to twelve independently of the probe.
-/

set_option autoImplicit false
set_option Elab.async false

noncomputable section

attribute [local instance] Classical.propDecidable

open Filter
open scoped Topology

namespace PrimeFactorOscillations.PrimeProfileRigidity

theorem normalized_twoStepSwap_cost_le (B : Set Nat)
    (hB : forall n, Membership.mem B n -> Not (Membership.mem B (n + 2)))
    (hgap : forall n, Membership.mem B n ->
      PrimeFactorUnimodality.primeAt (n + 2) = PrimeFactorUnimodality.primeAt n + 6)
    (t : Nat -> Real) (k : Nat) (ht : 0 < t (k + 1)) :
    normalizedPrimePrefixDefect (Finset.twoStepSwapPerm B hB) t (k + 1) <=
      6 * ((PrimeFactorUnimodality.primeAt (k + 1) : Real) /
        PrimeFactorUnimodality.primeAt k) ^ 2 + 6 := by
  let p : Nat -> Real := fun i => PrimeFactorUnimodality.primeAt i
  have hp : forall i, 0 < p i := by
    intro i
    dsimp only [p]
    exact_mod_cast (PrimeFactorUnimodality.prime_primeAt i).pos
  have hmono : Monotone p := by
    intro i j hij
    dsimp only [p]
    exact_mod_cast PrimeFactorUnimodality.primeAt_strictMono.monotone hij
  let c : Real := p (k + 1) ^ 2 * (p (k + 1) + t (k + 1)) / t (k + 1) ^ 2
  have hfirst : c * (if Membership.mem B (k + 1) then
      primeLogWeight (t (k + 1)) (k + 3) -
        primeLogWeight (t (k + 1)) (k + 1) else 0) <= 6 := by
    by_cases hk : Membership.mem B (k + 1)
    . rw [ite_eq_left hk]
      have hb := Real.normalized_pairLogDefect_le_gap_mul_reference_ratio_sq
        (t (k + 1)) (p (k + 1)) (p (k + 3)) (p (k + 1))
        ht (hp _) (hmono (by omega)) le_rfl (hmono (by omega))
      have hg : p (k + 3) - p (k + 1) = 6 := by
        have he := hgap (k + 1) hk
        have hi : k + 1 + 2 = k + 3 := by omega
        rw [hi] at he
        have hc : p (k + 3) = p (k + 1) + 6 := by
          dsimp only [p]
          exact_mod_cast he
        linarith only [hc]
      rw [hg, div_self (hp _).ne'] at hb
      simpa only [one_pow, mul_one, c, p, Real.pairLogDefect, primeLogWeight] using hb
    . rw [ite_eq_right hk, mul_zero]
      norm_num
  have hsecond : c * (if Membership.mem B k then
      primeLogWeight (t (k + 1)) (k + 2) -
        primeLogWeight (t (k + 1)) k else 0) <=
      6 * (p (k + 1) / p k) ^ 2 := by
    by_cases hk : Membership.mem B k
    . rw [ite_eq_left hk]
      have hb := Real.normalized_pairLogDefect_le_gap_mul_reference_ratio_sq
        (t (k + 1)) (p k) (p (k + 2)) (p (k + 1))
        ht (hp _) (hmono (by omega)) (hmono (by omega)) (hmono (by omega))
      have hg : p (k + 2) - p k = 6 := by
        have hc : p (k + 2) = p k + 6 := by
          dsimp only [p]
          exact_mod_cast hgap k hk
        linarith only [hc]
      rw [hg] at hb
      exact hb
    . rw [ite_eq_right hk, mul_zero]
      positivity
  unfold normalizedPrimePrefixDefect
  have hi : k + 1 + 1 = k + 2 := by omega
  rw [hi, Finset.prefixDefect_twoStepSwapPerm, mul_add]
  change c * _ + c * _ <= 6 * (p (k + 1) / p k) ^ 2 + 6
  linarith only [hfirst, hsecond]

theorem eventual_uniform_twoStepSwap_cost_le (B : Set Nat)
    (hB : forall n, Membership.mem B n -> Not (Membership.mem B (n + 2)))
    (hgap : forall n, Membership.mem B n ->
      PrimeFactorUnimodality.primeAt (n + 2) = PrimeFactorUnimodality.primeAt n + 6)
    (eps : Real) (heps : 0 < eps) :
    exists N : Nat, forall k : Nat, N <= k -> forall t : Nat -> Real,
      0 < t (k + 1) ->
      normalizedPrimePrefixDefect (Finset.twoStepSwapPerm B hB) t (k + 1) <= 12 + eps := by
  have hc : Tendsto (fun k : Nat =>
      6 * ((PrimeFactorUnimodality.primeAt (k + 1) : Real) /
        PrimeFactorUnimodality.primeAt k) ^ 2 + 6) atTop (nhds 12) := by
    convert (((tendsto_primeAt_succ_div).pow 2).const_mul (6 : Real)).add
      (tendsto_const_nhds (x := (6 : Real))) using 1
    norm_num
  have hnear := eventually_atTop.mp
    (hc.eventually (gt_mem_nhds (by linarith : (12 : Real) < 12 + eps)))
  let N := Classical.choose hnear
  have hN : forall k : Nat, N <= k ->
      6 * ((PrimeFactorUnimodality.primeAt (k + 1) : Real) /
        PrimeFactorUnimodality.primeAt k) ^ 2 + 6 < 12 + eps :=
    Classical.choose_spec hnear
  exact Exists.intro N (fun k hk t ht =>
    (normalized_twoStepSwap_cost_le B hB hgap t k ht).trans (hN k hk).le)

end PrimeFactorOscillations.PrimeProfileRigidity

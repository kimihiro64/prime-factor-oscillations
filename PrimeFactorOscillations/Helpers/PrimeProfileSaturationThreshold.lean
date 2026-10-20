/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/

import PrimeFactorOscillations.Helpers.PrimeProfileCostLocalization
import PrimeFactorOscillations.Mathlib.Analysis.SpecialFunctions.Log.CompensatedReciprocalSaturation
import PrimeFactorOscillations.Mathlib.Combinatorics.FinitePrefixTransposition

/-!
# The exact fixed-probe locality threshold of a prime-prefix profile

Every budget strictly below the scalar saturation confines all possible
prefix images to one finite set. At saturation, single finite transpositions
already have unbounded entering coordinates and unbounded full displacement.
-/

set_option autoImplicit false
set_option Elab.async false

noncomputable section

namespace PrimeFactorOscillations.PrimeProfileRigidity

/-- A subcritical full signed cost gives an explicit quadratic bound on every entry. -/
theorem prime_prefix_fixed_probe_incoming_bound
    (e : Equiv.Perm Nat) (t : Real) (n : Nat) (C : Real) (ht : 0 < t)
    (hC : C < Real.normalizedLogBoundarySaturation t (PrimeFactorUnimodality.primeAt n : Real))
    (hcost : normalizedPrimePrefixDefect e (fun _ => t) n <= C) :
    forall j, Membership.mem
      ((Finset.range (n + 1)).image e \ Finset.range (n + 1)) j ->
      (Real.normalizedLogBoundarySaturation t (PrimeFactorUnimodality.primeAt n : Real) - C) *
        (PrimeFactorUnimodality.primeAt j : Real) *
          ((PrimeFactorUnimodality.primeAt j : Real) + t) <=
            (PrimeFactorUnimodality.primeAt n : Real) ^ 2 *
              ((PrimeFactorUnimodality.primeAt n : Real) + t) := by
  intro j hj
  have hcostj := ((normalized_reference_costs_le_prefixDefect e (fun _ => t) n ht).1 j hj).trans hcost
  have hr : (0 : Real) < PrimeFactorUnimodality.primeAt n := by
    exact_mod_cast (PrimeFactorUnimodality.prime_primeAt n).pos
  have hq : (0 : Real) < PrimeFactorUnimodality.primeAt j := by
    exact_mod_cast (PrimeFactorUnimodality.prime_primeAt j).pos
  exact Real.incoming_coordinate_bound_of_cost_lt_saturation t _ _ C ht hr hq hC hcostj

/-- One finite ambient prefix contains every image allowed below saturation. -/
theorem prime_prefix_fixed_probe_bounded_support (t : Real) (n : Nat) (C : Real)
    (ht : 0 < t)
    (hC : C < Real.normalizedLogBoundarySaturation t (PrimeFactorUnimodality.primeAt n : Real)) :
    exists M : Nat, forall e : Equiv.Perm Nat,
      normalizedPrimePrefixDefect e (fun _ => t) n <= C ->
      forall j, Membership.mem ((Finset.range (n + 1)).image e) j ->
        Membership.mem (Finset.range M) j := by
  let r : Real := PrimeFactorUnimodality.primeAt n
  let delta : Real := Real.normalizedLogBoundarySaturation t r - C
  let A : Real := r ^ 2 * (r + t)
  have hdelta : 0 < delta := sub_pos.mpr hC
  have hM : exists M : Nat, max ((n + 1 : Nat) : Real) (A / delta) < (M : Real) :=
    exists_nat_gt _
  let M := Classical.choose hM
  have hMgt : max ((n + 1 : Nat) : Real) (A / delta) < (M : Real) :=
    Classical.choose_spec hM
  have hnMreal : ((n + 1 : Nat) : Real) < (M : Real) :=
    (le_max_left _ _).trans_lt hMgt
  have hnM : n + 1 < M := by exact_mod_cast hnMreal
  refine Exists.intro M ?_
  intro e he j hj
  by_cases hjlow : Membership.mem (Finset.range (n + 1)) j
  . exact Finset.mem_range.mpr ((Finset.mem_range.mp hjlow).trans hnM)
  . have hjin : Membership.mem
        ((Finset.range (n + 1)).image e \ Finset.range (n + 1)) j :=
      Finset.mem_sdiff.mpr (And.intro hj hjlow)
    have hbound := prime_prefix_fixed_probe_incoming_bound e t n C ht hC he j hjin
    let q : Real := PrimeFactorUnimodality.primeAt j
    have hq2 : (2 : Real) <= q := by
      dsimp only [q]
      exact_mod_cast (PrimeFactorUnimodality.prime_primeAt j).two_le
    have hq : 0 < q := by linarith only [hq2]
    have hqt : 1 <= q + t := by linarith only [hq2, ht]
    have hmul := mul_le_mul_of_nonneg_left hqt (mul_nonneg hdelta.le hq.le)
    have hprod : delta * q * (q + t) <= A := hbound
    have hsmall : delta * q <= A := by nlinarith only [hmul, hprod]
    have hscale := mul_le_mul_of_nonneg_right hsmall
      (by positivity : 0 <= 1 / delta)
    have hid : (delta * q) * (1 / delta) = q := by field_simp [hdelta.ne']
    rw [hid] at hscale
    have hqle : q <= A / delta := by simpa only [mul_one_div] using hscale
    have hjq : (j : Real) <= q := by
      dsimp only [q]
      exact_mod_cast PrimeFactorUnimodality.primeAt_strictMono.id_le j
    have hjMreal : (j : Real) < (M : Real) :=
      (hjq.trans hqle).trans_lt ((le_max_right _ _).trans_lt hMgt)
    exact Finset.mem_range.mpr (by exact_mod_cast hjMreal)

/-- The exact full normalized cost of a crossing transposition. -/
theorem prime_prefix_swap_fixed_probe_cost (t : Real) (n j : Nat) (hnj : n < j) :
    normalizedPrimePrefixDefect (Equiv.swap n j) (fun _ => t) n =
      (PrimeFactorUnimodality.primeAt n : Real) ^ 2 *
        ((PrimeFactorUnimodality.primeAt n : Real) + t) / t ^ 2 *
          Real.pairLogDefect t (PrimeFactorUnimodality.primeAt n : Real)
            (PrimeFactorUnimodality.primeAt j : Real) := by
  unfold normalizedPrimePrefixDefect
  rw [Finset.prefixDefect_swap_of_crossing (primeLogWeight t) n j (n + 1)
    (Nat.lt_succ_self n) (by omega)]
  rfl

/-- With the same positive probe, finite swaps have arbitrarily large displacement below saturation. -/
theorem prime_prefix_fixed_probe_unbounded_swaps (t : Real) (n : Nat) (ht : 0 < t)
    (B : Real) (M : Nat) :
    exists j : Nat, max n M < j /\
      B < Finset.prefixDefect (fun i => (PrimeFactorUnimodality.primeAt i : Real))
        (Equiv.swap n j) (n + 1) /\
      normalizedPrimePrefixDefect (Equiv.swap n j) (fun _ => t) n <
        Real.normalizedLogBoundarySaturation t (PrimeFactorUnimodality.primeAt n : Real) := by
  let r : Real := PrimeFactorUnimodality.primeAt n
  have hQ : exists Q : Nat, B + r < (Q : Real) := exists_nat_gt _
  let Q := Classical.choose hQ
  have hQgt : B + r < (Q : Real) := Classical.choose_spec hQ
  let j : Nat := Q + n + M + 1
  have hj : max n M < j := by dsimp only [j]; omega
  have hnj : n < j := (le_max_left n M).trans_lt hj
  have hQj : (Q : Real) <= (j : Real) := by
    exact_mod_cast (show Q <= j by dsimp only [j]; omega)
  have hjq : (j : Real) <= (PrimeFactorUnimodality.primeAt j : Real) := by
    exact_mod_cast PrimeFactorUnimodality.primeAt_strictMono.id_le j
  have hS := Finset.prefixDefect_swap_of_crossing
    (fun i => (PrimeFactorUnimodality.primeAt i : Real)) n j (n + 1)
    (Nat.lt_succ_self n) (by omega)
  have hr : 0 < r := by
    dsimp only [r]
    exact_mod_cast (PrimeFactorUnimodality.prime_primeAt n).pos
  have hq : (0 : Real) < PrimeFactorUnimodality.primeAt j := by
    exact_mod_cast (PrimeFactorUnimodality.prime_primeAt j).pos
  refine Exists.intro j (And.intro hj (And.intro ?_ ?_))
  . rw [hS]
    change B < (PrimeFactorUnimodality.primeAt j : Real) - r
    linarith only [hQgt, hQj, hjq]
  . rw [prime_prefix_swap_fixed_probe_cost t n j hnj]
    exact sub_pos.mp (Real.normalizedLogBoundarySaturation_residual_bounds
      t r (PrimeFactorUnimodality.primeAt j : Real) ht hr hq).1

/-- The scalar saturation is exactly the boundary for uniform finite prefix localization. -/
theorem prime_prefix_fixed_probe_locality_iff (t : Real) (n : Nat) (C : Real) (ht : 0 < t) :
    (exists M : Nat, forall e : Equiv.Perm Nat,
      normalizedPrimePrefixDefect e (fun _ => t) n <= C ->
      forall j, Membership.mem ((Finset.range (n + 1)).image e) j ->
        Membership.mem (Finset.range M) j) <->
    C < Real.normalizedLogBoundarySaturation t (PrimeFactorUnimodality.primeAt n : Real) := by
  constructor
  . intro h
    let M := Classical.choose h
    have hcover := Classical.choose_spec h
    by_contra hn
    have hKC : Real.normalizedLogBoundarySaturation t
        (PrimeFactorUnimodality.primeAt n : Real) <= C := le_of_not_gt hn
    have hj := prime_prefix_fixed_probe_unbounded_swaps t n ht 0 M
    let j := Classical.choose hj
    have hjinfo := Classical.choose_spec hj
    have hnj : n < j := (le_max_left n M).trans_lt hjinfo.1
    have hcost : normalizedPrimePrefixDefect (Equiv.swap n j) (fun _ => t) n <= C :=
      hjinfo.2.2.le.trans hKC
    have hmem : Membership.mem ((Finset.range (n + 1)).image (Equiv.swap n j)) j :=
      Finset.mem_image.mpr (Exists.intro n
        (And.intro (Finset.mem_range.mpr (Nat.lt_succ_self n)) (Equiv.swap_apply_left n j)))
    have hjM := Finset.mem_range.mp (hcover (Equiv.swap n j) hcost j hmem)
    have hMj : M < j := (le_max_right n M).trans_lt hjinfo.1
    omega
  . intro hC
    exact prime_prefix_fixed_probe_bounded_support t n C ht hC

end PrimeFactorOscillations.PrimeProfileRigidity

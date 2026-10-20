/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/

import PrimeFactorOscillations.Helpers.PrimeProfileSaturationThreshold
import PrimeFactorOscillations.Mathlib.Analysis.SpecialFunctions.Log.CompensatedReciprocalUpperCost

/-!
# Sharp locality uniformly over every positive probe

A budget below half the boundary prime confines every admissible prefix image
to a single finite set independently of the positive probe. At the half-prime
budget, explicit positive probes and finite swaps escape every finite set.
-/

set_option autoImplicit false
set_option Elab.async false

noncomputable section

namespace PrimeFactorOscillations.PrimeProfileRigidity

/-- The complete signed cost bounds every entering coordinate independently of the probe. -/
theorem prime_prefix_probe_uniform_incoming_bound
    (e : Equiv.Perm Nat) (t : Real) (n : Nat) (C : Real) (ht : 0 < t)
    (hcost : normalizedPrimePrefixDefect e (fun _ => t) n <= C) :
    forall j, Membership.mem
      ((Finset.range (n + 1)).image e \ Finset.range (n + 1)) j ->
      ((PrimeFactorUnimodality.primeAt n : Real) - 2 * C) *
        (PrimeFactorUnimodality.primeAt j : Real) ^ 2 <=
          (PrimeFactorUnimodality.primeAt n : Real) ^ 3 := by
  intro j hj
  let r : Real := PrimeFactorUnimodality.primeAt n
  let q : Real := PrimeFactorUnimodality.primeAt j
  have hnj : n <= j := by
    have hnot := (Finset.mem_sdiff.mp hj).2
    have hnotlt : Not (j < n + 1) := fun h => hnot (Finset.mem_range.mpr h)
    omega
  have hr : 0 < r := by
    dsimp only [r]
    exact_mod_cast (PrimeFactorUnimodality.prime_primeAt n).pos
  have hq : 0 < q := by
    dsimp only [q]
    exact_mod_cast (PrimeFactorUnimodality.prime_primeAt j).pos
  have hrq : r <= q := by
    dsimp only [r, q]
    exact_mod_cast PrimeFactorUnimodality.primeAt_strictMono.monotone hnj
  have hcostj := ((normalized_reference_costs_le_prefixDefect
    e (fun _ => t) n ht).1 j hj).trans hcost
  have h := (Real.incoming_integrated_normalized_pairLogDefect_lower
    t r q ht hr hrq).trans hcostj
  have hscale := mul_le_mul_of_nonneg_right h (by positivity : 0 <= 2 * q ^ 2)
  have hid : (r / 2 * (1 - (r / q) ^ 2)) * (2 * q ^ 2) =
      r * q ^ 2 - r ^ 3 := by
    field_simp [hq.ne']
  rw [hid] at hscale
  change (r - 2 * C) * q ^ 2 <= r ^ 3
  nlinarith only [hscale]

/-- A single finite ambient prefix works simultaneously for every positive probe. -/
theorem prime_prefix_probe_uniform_bounded_support (n : Nat) (C : Real)
    (hC : C < (PrimeFactorUnimodality.primeAt n : Real) / 2) :
    exists M : Nat, forall t : Real, 0 < t -> forall e : Equiv.Perm Nat,
      normalizedPrimePrefixDefect e (fun _ => t) n <= C ->
      forall j, Membership.mem ((Finset.range (n + 1)).image e) j ->
        Membership.mem (Finset.range M) j := by
  let r : Real := PrimeFactorUnimodality.primeAt n
  let delta : Real := r - 2 * C
  let A : Real := r ^ 3
  have hdelta : 0 < delta := by dsimp only [delta]; linarith only [hC]
  have hM : exists M : Nat, max ((n + 1 : Nat) : Real) (A / delta) < (M : Real) :=
    exists_nat_gt _
  let M := Classical.choose hM
  have hMgt := Classical.choose_spec hM
  have hnMreal : ((n + 1 : Nat) : Real) < (M : Real) :=
    (le_max_left _ _).trans_lt hMgt
  have hnM : n + 1 < M := by exact_mod_cast hnMreal
  refine Exists.intro M ?_
  intro t ht e he j hj
  by_cases hjlow : Membership.mem (Finset.range (n + 1)) j
  . exact Finset.mem_range.mpr ((Finset.mem_range.mp hjlow).trans hnM)
  . have hjin : Membership.mem
        ((Finset.range (n + 1)).image e \ Finset.range (n + 1)) j :=
      Finset.mem_sdiff.mpr (And.intro hj hjlow)
    have hbound := prime_prefix_probe_uniform_incoming_bound e t n C ht he j hjin
    let q : Real := PrimeFactorUnimodality.primeAt j
    have hq2 : (2 : Real) <= q := by
      dsimp only [q]
      exact_mod_cast (PrimeFactorUnimodality.prime_primeAt j).two_le
    have hqle : q <= q ^ 2 := by nlinarith only [hq2]
    have hmul := mul_le_mul_of_nonneg_left hqle hdelta.le
    have hprod : delta * q ^ 2 <= A := hbound
    have hsmall : delta * q <= A := hmul.trans hprod
    have hscale := mul_le_mul_of_nonneg_right hsmall
      (by positivity : 0 <= 1 / delta)
    have hid : (delta * q) * (1 / delta) = q := by field_simp [hdelta.ne']
    rw [hid] at hscale
    have hqbound : q <= A / delta := by simpa only [mul_one_div] using hscale
    have hjq : (j : Real) <= q := by
      dsimp only [q]
      exact_mod_cast PrimeFactorUnimodality.primeAt_strictMono.id_le j
    have hjMreal : (j : Real) < (M : Real) :=
      (hjq.trans hqbound).trans_lt ((le_max_right _ _).trans_lt hMgt)
    exact Finset.mem_range.mpr (by exact_mod_cast hjMreal)

/-- Positive probes and finite swaps have arbitrary displacement below half the reference. -/
theorem prime_prefix_probe_uniform_unbounded_swaps (n : Nat) (B : Real) (M : Nat) :
    exists j : Nat, exists t : Real, max n M < j /\ 0 < t /\
      B < Finset.prefixDefect (fun i => (PrimeFactorUnimodality.primeAt i : Real))
        (Equiv.swap n j) (n + 1) /\
      t = Real.halfReferenceEscapeProbe (PrimeFactorUnimodality.primeAt n : Real)
        (PrimeFactorUnimodality.primeAt j : Real) /\
      normalizedPrimePrefixDefect (Equiv.swap n j) (fun _ => t) n <=
        (PrimeFactorUnimodality.primeAt n : Real) / 2 -
          (PrimeFactorUnimodality.primeAt n : Real) ^ 3 /
            (4 * (PrimeFactorUnimodality.primeAt j : Real) ^ 2) /\
      normalizedPrimePrefixDefect (Equiv.swap n j) (fun _ => t) n <
        (PrimeFactorUnimodality.primeAt n : Real) / 2 := by
  have hj := prime_prefix_fixed_probe_unbounded_swaps 1 n zero_lt_one B M
  let j := Classical.choose hj
  have hjinfo := Classical.choose_spec hj
  have hnj : n < j := (le_max_left n M).trans_lt hjinfo.1
  let r : Real := PrimeFactorUnimodality.primeAt n
  let q : Real := PrimeFactorUnimodality.primeAt j
  let t : Real := Real.halfReferenceEscapeProbe r q
  have hr : 0 < r := by
    dsimp only [r]
    exact_mod_cast (PrimeFactorUnimodality.prime_primeAt n).pos
  have hq : 0 < q := by
    dsimp only [q]
    exact_mod_cast (PrimeFactorUnimodality.prime_primeAt j).pos
  have hrq : r < q := by
    dsimp only [r, q]
    exact_mod_cast PrimeFactorUnimodality.primeAt_strictMono hnj
  have ht : 0 < t := Real.halfReferenceEscapeProbe_pos r q hr hrq
  have hbound : normalizedPrimePrefixDefect (Equiv.swap n j) (fun _ => t) n <=
      r / 2 - r ^ 3 / (4 * q ^ 2) := by
    rw [prime_prefix_swap_fixed_probe_cost t n j hnj]
    exact Real.halfReferenceEscapeProbe_cost_le r q hr hrq
  have hmargin : 0 < r ^ 3 / (4 * q ^ 2) := by positivity
  refine Exists.intro j (Exists.intro t ?_)
  exact And.intro hjinfo.1 (And.intro ht (And.intro hjinfo.2.1
    (And.intro rfl (And.intro hbound (hbound.trans_lt (sub_lt_self _ hmargin))))))

/-- Half the boundary prime is exactly the locality threshold uniform in all positive probes. -/
theorem prime_prefix_probe_uniform_locality_iff (n : Nat) (C : Real) :
    (exists M : Nat, forall t : Real, 0 < t -> forall e : Equiv.Perm Nat,
      normalizedPrimePrefixDefect e (fun _ => t) n <= C ->
      forall j, Membership.mem ((Finset.range (n + 1)).image e) j ->
        Membership.mem (Finset.range M) j) <->
    C < (PrimeFactorUnimodality.primeAt n : Real) / 2 := by
  constructor
  . intro h
    let M := Classical.choose h
    have hcover := Classical.choose_spec h
    by_contra hn
    have hhalf : (PrimeFactorUnimodality.primeAt n : Real) / 2 <= C := le_of_not_gt hn
    have hj := prime_prefix_probe_uniform_unbounded_swaps n 0 M
    let j := Classical.choose hj
    have htinfo := Classical.choose_spec hj
    let t := Classical.choose htinfo
    have hw := Classical.choose_spec htinfo
    have hcost : normalizedPrimePrefixDefect (Equiv.swap n j) (fun _ => t) n <= C :=
      hw.2.2.2.2.2.le.trans hhalf
    have hmem : Membership.mem ((Finset.range (n + 1)).image (Equiv.swap n j)) j :=
      Finset.mem_image.mpr (Exists.intro n
        (And.intro (Finset.mem_range.mpr (Nat.lt_succ_self n)) (Equiv.swap_apply_left n j)))
    have hjM := Finset.mem_range.mp (hcover t hw.2.1 (Equiv.swap n j) hcost j hmem)
    have hMj : M < j := (le_max_right n M).trans_lt hw.1
    omega
  . intro hC
    exact prime_prefix_probe_uniform_bounded_support n C hC

end PrimeFactorOscillations.PrimeProfileRigidity

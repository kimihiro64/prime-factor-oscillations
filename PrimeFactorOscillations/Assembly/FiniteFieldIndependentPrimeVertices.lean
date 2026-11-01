/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Assembly.FiniteFieldIndependentPrimeVertexDensity
import PrimeFactorOscillations.Helpers.NativePrimeVertexGapGreedy

/-! # Infinite fully squareclass-independent vertex/gap families in prime reservoirs

Only a nonvanishing upper prime frequency is required. No lower density,
density limit, equidistribution or effective rate is assumed for the reservoir.
-/

set_option autoImplicit false
set_option Elab.async false

namespace PrimeFactorOscillations.FiniteFieldIntegerSignature

variable (R : Nat -> Prop) [DecidablePred R]

theorem native_gap_reservoir_prefix_step_subset (Y : Nat) :
    nativePrimeVertexGapReservoirPrefix R (Y + 1) <=
      insert (Y + 1) (nativePrimeVertexGapReservoirPrefix R Y) := by
  change (if R (Y + 1) then
    nativePrimeVertexGapGreedyInsert (nativePrimeVertexGapReservoirPrefix R Y) (Y + 1)
    else nativePrimeVertexGapReservoirPrefix R Y) <= _
  split
  . exact native_prime_gap_insert_subset _ _
  . intro p hp
    exact Finset.mem_insert_of_mem hp

theorem native_gap_reservoir_prefix_geometry (Y : Nat) :
    And
      (forall p : Nat, Membership.mem (nativePrimeVertexGapReservoirPrefix R Y) p ->
        And (Nat.Prime p) (And (R p) (p <= Y)))
      (nativePrimeVertexGapIndependent (nativePrimeVertexGapReservoirPrefix R Y)) := by
  induction Y with
  | zero =>
    constructor
    . intro p hp
      simp [nativePrimeVertexGapReservoirPrefix] at hp
    . exact native_gap_independent_empty
  | succ Y ih =>
    change And
      (forall p : Nat,
        Membership.mem (if R (Y + 1) then
          nativePrimeVertexGapGreedyInsert (nativePrimeVertexGapReservoirPrefix R Y) (Y + 1)
          else nativePrimeVertexGapReservoirPrefix R Y) p ->
            And (Nat.Prime p) (And (R p) (p <= Y + 1)))
      (nativePrimeVertexGapIndependent (if R (Y + 1) then
        nativePrimeVertexGapGreedyInsert (nativePrimeVertexGapReservoirPrefix R Y) (Y + 1)
        else nativePrimeVertexGapReservoirPrefix R Y))
    by_cases hR : R (Y + 1)
    . rw [ite_eq_left hR]
      unfold nativePrimeVertexGapGreedyInsert
      by_cases h : And (Nat.Prime (Y + 1))
          (nativePrimeVertexGapIndependent (insert (Y + 1) (nativePrimeVertexGapReservoirPrefix R Y)))
      . rw [ite_eq_left h]
        refine And.intro ?_ h.2
        intro p hp
        rcases Finset.mem_insert.mp hp with heq | hpOld
        . subst p
          exact And.intro h.1 (And.intro hR (le_refl _))
        . have hh := ih.1 p hpOld
          exact And.intro hh.1 (And.intro hh.2.1 (Nat.le_succ_of_le hh.2.2))
      . rw [ite_eq_right h]
        refine And.intro ?_ ih.2
        intro p hp
        have hh := ih.1 p hp
        exact And.intro hh.1 (And.intro hh.2.1 (Nat.le_succ_of_le hh.2.2))
    . rw [ite_eq_right hR]
      refine And.intro ?_ ih.2
      intro p hp
      have hh := ih.1 p hp
      exact And.intro hh.1 (And.intro hh.2.1 (Nat.le_succ_of_le hh.2.2))

theorem native_gap_reservoir_prefix_monotone : Monotone (nativePrimeVertexGapReservoirPrefix R) := by
  apply monotone_nat_of_le_succ
  intro Y
  change nativePrimeVertexGapReservoirPrefix R Y <=
    if R (Y + 1) then
      nativePrimeVertexGapGreedyInsert (nativePrimeVertexGapReservoirPrefix R Y) (Y + 1)
    else nativePrimeVertexGapReservoirPrefix R Y
  split
  . exact native_prime_gap_insert_contains _ _
  . intro p hp
    exact hp

theorem native_gap_reservoir_prefix_mem_birth (Y p : Nat)
    (hp : Membership.mem (nativePrimeVertexGapReservoirPrefix R Y) p) :
    Membership.mem (nativePrimeVertexGapReservoirPrefix R p) p := by
  induction Y with
  | zero => simp [nativePrimeVertexGapReservoirPrefix] at hp
  | succ Y ih =>
    have hstep : Membership.mem (insert (Y + 1) (nativePrimeVertexGapReservoirPrefix R Y)) p :=
      native_gap_reservoir_prefix_step_subset R Y hp
    rcases Finset.mem_insert.mp hstep with heq | hpOld
    . subst p
      exact hp
    . exact ih hpOld

theorem native_gap_reservoir_prefix_mem_iff (Y p : Nat) :
    Membership.mem (nativePrimeVertexGapReservoirPrefix R Y) p <->
      And (Membership.mem (nativePrimeVertexGapReservoirClass R) p) (p <= Y) := by
  constructor
  . intro hp
    exact And.intro (native_gap_reservoir_prefix_mem_birth R Y p hp)
      ((native_gap_reservoir_prefix_geometry R Y).1 p hp).2.2
  . intro hp
    exact native_gap_reservoir_prefix_monotone R hp.2 hp.1

theorem native_gap_reservoir_class_geometry (p : Nat)
    (hp : Membership.mem (nativePrimeVertexGapReservoirClass R) p) :
    And (Nat.Prime p) (R p) := by
  have h := (native_gap_reservoir_prefix_geometry R p).1 p hp
  exact And.intro h.1 h.2.1

theorem native_gap_reservoir_class_infinite
    (hR : Not (Filter.Tendsto (fun N : Nat => primeEventProbability N R)
      Filter.atTop (nhds 0))) :
    Set.Infinite (nativePrimeVertexGapReservoirClass R) := by
  intro hfinite
  choose B hB using hfinite.bddAbove
  have hgeom := native_gap_reservoir_prefix_geometry R B
  choose q hq using exists_native_prime_gap_reservoir_extension_above R hR
    (nativePrimeVertexGapReservoirPrefix R B) B
    (fun p hp => (hgeom.1 p hp).1) hgeom.2 (fun p hp => (hgeom.1 p hp).2.2)
  have hlarge : B < q := hq.2.2.1
  have hbefore : nativePrimeVertexGapReservoirPrefix R (q - 1) =
      nativePrimeVertexGapReservoirPrefix R B := by
    apply Finset.Subset.antisymm
    . intro p hp
      have hc := (native_gap_reservoir_prefix_mem_iff R (q - 1) p).mp hp
      exact (native_gap_reservoir_prefix_mem_iff R B p).mpr (And.intro hc.1 (hB hc.1))
    . exact native_gap_reservoir_prefix_monotone R (by omega)
  have hqeq : q - 1 + 1 = q := by omega
  have hat : nativePrimeVertexGapReservoirPrefix R q =
      nativePrimeVertexGapGreedyInsert (nativePrimeVertexGapReservoirPrefix R B) q := by
    calc
      _ = nativePrimeVertexGapReservoirPrefix R ((q - 1) + 1) :=
        congrArg (nativePrimeVertexGapReservoirPrefix R) hqeq.symm
      _ = if R ((q - 1) + 1) then
          nativePrimeVertexGapGreedyInsert (nativePrimeVertexGapReservoirPrefix R (q - 1)) ((q - 1) + 1)
          else nativePrimeVertexGapReservoirPrefix R (q - 1) := rfl
      _ = _ := by rw [hbefore, hqeq, ite_eq_left hq.2.1]
  have hmem : Membership.mem (nativePrimeVertexGapReservoirClass R) q := by
    change Membership.mem (nativePrimeVertexGapReservoirPrefix R q) q
    rw [hat]
    unfold nativePrimeVertexGapGreedyInsert
    rw [ite_eq_left (And.intro hq.1 hq.2.2.2)]
    exact Finset.mem_insert_self _ _
  have hqb := hB hmem
  omega

theorem native_gap_reservoir_class_finite_independent (P : Finset Nat)
    (hP : forall p : Nat, Membership.mem P p ->
      Membership.mem (nativePrimeVertexGapReservoirClass R) p) :
    nativePrimeVertexGapIndependent P := by
  choose B hB using P.finite_toSet.bddAbove
  apply native_gap_independent_mono (Q := nativePrimeVertexGapReservoirPrefix R B)
    ?_ (native_gap_reservoir_prefix_geometry R B).2
  intro p hp
  exact (native_gap_reservoir_prefix_mem_iff R B p).mpr (And.intro (hP p hp) (hB hp))

theorem native_infinite_prime_gap_independent_family_in_reservoir
    (hR : Not (Filter.Tendsto (fun N : Nat => primeEventProbability N R)
      Filter.atTop (nhds 0))) :
    And (Set.Infinite (nativePrimeVertexGapReservoirClass R))
      (And (forall p : Nat, Membership.mem (nativePrimeVertexGapReservoirClass R) p ->
          And (Nat.Prime p) (R p))
        (forall P : Finset Nat,
          (forall p : Nat, Membership.mem P p ->
            Membership.mem (nativePrimeVertexGapReservoirClass R) p) ->
              nativePrimeVertexGapIndependent P)) :=
  And.intro (native_gap_reservoir_class_infinite R hR)
    (And.intro (native_gap_reservoir_class_geometry R)
      (native_gap_reservoir_class_finite_independent R))

theorem native_gap_reservoir_infinite_of_positive_upper_density (delta : Real)
    (hdelta : 0 < delta)
    (hfreq : forall B : Nat, exists N : Nat,
      And (B <= N) (delta <= primeEventProbability N R)) :
    Set.Infinite (nativePrimeVertexGapReservoirClass R) := by
  apply native_gap_reservoir_class_infinite R
  intro hzero
  have hev := hzero.eventually_lt_const hdelta
  choose B hB using Filter.eventually_atTop.mp hev
  choose N hN using hfreq B
  exact not_lt_of_ge hN.2 (hB N hN.1)

theorem native_infinite_prime_gap_independent_family :
    And (Set.Infinite (nativePrimeVertexGapReservoirClass (fun _ => True)))
      (And (forall p : Nat,
          Membership.mem (nativePrimeVertexGapReservoirClass (fun _ => True)) p -> Nat.Prime p)
        (forall P : Finset Nat,
          (forall p : Nat, Membership.mem P p ->
            Membership.mem (nativePrimeVertexGapReservoirClass (fun _ => True)) p) ->
              nativePrimeVertexGapIndependent P)) := by
  have hfalse : Filter.Tendsto
      (fun N : Nat => primeEventProbability N (fun _ => Not True))
        Filter.atTop (nhds 0) := by
    have heq : (fun N : Nat => primeEventProbability N (fun _ => Not True)) =
        (fun _ : Nat => (0 : Real)) := by
      funext N
      simp [primeEventProbability]
    rw [heq]
    exact tendsto_const_nhds
  have hone := tendsto_prime_probability_one_of_complement_zero (fun _ : Nat => True) hfalse
  have hR : Not (Filter.Tendsto
      (fun N : Nat => primeEventProbability N (fun _ : Nat => True))
        Filter.atTop (nhds 0)) := by
    intro hzero
    have h01 : (0 : Real) = 1 := tendsto_nhds_unique hzero hone
    norm_num at h01
  have h := native_infinite_prime_gap_independent_family_in_reservoir (fun _ => True) hR
  exact And.intro h.1 (And.intro (fun p hp => (h.2.1 p hp).1) h.2.2)

end PrimeFactorOscillations.FiniteFieldIntegerSignature

/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Assembly.FiniteFieldNativeVertexGreedy
import PrimeFactorOscillations.Assembly.FiniteFieldNativeVertexReservoirExtension
import PrimeFactorOscillations.Definitions.NativePrimeVertexReservoir

/-! # Complete native-flat families in positive-upper-density prime reservoirs

Only a nonvanishing upper prime frequency is required. No lower density,
density limit, equidistribution or effective rate is assumed for the reservoir.
-/

set_option autoImplicit false
set_option Elab.async false

namespace PrimeFactorOscillations.FiniteFieldIntegerSignature

variable (R : Nat -> Prop) [DecidablePred R]

theorem native_reservoir_prefix_step_subset (Y : Nat) :
    nativePrimeVertexReservoirPrefix R (Y + 1) <=
      insert (Y + 1) (nativePrimeVertexReservoirPrefix R Y) := by
  change (if R (Y + 1) then
    nativePrimeVertexGreedyInsert (nativePrimeVertexReservoirPrefix R Y) (Y + 1)
    else nativePrimeVertexReservoirPrefix R Y) <= _
  split
  . exact native_prime_vertex_insert_subset _ _
  . intro p hp
    exact Finset.mem_insert_of_mem hp

theorem native_reservoir_prefix_geometry (Y : Nat) :
    And
      (forall p : Nat, Membership.mem (nativePrimeVertexReservoirPrefix R Y) p ->
        And (Nat.Prime p) (And (R p) (p <= Y)))
      (nativePrimeVertexSquareFlat (nativePrimeVertexReservoirPrefix R Y)) := by
  induction Y with
  | zero =>
    constructor
    . intro p hp
      simp [nativePrimeVertexReservoirPrefix] at hp
    . intro p hp
      simp [nativePrimeVertexReservoirPrefix] at hp
  | succ Y ih =>
    change And
      (forall p : Nat,
        Membership.mem (if R (Y + 1) then
          nativePrimeVertexGreedyInsert (nativePrimeVertexReservoirPrefix R Y) (Y + 1)
          else nativePrimeVertexReservoirPrefix R Y) p ->
            And (Nat.Prime p) (And (R p) (p <= Y + 1)))
      (nativePrimeVertexSquareFlat (if R (Y + 1) then
        nativePrimeVertexGreedyInsert (nativePrimeVertexReservoirPrefix R Y) (Y + 1)
        else nativePrimeVertexReservoirPrefix R Y))
    by_cases hR : R (Y + 1)
    . rw [ite_eq_left hR]
      unfold nativePrimeVertexGreedyInsert
      by_cases h : And (Nat.Prime (Y + 1))
          (nativePrimeVertexSquareFlat (insert (Y + 1) (nativePrimeVertexReservoirPrefix R Y)))
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

theorem native_reservoir_prefix_monotone : Monotone (nativePrimeVertexReservoirPrefix R) := by
  apply monotone_nat_of_le_succ
  intro Y
  change nativePrimeVertexReservoirPrefix R Y <=
    if R (Y + 1) then
      nativePrimeVertexGreedyInsert (nativePrimeVertexReservoirPrefix R Y) (Y + 1)
    else nativePrimeVertexReservoirPrefix R Y
  split
  . exact native_prime_vertex_insert_contains _ _
  . intro p hp
    exact hp

theorem native_reservoir_prefix_mem_birth (Y p : Nat)
    (hp : Membership.mem (nativePrimeVertexReservoirPrefix R Y) p) :
    Membership.mem (nativePrimeVertexReservoirPrefix R p) p := by
  induction Y with
  | zero => simp [nativePrimeVertexReservoirPrefix] at hp
  | succ Y ih =>
    have hstep : Membership.mem (insert (Y + 1) (nativePrimeVertexReservoirPrefix R Y)) p :=
      native_reservoir_prefix_step_subset R Y hp
    rcases Finset.mem_insert.mp hstep with heq | hpOld
    . subst p
      exact hp
    . exact ih hpOld

theorem native_reservoir_prefix_mem_iff (Y p : Nat) :
    Membership.mem (nativePrimeVertexReservoirPrefix R Y) p <->
      And (Membership.mem (nativePrimeVertexReservoirClass R) p) (p <= Y) := by
  constructor
  . intro hp
    exact And.intro (native_reservoir_prefix_mem_birth R Y p hp)
      ((native_reservoir_prefix_geometry R Y).1 p hp).2.2
  . intro hp
    exact native_reservoir_prefix_monotone R hp.2 hp.1

theorem native_reservoir_class_geometry (p : Nat)
    (hp : Membership.mem (nativePrimeVertexReservoirClass R) p) :
    And (Nat.Prime p) (R p) := by
  have h := (native_reservoir_prefix_geometry R p).1 p hp
  exact And.intro h.1 h.2.1

theorem native_reservoir_class_infinite
    (hR : Not (Filter.Tendsto (fun N : Nat => primeEventProbability N R)
      Filter.atTop (nhds 0))) :
    Set.Infinite (nativePrimeVertexReservoirClass R) := by
  intro hfinite
  choose B hB using hfinite.bddAbove
  have hgeom := native_reservoir_prefix_geometry R B
  choose q hq using exists_native_prime_vertex_reservoir_extension_above R hR
    (nativePrimeVertexReservoirPrefix R B) B
    (fun p hp => (hgeom.1 p hp).1) hgeom.2 (fun p hp => (hgeom.1 p hp).2.2)
  have hlarge : B < q := hq.2.2.1
  have hbefore : nativePrimeVertexReservoirPrefix R (q - 1) =
      nativePrimeVertexReservoirPrefix R B := by
    apply Finset.Subset.antisymm
    . intro p hp
      have hc := (native_reservoir_prefix_mem_iff R (q - 1) p).mp hp
      exact (native_reservoir_prefix_mem_iff R B p).mpr (And.intro hc.1 (hB hc.1))
    . exact native_reservoir_prefix_monotone R (by omega)
  have hqeq : q - 1 + 1 = q := by omega
  have hat : nativePrimeVertexReservoirPrefix R q =
      nativePrimeVertexGreedyInsert (nativePrimeVertexReservoirPrefix R B) q := by
    calc
      _ = nativePrimeVertexReservoirPrefix R ((q - 1) + 1) :=
        congrArg (nativePrimeVertexReservoirPrefix R) hqeq.symm
      _ = if R ((q - 1) + 1) then
          nativePrimeVertexGreedyInsert (nativePrimeVertexReservoirPrefix R (q - 1)) ((q - 1) + 1)
          else nativePrimeVertexReservoirPrefix R (q - 1) := rfl
      _ = _ := by rw [hbefore, hqeq, ite_eq_left hq.2.1]
  have hmem : Membership.mem (nativePrimeVertexReservoirClass R) q := by
    change Membership.mem (nativePrimeVertexReservoirPrefix R q) q
    rw [hat]
    unfold nativePrimeVertexGreedyInsert
    rw [ite_eq_left (And.intro hq.1 hq.2.2.2)]
    exact Finset.mem_insert_self _ _
  have hqb := hB hmem
  omega

theorem native_reservoir_class_square_compatible (p q r s : Nat)
    (hp : Membership.mem (nativePrimeVertexReservoirClass R) p)
    (hq : Membership.mem (nativePrimeVertexReservoirClass R) q)
    (hr : Membership.mem (nativePrimeVertexReservoirClass R) r)
    (hs : Membership.mem (nativePrimeVertexReservoirClass R) s)
    (hpq : p < q) (hrs : r < s) (hneq : Not (And (p = r) (q = s))) :
    nativePrimePairSquareCompatible (p, q - p) (r, s - r) := by
  let Y := p + q + r + s
  have hpY : Membership.mem (nativePrimeVertexReservoirPrefix R Y) p :=
    (native_reservoir_prefix_mem_iff R Y p).mpr (And.intro hp (by dsimp only [Y]; omega))
  have hqY : Membership.mem (nativePrimeVertexReservoirPrefix R Y) q :=
    (native_reservoir_prefix_mem_iff R Y q).mpr (And.intro hq (by dsimp only [Y]; omega))
  have hrY : Membership.mem (nativePrimeVertexReservoirPrefix R Y) r :=
    (native_reservoir_prefix_mem_iff R Y r).mpr (And.intro hr (by dsimp only [Y]; omega))
  have hsY : Membership.mem (nativePrimeVertexReservoirPrefix R Y) s :=
    (native_reservoir_prefix_mem_iff R Y s).mpr (And.intro hs (by dsimp only [Y]; omega))
  exact (native_reservoir_prefix_geometry R Y).2 p hpY q hqY hpq r hrY s hsY hrs hneq

theorem native_reservoir_class_agreement (p q r s : Nat)
    (hp : Membership.mem (nativePrimeVertexReservoirClass R) p)
    (hq : Membership.mem (nativePrimeVertexReservoirClass R) q)
    (hr : Membership.mem (nativePrimeVertexReservoirClass R) r)
    (hs : Membership.mem (nativePrimeVertexReservoirClass R) s)
    (hpq : p < q) (hrs : r < s) (hneq : Not (And (p = r) (q = s))) :
    nativeAgreementRate p (q - p) r (s - r) = 3 / 8 := by
  have hcomp := native_reservoir_class_square_compatible R p q r s hp hq hr hs hpq hrs hneq
  unfold nativePrimePairSquareCompatible at hcomp
  have hlower : Not (IsSquare ((q - p) * (s - r) * p * r)) := by
    simpa only [mul_assoc, mul_comm, mul_left_comm] using hcomp.1
  have hupper : Not (IsSquare ((q - p) * (s - r) *
      (p + (q - p)) * (r + (s - r)))) := by
    simpa only [mul_assoc, mul_comm, mul_left_comm] using hcomp.2
  rw [native_agreement_rate_eq_square_test p (q - p) r (s - r)
    (native_reservoir_class_geometry R p hp).1.pos (Nat.sub_pos_of_lt hpq)
    (native_reservoir_class_geometry R r hr).1.pos (Nat.sub_pos_of_lt hrs)]
  rw [ite_eq_right hlower, ite_eq_right hupper]
  norm_num

theorem native_complete_prime_vertex_family_in_reservoir
    (hR : Not (Filter.Tendsto (fun N : Nat => primeEventProbability N R)
      Filter.atTop (nhds 0))) :
    And (Set.Infinite (nativePrimeVertexReservoirClass R))
      (And (forall p : Nat, Membership.mem (nativePrimeVertexReservoirClass R) p ->
          And (Nat.Prime p) (R p))
        (forall p q r s : Nat,
          Membership.mem (nativePrimeVertexReservoirClass R) p ->
          Membership.mem (nativePrimeVertexReservoirClass R) q ->
          Membership.mem (nativePrimeVertexReservoirClass R) r ->
          Membership.mem (nativePrimeVertexReservoirClass R) s ->
          p < q -> r < s -> Not (And (p = r) (q = s)) ->
            nativeAgreementRate p (q - p) r (s - r) = 3 / 8)) :=
  And.intro (native_reservoir_class_infinite R hR)
    (And.intro (native_reservoir_class_geometry R) (native_reservoir_class_agreement R))

theorem native_reservoir_infinite_of_positive_upper_density (delta : Real)
    (hdelta : 0 < delta)
    (hfreq : forall B : Nat, exists N : Nat,
      And (B <= N) (delta <= primeEventProbability N R)) :
    Set.Infinite (nativePrimeVertexReservoirClass R) := by
  apply native_reservoir_class_infinite R
  intro hzero
  have hev := hzero.eventually_lt_const hdelta
  choose B hB using Filter.eventually_atTop.mp hev
  choose N hN using hfreq B
  exact not_lt_of_ge hN.2 (hB N hN.1)


/-- A finite prime coloring has a computable monochromatic complete family.
The color is existentially selected; no uniform computable color selector is
claimed. -/
theorem native_monochromatic_complete_prime_vertex_family
    {I : Type*} [Fintype I] [DecidableEq I] (c : Nat -> I) :
    exists i : I,
      And (Set.Infinite (nativePrimeVertexReservoirClass (fun p => c p = i)))
        (And (forall p : Nat,
            Membership.mem (nativePrimeVertexReservoirClass (fun p => c p = i)) p ->
              And (Nat.Prime p) (c p = i))
          (forall p q r s : Nat,
            Membership.mem (nativePrimeVertexReservoirClass (fun p => c p = i)) p ->
            Membership.mem (nativePrimeVertexReservoirClass (fun p => c p = i)) q ->
            Membership.mem (nativePrimeVertexReservoirClass (fun p => c p = i)) r ->
            Membership.mem (nativePrimeVertexReservoirClass (fun p => c p = i)) s ->
            p < q -> r < s -> Not (And (p = r) (q = s)) ->
              nativeAgreementRate p (q - p) r (s - r) = 3 / 8)) := by
  have hcolor : exists i : I,
      Not (Filter.Tendsto (fun N : Nat => primeEventProbability N (fun p => c p = i))
        Filter.atTop (nhds 0)) := by
    classical
    by_contra hnone
    have hEach : forall i : I,
        Filter.Tendsto (fun N : Nat => primeEventProbability N (fun p => c p = i))
          Filter.atTop (nhds 0) := by
      intro i
      by_contra hi
      exact hnone (Exists.intro i hi)
    have hUnion := tendsto_prime_probability_finite_union_zero (fun i p => c p = i) hEach
    have hzero := tendsto_prime_probability_zero_of_imp (fun _ : Nat => True)
      (fun p => exists i : I, c p = i) (fun p _ => Exists.intro (c p) rfl) hUnion
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
    have h01 : (0 : Real) = 1 := tendsto_nhds_unique hzero hone
    norm_num at h01
  choose i hi using hcolor
  exact Exists.intro i (native_complete_prime_vertex_family_in_reservoir (fun p => c p = i) hi)
end PrimeFactorOscillations.FiniteFieldIntegerSignature

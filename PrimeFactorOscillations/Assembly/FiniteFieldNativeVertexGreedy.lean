/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Assembly.FiniteFieldNativeArithmeticAgreement
import PrimeFactorOscillations.Assembly.FiniteFieldNativeVertexDensity

/-! # One computable infinite complete prime-vertex family

All pair labels formed from the single vertex class separate in both square
rows. Every finite greedy prefix persists, and a finite final class would
contradict the proved density-one prime-extension theorem.
-/

set_option autoImplicit false
set_option Elab.async false

namespace PrimeFactorOscillations.FiniteFieldIntegerSignature

theorem native_prime_vertex_insert_contains (P : Finset Nat) (q : Nat) :
    P <= nativePrimeVertexGreedyInsert P q := by
  unfold nativePrimeVertexGreedyInsert
  split
  . intro p hp
    exact Finset.mem_insert_of_mem hp
  . intro p hp
    exact hp

theorem native_prime_vertex_insert_subset (P : Finset Nat) (q : Nat) :
    nativePrimeVertexGreedyInsert P q <= insert q P := by
  unfold nativePrimeVertexGreedyInsert
  split
  . intro p hp
    exact hp
  . intro p hp
    exact Finset.mem_insert_of_mem hp

theorem native_prime_vertex_prefix_geometry (Y : Nat) :
    And
      (forall p : Nat, Membership.mem (nativePrimeVertexGreedyPrefix Y) p ->
        And (Nat.Prime p) (p <= Y))
      (nativePrimeVertexSquareFlat (nativePrimeVertexGreedyPrefix Y)) := by
  induction Y with
  | zero =>
    constructor
    . intro p hp
      simp [nativePrimeVertexGreedyPrefix] at hp
    . intro p hp
      simp [nativePrimeVertexGreedyPrefix] at hp
  | succ Y ih =>
    change And
      (forall p : Nat,
        Membership.mem (nativePrimeVertexGreedyInsert (nativePrimeVertexGreedyPrefix Y) (Y + 1)) p ->
          And (Nat.Prime p) (p <= Y + 1))
      (nativePrimeVertexSquareFlat
        (nativePrimeVertexGreedyInsert (nativePrimeVertexGreedyPrefix Y) (Y + 1)))
    unfold nativePrimeVertexGreedyInsert
    by_cases h : And (Nat.Prime (Y + 1))
        (nativePrimeVertexSquareFlat (insert (Y + 1) (nativePrimeVertexGreedyPrefix Y)))
    . simp only [ite_eq_left h]
      refine And.intro ?_ h.2
      intro p hp
      rcases Finset.mem_insert.mp hp with heq | hpOld
      . subst p
        exact And.intro h.1 (le_refl _)
      . have hh := ih.1 p hpOld
        exact And.intro hh.1 (Nat.le_succ_of_le hh.2)
    . simp only [ite_eq_right h]
      refine And.intro ?_ ih.2
      intro p hp
      have hh := ih.1 p hp
      exact And.intro hh.1 (Nat.le_succ_of_le hh.2)

theorem native_prime_vertex_prefix_monotone : Monotone nativePrimeVertexGreedyPrefix := by
  apply monotone_nat_of_le_succ
  intro Y
  change nativePrimeVertexGreedyPrefix Y <=
    nativePrimeVertexGreedyInsert (nativePrimeVertexGreedyPrefix Y) (Y + 1)
  exact native_prime_vertex_insert_contains _ _

theorem native_prime_vertex_prefix_mem_birth (Y p : Nat)
    (hp : Membership.mem (nativePrimeVertexGreedyPrefix Y) p) :
    Membership.mem (nativePrimeVertexGreedyPrefix p) p := by
  induction Y with
  | zero => simp [nativePrimeVertexGreedyPrefix] at hp
  | succ Y ih =>
    have hstep : Membership.mem (insert (Y + 1) (nativePrimeVertexGreedyPrefix Y)) p :=
      native_prime_vertex_insert_subset (nativePrimeVertexGreedyPrefix Y) (Y + 1) hp
    rcases Finset.mem_insert.mp hstep with heq | hpOld
    . subst p
      exact hp
    . exact ih hpOld

theorem native_prime_vertex_prefix_mem_iff (Y p : Nat) :
    Membership.mem (nativePrimeVertexGreedyPrefix Y) p <->
      And (Membership.mem nativePrimeVertexGreedyClass p) (p <= Y) := by
  constructor
  . intro hp
    exact And.intro (native_prime_vertex_prefix_mem_birth Y p hp)
      ((native_prime_vertex_prefix_geometry Y).1 p hp).2
  . intro hp
    exact native_prime_vertex_prefix_monotone hp.2 hp.1

theorem native_prime_vertex_class_prime (p : Nat)
    (hp : Membership.mem nativePrimeVertexGreedyClass p) : Nat.Prime p :=
  ((native_prime_vertex_prefix_geometry p).1 p hp).1

theorem native_prime_vertex_class_infinite : Set.Infinite nativePrimeVertexGreedyClass := by
  intro hfinite
  choose B hB using hfinite.bddAbove
  have hgeom := native_prime_vertex_prefix_geometry B
  choose q hq using exists_native_prime_vertex_extension_above
    (nativePrimeVertexGreedyPrefix B) B
    (fun p hp => (hgeom.1 p hp).1) hgeom.2 (fun p hp => (hgeom.1 p hp).2)
  have hbefore : nativePrimeVertexGreedyPrefix (q - 1) = nativePrimeVertexGreedyPrefix B := by
    apply Finset.Subset.antisymm
    . intro p hp
      have hc := (native_prime_vertex_prefix_mem_iff (q - 1) p).mp hp
      exact (native_prime_vertex_prefix_mem_iff B p).mpr (And.intro hc.1 (hB hc.1))
    . exact native_prime_vertex_prefix_monotone (by omega)
  have hqeq : q - 1 + 1 = q := by omega
  have hat : nativePrimeVertexGreedyPrefix q =
      nativePrimeVertexGreedyInsert (nativePrimeVertexGreedyPrefix B) q := by
    calc
      _ = nativePrimeVertexGreedyPrefix ((q - 1) + 1) :=
        congrArg nativePrimeVertexGreedyPrefix hqeq.symm
      _ = nativePrimeVertexGreedyInsert (nativePrimeVertexGreedyPrefix (q - 1)) ((q - 1) + 1) :=
        rfl
      _ = _ := by rw [hbefore, hqeq]
  have hmem : Membership.mem nativePrimeVertexGreedyClass q := by
    change Membership.mem (nativePrimeVertexGreedyPrefix q) q
    rw [hat]
    unfold nativePrimeVertexGreedyInsert
    rw [ite_eq_left (And.intro hq.1 hq.2.2)]
    exact Finset.mem_insert_self _ _
  have hqb := hB hmem
  omega

theorem native_prime_vertex_class_square_compatible (p q r s : Nat)
    (hp : Membership.mem nativePrimeVertexGreedyClass p)
    (hq : Membership.mem nativePrimeVertexGreedyClass q)
    (hr : Membership.mem nativePrimeVertexGreedyClass r)
    (hs : Membership.mem nativePrimeVertexGreedyClass s)
    (hpq : p < q) (hrs : r < s) (hneq : Not (And (p = r) (q = s))) :
    nativePrimePairSquareCompatible (p, q - p) (r, s - r) := by
  let Y := p + q + r + s
  have hpY : Membership.mem (nativePrimeVertexGreedyPrefix Y) p :=
    (native_prime_vertex_prefix_mem_iff Y p).mpr (And.intro hp (by dsimp only [Y]; omega))
  have hqY : Membership.mem (nativePrimeVertexGreedyPrefix Y) q :=
    (native_prime_vertex_prefix_mem_iff Y q).mpr (And.intro hq (by dsimp only [Y]; omega))
  have hrY : Membership.mem (nativePrimeVertexGreedyPrefix Y) r :=
    (native_prime_vertex_prefix_mem_iff Y r).mpr (And.intro hr (by dsimp only [Y]; omega))
  have hsY : Membership.mem (nativePrimeVertexGreedyPrefix Y) s :=
    (native_prime_vertex_prefix_mem_iff Y s).mpr (And.intro hs (by dsimp only [Y]; omega))
  exact (native_prime_vertex_prefix_geometry Y).2 p hpY q hqY hpq r hrY s hsY hrs hneq

theorem native_prime_vertex_class_agreement (p q r s : Nat)
    (hp : Membership.mem nativePrimeVertexGreedyClass p)
    (hq : Membership.mem nativePrimeVertexGreedyClass q)
    (hr : Membership.mem nativePrimeVertexGreedyClass r)
    (hs : Membership.mem nativePrimeVertexGreedyClass s)
    (hpq : p < q) (hrs : r < s) (hneq : Not (And (p = r) (q = s))) :
    nativeAgreementRate p (q - p) r (s - r) = 3 / 8 := by
  have hcomp := native_prime_vertex_class_square_compatible p q r s hp hq hr hs hpq hrs hneq
  unfold nativePrimePairSquareCompatible at hcomp
  have hlower : Not (IsSquare ((q - p) * (s - r) * p * r)) := by
    simpa only [mul_assoc, mul_comm, mul_left_comm] using hcomp.1
  have hupper : Not (IsSquare ((q - p) * (s - r) *
      (p + (q - p)) * (r + (s - r)))) := by
    simpa only [mul_assoc, mul_comm, mul_left_comm] using hcomp.2
  rw [native_agreement_rate_eq_square_test p (q - p) r (s - r)
    (native_prime_vertex_class_prime p hp).pos (Nat.sub_pos_of_lt hpq)
    (native_prime_vertex_class_prime r hr).pos (Nat.sub_pos_of_lt hrs)]
  rw [ite_eq_right hlower, ite_eq_right hupper]
  norm_num

theorem native_computable_complete_prime_vertex_family :
    And (Set.Infinite nativePrimeVertexGreedyClass)
      (And (forall p : Nat, Membership.mem nativePrimeVertexGreedyClass p -> Nat.Prime p)
        (forall p q r s : Nat,
          Membership.mem nativePrimeVertexGreedyClass p ->
          Membership.mem nativePrimeVertexGreedyClass q ->
          Membership.mem nativePrimeVertexGreedyClass r ->
          Membership.mem nativePrimeVertexGreedyClass s ->
          p < q -> r < s -> Not (And (p = r) (q = s)) ->
            nativeAgreementRate p (q - p) r (s - r) = 3 / 8)) :=
  And.intro native_prime_vertex_class_infinite
    (And.intro native_prime_vertex_class_prime native_prime_vertex_class_agreement)

end PrimeFactorOscillations.FiniteFieldIntegerSignature

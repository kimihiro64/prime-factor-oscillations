/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Definitions.NativePrimeEulerianMasks
import PrimeFactorOscillations.Helpers.NativePrimeDiagonalCycles

/-! # All Eulerian masks and signed phase-twisted diagonal square tests -/

set_option autoImplicit false
set_option Elab.async false

namespace PrimeFactorOscillations.FiniteFieldIntegerSignature

theorem native_eulerian_masks_mem_iff (P : Finset Nat)
    (G C : Finset (Prod Nat Nat)) :
    Membership.mem (nativeEulerianMasks P G) C <->
      And (C <= G)
        (forall p : Nat, Membership.mem P p -> nativePrimeVertexCycleDegree C p % 2 = 0) := by
  rw [nativeEulerianMasks, Finset.mem_filter, Finset.mem_powerset]
  constructor
  . intro h
    refine And.intro h.1 ?_
    intro p hp
    have hm : Membership.mem
        (P.filter (fun x => nativePrimeVertexCycleDegree C x % 2 = 0)) p := by
      rw [h.2]
      exact hp
    exact (Finset.mem_filter.mp hm).2
  . intro h
    refine And.intro h.1 ?_
    apply Finset.Subset.antisymm (Finset.filter_subset _ _)
    intro p hp
    exact Finset.mem_filter.mpr (And.intro hp (h.2 p hp))

theorem native_eulerian_count_positive (P : Finset Nat)
    (G : Finset (Prod Nat Nat)) : 0 < nativeEulerianCount P G := by
  have hm : Membership.mem (nativeEulerianMasks P G) {} := by
    apply (native_eulerian_masks_mem_iff P G {}).mpr
    exact And.intro (Finset.empty_subset G) (by simp [nativePrimeVertexCycleDegree])
  exact Finset.card_pos.mpr (Exists.intro {} hm)

theorem native_diagonal_unsigned_isSquare_iff (P : Finset Nat)
    (hP : forall p : Nat, Membership.mem P p -> Nat.Prime p)
    (C : Finset (Prod Nat Nat)) (hC : C <= nativePrimeVertexEdges P) :
    IsSquare (C.prod (fun e => e.1 * (e.2 - e.1)) *
      C.prod (fun e => e.2 * (e.2 - e.1))) <->
      forall p : Nat, Membership.mem P p -> nativePrimeVertexCycleDegree C p % 2 = 0 := by
  constructor
  . intro hsq
    rw [native_diagonal_natural_product P C hC] at hsq
    let Q := C.prod (fun e => e.2 - e.1)
    have hQ : 0 < Q := Finset.prod_pos (fun e he =>
      Nat.sub_pos_of_lt ((native_gap_edges_mem_iff P e).mp (hC he)).2.2)
    have hwhole : IsSquare ((Q * Q) *
        P.prod (fun p => p ^ nativePrimeVertexCycleDegree C p)) := by
      simpa only [Q, pow_two] using hsq
    have hx := Nat.isSquare_mul_trans_of_pos (a := 1) (b := Q * Q)
      (c := P.prod (fun p => p ^ nativePrimeVertexCycleDegree C p))
      (Nat.mul_pos hQ hQ) (Exists.intro Q (by simp)) hwhole
    have hvertex : IsSquare (P.prod (fun p => p ^ nativePrimeVertexCycleDegree C p)) := by
      simpa only [one_mul] using hx
    exact native_prime_power_product_even_of_square P hP
      (fun p => nativePrimeVertexCycleDegree C p) hvertex
  . intro heven
    let V := P.prod (fun p => p ^ (nativePrimeVertexCycleDegree C p / 2))
    have hv : P.prod (fun p => p ^ nativePrimeVertexCycleDegree C p) = V ^ 2 := by
      calc
        _ = P.prod (fun p => (p ^ (nativePrimeVertexCycleDegree C p / 2)) ^ 2) := by
          apply Finset.prod_congr rfl
          intro p hp
          have he : nativePrimeVertexCycleDegree C p =
              nativePrimeVertexCycleDegree C p / 2 * 2 := by
            have hh := heven p hp
            omega
          calc
            _ = p ^ (nativePrimeVertexCycleDegree C p / 2 * 2) :=
              congrArg (fun n : Nat => p ^ n) he
            _ = _ := pow_mul _ _ _
        _ = V ^ 2 := by rw [Finset.prod_pow]
    refine Exists.intro ((C.prod (fun e => e.2 - e.1)) * V) ?_
    rw [native_diagonal_natural_product P C hC, hv]
    ring

theorem native_signed_positive_cast_square_iff (D : Nat) (hD : 0 < D) (b : Nat) :
    IsSquare ((-1 : Int) ^ b * (D : Int)) <-> And (IsSquare D) (b % 2 = 0) := by
  have hcast : IsSquare (D : Int) <-> IsSquare D := by
    constructor
    . intro h
      choose k hk using h
      refine Exists.intro k.natAbs ?_
      have hh := congrArg Int.natAbs hk
      simpa only [Int.natAbs_natCast, Int.natAbs_mul] using hh
    . intro h
      choose k hk using h
      exact Exists.intro (k : Int) (by exact_mod_cast hk)
  by_cases hb : b % 2 = 0
  . have he : b = 2 * (b / 2) := by omega
    have hp : (-1 : Int) ^ b = 1 := by rw [he, pow_mul]; norm_num
    rw [hp, one_mul, hcast]
    constructor
    . intro h
      exact And.intro h hb
    . intro h
      exact h.1
  . have he : b = 2 * (b / 2) + 1 := by omega
    have hp : (-1 : Int) ^ b = -1 := by
      rw [he, pow_add, pow_mul]
      norm_num
    have hpos : (0 : Int) < (D : Int) := by exact_mod_cast hD
    have hneg : (-1 : Int) ^ b * (D : Int) < 0 := by
      rw [hp, neg_one_mul]
      exact neg_lt_zero.mpr hpos
    constructor
    . intro hsq
      choose k hk using hsq
      have hn : 0 <= (-1 : Int) ^ b * (D : Int) := by
        rw [hk]
        exact mul_self_nonneg k
      exact False.elim ((not_le_of_gt hneg) hn)
    . intro h
      exact False.elim (hb h.2)

theorem native_signed_phase_diagonal_isSquare_iff (P : Finset Nat)
    (hP : forall p : Nat, Membership.mem P p -> Nat.Prime p)
    (C : Finset (Prod Nat Nat)) (hC : C <= nativePrimeVertexEdges P) (b : Nat) :
    IsSquare ((-1 : Int) ^ b * nativeSignedRowProduct C C) <->
      And (forall p : Nat, Membership.mem P p -> nativePrimeVertexCycleDegree C p % 2 = 0)
        ((b + C.card) % 2 = 0) := by
  let D := C.prod (fun e => e.1 * (e.2 - e.1)) *
    C.prod (fun e => e.2 * (e.2 - e.1))
  have hD : 0 < D := native_signed_unsigned_product_positive P hP C C hC hC
  have hf : (-1 : Int) ^ b * nativeSignedRowProduct C C =
      (-1 : Int) ^ (b + C.card) * (D : Int) := by
    rw [native_signed_row_product_factorization, pow_add]
    dsimp only [D]
    ring
  rw [hf, native_signed_positive_cast_square_iff D hD (b + C.card)]
  change And (IsSquare (C.prod (fun e => e.1 * (e.2 - e.1)) *
    C.prod (fun e => e.2 * (e.2 - e.1)))) ((b + C.card) % 2 = 0) <-> _
  rw [native_diagonal_unsigned_isSquare_iff P hP C hC]

theorem native_negative_diagonal_isSquare_iff (P : Finset Nat)
    (hP : forall p : Nat, Membership.mem P p -> Nat.Prime p)
    (C : Finset (Prod Nat Nat)) (hC : C <= nativePrimeVertexEdges P) :
    IsSquare (-nativeSignedRowProduct C C) <->
      And (forall p : Nat, Membership.mem P p -> nativePrimeVertexCycleDegree C p % 2 = 0)
        (C.card % 2 = 1) := by
  have h := native_signed_phase_diagonal_isSquare_iff P hP C hC 1
  have he : (1 + C.card) % 2 = 0 <-> C.card % 2 = 1 := by omega
  rw [he] at h
  simpa only [pow_one, neg_one_mul] using h

end PrimeFactorOscillations.FiniteFieldIntegerSignature

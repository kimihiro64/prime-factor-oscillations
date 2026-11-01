/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.NativePrimeSignedCycleKernel

/-! # Signed cycle supply without a gap-independence hypothesis

The positive even-cycle contribution exists for every strict prime graph.
Only exclusion of additional square masks needs the independent class.
-/

set_option autoImplicit false
set_option Elab.async false

namespace PrimeFactorOscillations.FiniteFieldIntegerSignature

theorem native_signed_unsigned_product_positive (P : Finset Nat)
    (hP : forall p : Nat, Membership.mem P p -> Nat.Prime p)
    (A B : Finset (Prod Nat Nat))
    (hA : A <= nativePrimeVertexEdges P) (hB : B <= nativePrimeVertexEdges P) :
    0 < A.prod (fun e => e.1 * (e.2 - e.1)) *
      B.prod (fun e => e.2 * (e.2 - e.1)) := by
  rw [native_gap_row_product_powers P A B hA hB]
  apply Finset.prod_pos
  intro x hx
  exact pow_pos (native_gap_basis_value_positive P hP x hx) _

theorem native_signed_row_product_ne_zero (P : Finset Nat)
    (hP : forall p : Nat, Membership.mem P p -> Nat.Prime p)
    (A B : Finset (Prod Nat Nat))
    (hA : A <= nativePrimeVertexEdges P) (hB : B <= nativePrimeVertexEdges P) :
    Not (nativeSignedRowProduct A B = 0) := by
  have hpos := native_signed_unsigned_product_positive P hP A B hA hB
  rw [native_signed_row_product_factorization]
  apply mul_ne_zero
  . exact pow_ne_zero _ (by decide : Not ((-1 : Int) = 0))
  . exact_mod_cast (Nat.ne_of_gt hpos)

theorem native_signed_paired_row_product_neg_of_odd (P : Finset Nat)
    (hP : forall p : Nat, Membership.mem P p -> Nat.Prime p)
    (C : Finset (Prod Nat Nat)) (hC : C <= nativePrimeVertexEdges P)
    (hodd : C.card % 2 = 1) : nativeSignedRowProduct C C < 0 := by
  have hpos := native_signed_unsigned_product_positive P hP C C hC hC
  have hcast : (0 : Int) <
      ((C.prod (fun e => e.1 * (e.2 - e.1)) *
        C.prod (fun e => e.2 * (e.2 - e.1)) : Nat) : Int) := by
    exact_mod_cast hpos
  have he : C.card = 2 * (C.card / 2) + 1 := by omega
  have hpower : (-1 : Int) ^ C.card = -1 := by
    calc
      _ = (-1 : Int) ^ (2 * (C.card / 2) + 1) :=
        congrArg (fun n : Nat => (-1 : Int) ^ n) he
      _ = -1 := by
        have htwo : (-1 : Int) ^ 2 = 1 := by decide
        rw [pow_add, pow_mul, htwo, one_pow, pow_one, one_mul]
  rw [native_signed_row_product_factorization, hpower, neg_one_mul]
  exact neg_lt_zero.mpr hcast

theorem native_signed_cycle_product_isSquare (P : Finset Nat)
    (C : Finset (Prod Nat Nat)) (hC : C <= nativePrimeVertexEdges P)
    (hdeg : forall p : Nat, Membership.mem P p -> nativePrimeVertexCycleDegree C p % 2 = 0)
    (hcard : C.card % 2 = 0) : IsSquare (nativeSignedRowProduct C C) := by
  classical
  have heven : forall x : Sum Nat (Prod Nat Nat),
      Membership.mem (nativeVertexGapBasis P) x ->
        nativeVertexGapRowMultiplicity C C x % 2 = 0 := by
    intro x hx
    cases x with
    | inl p =>
      simpa only [native_gap_row_multiplicity_vertex, nativePrimeVertexCycleDegree] using
        hdeg p ((native_gap_basis_vertex_mem P p).mp hx)
    | inr e =>
      rw [native_gap_row_multiplicity_edge]
      by_cases he : Membership.mem C e <;> simp [he]
  let Q : Nat := (nativeVertexGapBasis P).prod (fun x =>
    nativeVertexGapValue x ^ (nativeVertexGapRowMultiplicity C C x / 2))
  have hprod : C.prod (fun e => e.1 * (e.2 - e.1)) *
      C.prod (fun e => e.2 * (e.2 - e.1)) = Q ^ 2 := by
    rw [native_gap_row_product_powers P C C hC hC]
    calc
      _ = (nativeVertexGapBasis P).prod (fun x =>
          (nativeVertexGapValue x ^ (nativeVertexGapRowMultiplicity C C x / 2)) ^ 2) := by
        apply Finset.prod_congr rfl
        intro x hx
        have hp := heven x hx
        have he : nativeVertexGapRowMultiplicity C C x =
            nativeVertexGapRowMultiplicity C C x / 2 * 2 := by omega
        calc
          _ = nativeVertexGapValue x ^
              (nativeVertexGapRowMultiplicity C C x / 2 * 2) :=
            congrArg (fun n : Nat => nativeVertexGapValue x ^ n) he
          _ = _ := pow_mul _ _ _
      _ = Q ^ 2 := by rw [Finset.prod_pow]
  have he : C.card = 2 * (C.card / 2) := by omega
  have hpower : (-1 : Int) ^ C.card = 1 := by
    calc
      _ = (-1 : Int) ^ (2 * (C.card / 2)) :=
        congrArg (fun n : Nat => (-1 : Int) ^ n) he
      _ = 1 := by
        have htwo : (-1 : Int) ^ 2 = 1 := by decide
        rw [pow_mul, htwo, one_pow]
  rw [native_signed_row_product_factorization, hpower, one_mul, hprod, Nat.cast_pow]
  exact Exists.intro (Q : Int) (pow_two _)

end PrimeFactorOscillations.FiniteFieldIntegerSignature

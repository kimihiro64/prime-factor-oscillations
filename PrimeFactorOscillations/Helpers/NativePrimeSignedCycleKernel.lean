/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Definitions.NativePrimeSignedRows
import PrimeFactorOscillations.Helpers.NativePrimeVertexGapCycles

/-! # The full signed native cycle kernel

The actual lower row carries a minus sign. Its cardinal parity is retained
alongside every edge equality and vertex degree condition.
-/

set_option autoImplicit false
set_option Elab.async false

namespace PrimeFactorOscillations.FiniteFieldIntegerSignature

theorem native_signed_row_product_factorization (A B : Finset (Prod Nat Nat)) :
    nativeSignedRowProduct A B = (-1 : Int) ^ A.card *
      ((A.prod (fun e => e.1 * (e.2 - e.1)) *
        B.prod (fun e => e.2 * (e.2 - e.1)) : Nat) : Int) := by
  have hcoeff : nativeSignedLowerCoefficient =
      (fun e : Prod Nat Nat => (-1 : Int) * ((e.1 * (e.2 - e.1) : Nat) : Int)) := by
    funext e
    exact neg_eq_neg_one_mul _
  rw [nativeSignedRowProduct, hcoeff, Finset.prod_mul_distrib, Finset.prod_const]
  unfold nativeSignedUpperCoefficient
  simp only [Nat.cast_mul, Nat.cast_prod]
  ring

theorem native_signed_row_product_isSquare_iff (P : Finset Nat)
    (hP : forall p : Nat, Membership.mem P p -> Nat.Prime p)
    (hind : nativePrimeVertexGapIndependent P)
    (A B : Finset (Prod Nat Nat))
    (hA : A <= nativePrimeVertexEdges P) (hB : B <= nativePrimeVertexEdges P) :
    IsSquare (nativeSignedRowProduct A B) <->
      And (A = B) (And (forall p : Nat, Membership.mem P p ->
        nativePrimeVertexCycleDegree A p % 2 = 0) (A.card % 2 = 0)) := by
  classical
  let D := A.prod (fun e => e.1 * (e.2 - e.1)) *
    B.prod (fun e => e.2 * (e.2 - e.1))
  have hD : 0 < D := by
    dsimp only [D]
    rw [native_gap_row_product_powers P A B hA hB]
    apply Finset.prod_pos
    intro x hx
    exact pow_pos (native_gap_basis_value_positive P hP x hx) _
  have hcast : IsSquare (D : Int) <-> IsSquare D := by
    constructor
    . intro h
      cases h with
      | intro k hk =>
        refine Exists.intro k.natAbs ?_
        have hh := congrArg Int.natAbs hk
        simpa only [Int.natAbs_natCast, Int.natAbs_mul] using hh
    . intro h
      cases h with
      | intro k hk =>
        refine Exists.intro (k : Int) ?_
        exact_mod_cast hk
  have hpower : (-1 : Int) ^ A.card = if A.card % 2 = 0 then 1 else -1 := by
    have hn : A.card = 2 * (A.card / 2) + A.card % 2 := by omega
    calc
      _ = (-1 : Int) ^ (2 * (A.card / 2) + A.card % 2) := congrArg _ hn
      _ = _ := by
        rw [pow_add, pow_mul]
        have htwo : (-1 : Int) ^ 2 = 1 := by decide
        rw [htwo, one_pow, one_mul]
        have hrem : Or (A.card % 2 = 0) (A.card % 2 = 1) := by omega
        cases hrem with
        | inl hz => simp [hz]
        | inr ho => simp [ho]
  have hfactor : nativeSignedRowProduct A B = (-1 : Int) ^ A.card * (D : Int) :=
    native_signed_row_product_factorization A B
  by_cases heven : A.card % 2 = 0
  case pos =>
    have heq : nativeSignedRowProduct A B = (D : Int) := by
      rw [hfactor, hpower]
      simp [heven]
    have hNat : IsSquare D <-> And (A = B)
        (forall p : Nat, Membership.mem P p -> nativePrimeVertexCycleDegree A p % 2 = 0) :=
      native_gap_row_product_square_iff P hP hind A B hA hB
    rw [heq, hcast, hNat]
    constructor
    . intro h
      exact And.intro h.1 (And.intro h.2 heven)
    . intro h
      exact And.intro h.1 h.2.1
  case neg =>
    have hDint : (0 : Int) < (D : Int) := by exact_mod_cast hD
    have hneg : nativeSignedRowProduct A B < 0 := by
      rw [hfactor, hpower]
      simp only [ite_eq_right heven, neg_one_mul]
      exact neg_lt_zero.mpr hDint
    have hnsq : Not (IsSquare (nativeSignedRowProduct A B)) := by
      intro h
      cases h with
      | intro k hk =>
        have hnon : 0 <= nativeSignedRowProduct A B := by
          rw [hk]
          exact mul_self_nonneg k
        exact (not_le_of_gt hneg) hnon
    constructor
    . intro h
      exact False.elim (hnsq h)
    . intro h
      exact False.elim (heven h.2.2)

end PrimeFactorOscillations.FiniteFieldIntegerSignature

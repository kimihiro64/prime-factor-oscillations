/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.NativePrimePhaseCycles
import PrimeFactorOscillations.Helpers.NativePrimeSignedCycleKernel

/-! # Full phase-twisted native row square kernel -/

set_option autoImplicit false
set_option Elab.async false

namespace PrimeFactorOscillations.FiniteFieldIntegerSignature

theorem native_phase_row_unsigned_product_positive (P : Finset Nat)
    (hP : forall p : Nat, Membership.mem P p -> Nat.Prime p)
    (A B : Finset (Prod Nat Nat))
    (hA : A <= nativePrimeVertexEdges P) (hB : B <= nativePrimeVertexEdges P) :
    0 < A.prod (fun e => e.1 * (e.2 - e.1)) *
      B.prod (fun e => e.2 * (e.2 - e.1)) := by
  rw [native_gap_row_product_powers P A B hA hB]
  apply Finset.prod_pos
  intro x hx
  exact pow_pos (native_gap_basis_value_positive P hP x hx) _

theorem native_twisted_signed_row_product_isSquare_iff (P : Finset Nat)
    (hP : forall p : Nat, Membership.mem P p -> Nat.Prime p)
    (hind : nativePrimeVertexGapIndependent P)
    (A B : Finset (Prod Nat Nat))
    (hA : A <= nativePrimeVertexEdges P) (hB : B <= nativePrimeVertexEdges P) (b : Nat) :
    IsSquare ((-1 : Int) ^ b * nativeSignedRowProduct A B) <->
      And (A = B) (And
        (forall p : Nat, Membership.mem P p -> nativePrimeVertexCycleDegree A p % 2 = 0)
        ((b + A.card) % 2 = 0)) := by
  let D := A.prod (fun e => e.1 * (e.2 - e.1)) *
    B.prod (fun e => e.2 * (e.2 - e.1))
  have hD : 0 < D := native_phase_row_unsigned_product_positive P hP A B hA hB
  have hfactor : (-1 : Int) ^ b * nativeSignedRowProduct A B =
      (-1 : Int) ^ (b + A.card) * (D : Int) := by
    rw [native_signed_row_product_factorization, pow_add]
    dsimp only [D]
    ring
  have hNat : IsSquare D <-> And (A = B)
      (forall p : Nat, Membership.mem P p -> nativePrimeVertexCycleDegree A p % 2 = 0) :=
    native_gap_row_product_square_iff P hP hind A B hA hB
  rw [hfactor, native_signed_positive_cast_square_iff D hD (b + A.card), hNat]
  constructor
  . intro h
    exact And.intro h.1.1 (And.intro h.1.2 h.2)
  . intro h
    exact And.intro (And.intro h.1 h.2.1) h.2.2

theorem native_negative_signed_row_product_isSquare_iff (P : Finset Nat)
    (hP : forall p : Nat, Membership.mem P p -> Nat.Prime p)
    (hind : nativePrimeVertexGapIndependent P)
    (A B : Finset (Prod Nat Nat))
    (hA : A <= nativePrimeVertexEdges P) (hB : B <= nativePrimeVertexEdges P) :
    IsSquare (-nativeSignedRowProduct A B) <->
      And (A = B) (And
        (forall p : Nat, Membership.mem P p -> nativePrimeVertexCycleDegree A p % 2 = 0)
        (A.card % 2 = 1)) := by
  have hpar : (1 + A.card) % 2 = 0 <-> A.card % 2 = 1 := by omega
  have h := native_twisted_signed_row_product_isSquare_iff P hP hind A B hA hB 1
  simpa only [pow_one, neg_one_mul, hpar] using h

end PrimeFactorOscillations.FiniteFieldIntegerSignature

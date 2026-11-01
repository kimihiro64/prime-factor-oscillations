/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.NativePrimeUniversalCycles

/-! # Diagonal square relations are universal for actual prime vertices

All gap factors are squared on a diagonal mask. Distinct actual primes
then read every vertex incidence parity, without gap independence.
-/

set_option autoImplicit false
set_option Elab.async false

namespace PrimeFactorOscillations.FiniteFieldIntegerSignature

theorem native_vertex_endpoint_product (P : Finset Nat)
    (C : Finset (Prod Nat Nat)) (f : Prod Nat Nat -> Nat)
    (hf : forall e : Prod Nat Nat, Membership.mem C e -> Membership.mem P (f e)) :
    C.prod f = P.prod (fun p => p ^ (C.filter (fun e => f e = p)).card) := by
  classical
  symm
  calc
    _ = P.prod (fun p => (C.filter (fun e => f e = p)).prod f) := by
      apply Finset.prod_congr rfl
      intro p _
      rw [<- Finset.prod_const]
      apply Finset.prod_congr rfl
      intro e he
      exact (Finset.mem_filter.mp he).2.symm
    _ = _ := Finset.prod_fiberwise_of_maps_to hf f

theorem native_diagonal_natural_product (P : Finset Nat)
    (C : Finset (Prod Nat Nat)) (hC : C <= nativePrimeVertexEdges P) :
    C.prod (fun e => e.1 * (e.2 - e.1)) *
        C.prod (fun e => e.2 * (e.2 - e.1)) =
      (C.prod (fun e => e.2 - e.1)) ^ 2 *
        P.prod (fun p => p ^ nativePrimeVertexCycleDegree C p) := by
  classical
  have hl : forall e : Prod Nat Nat, Membership.mem C e -> Membership.mem P e.1 :=
    fun e he => ((native_gap_edges_mem_iff P e).mp (hC he)).1
  have hu : forall e : Prod Nat Nat, Membership.mem C e -> Membership.mem P e.2 :=
    fun e he => ((native_gap_edges_mem_iff P e).mp (hC he)).2.1
  have hv : C.prod Prod.fst * C.prod Prod.snd =
      P.prod (fun p => p ^ nativePrimeVertexCycleDegree C p) := by
    rw [native_vertex_endpoint_product P C Prod.fst hl,
      native_vertex_endpoint_product P C Prod.snd hu, <- Finset.prod_mul_distrib]
    apply Finset.prod_congr rfl
    intro p _
    exact (pow_add p _ _).symm
  calc
    _ = (C.prod (fun e => e.2 - e.1)) ^ 2 *
        (C.prod Prod.fst * C.prod Prod.snd) := by
      rw [Finset.prod_mul_distrib, Finset.prod_mul_distrib]
      ring
    _ = _ := by rw [hv]

theorem native_prime_power_product_valuation (P : Finset Nat)
    (hP : forall p : Nat, Membership.mem P p -> Nat.Prime p)
    (n : Nat -> Nat) (p : Nat) (hp : Membership.mem P p) :
    (P.prod (fun q => q ^ n q)).factorization p = n p := by
  classical
  rw [Nat.factorization_prod_apply (fun q hq => pow_ne_zero _ (hP q hq).ne_zero)]
  calc
    _ = (p ^ n p).factorization p := by
      apply Finset.sum_eq_single p
      . intro q hq hqp
        rw [Nat.factorization_pow, (hP q hq).factorization]
        simp [Ne.symm hqp]
      . intro hn
        exact False.elim (hn hp)
    _ = n p := by
      rw [Nat.factorization_pow, (hP p hp).factorization]
      simp

theorem native_prime_power_product_even_of_square (P : Finset Nat)
    (hP : forall p : Nat, Membership.mem P p -> Nat.Prime p)
    (n : Nat -> Nat) (hsq : IsSquare (P.prod (fun p => p ^ n p))) :
    forall p : Nat, Membership.mem P p -> n p % 2 = 0 := by
  classical
  have hpos : 0 < P.prod (fun p => p ^ n p) :=
    Finset.prod_pos (fun p hp => pow_pos (hP p hp).pos _)
  choose k hk using hsq
  have hk0 : Not (k = 0) := by
    intro hz
    rw [hk, hz, zero_mul] at hpos
    omega
  intro p hp
  have hfac := congrArg (fun a : Nat => a.factorization p) hk
  rw [native_prime_power_product_valuation P hP n p hp,
    Nat.factorization_mul hk0 hk0] at hfac
  simp only [Finsupp.add_apply] at hfac
  omega

theorem native_signed_diagonal_isSquare_iff (P : Finset Nat)
    (hP : forall p : Nat, Membership.mem P p -> Nat.Prime p)
    (C : Finset (Prod Nat Nat)) (hC : C <= nativePrimeVertexEdges P) :
    IsSquare (nativeSignedRowProduct C C) <->
      And (forall p : Nat, Membership.mem P p -> nativePrimeVertexCycleDegree C p % 2 = 0)
        (C.card % 2 = 0) := by
  constructor
  . intro hsq
    have hcard : C.card % 2 = 0 := by
      by_contra hn
      have hodd : C.card % 2 = 1 := by omega
      have hneg := native_signed_paired_row_product_neg_of_odd P hP C hC hodd
      choose k hk using hsq
      have hnon : 0 <= nativeSignedRowProduct C C := by
        rw [hk]
        exact mul_self_nonneg k
      exact (not_le_of_gt hneg) hnon
    have he : C.card = 2 * (C.card / 2) := by omega
    have hpower : (-1 : Int) ^ C.card = 1 := by
      rw [he, pow_mul]
      norm_num
    have hInt : IsSquare
        ((C.prod (fun e => e.1 * (e.2 - e.1)) *
          C.prod (fun e => e.2 * (e.2 - e.1)) : Nat) : Int) := by
      simpa only [native_signed_row_product_factorization, hpower, one_mul] using hsq
    have hNat : IsSquare
        (C.prod (fun e => e.1 * (e.2 - e.1)) *
          C.prod (fun e => e.2 * (e.2 - e.1))) := by
      choose k hk using hInt
      refine Exists.intro k.natAbs ?_
      have hh := congrArg Int.natAbs hk
      simpa only [Int.natAbs_natCast, Int.natAbs_mul] using hh
    rw [native_diagonal_natural_product P C hC] at hNat
    let Q := C.prod (fun e => e.2 - e.1)
    have hQ : 0 < Q := Finset.prod_pos (fun e he =>
      Nat.sub_pos_of_lt ((native_gap_edges_mem_iff P e).mp (hC he)).2.2)
    have hvertex : IsSquare (P.prod (fun p => p ^ nativePrimeVertexCycleDegree C p)) := by
      have hwhole : IsSquare ((Q * Q) *
          P.prod (fun p => p ^ nativePrimeVertexCycleDegree C p)) := by
        simpa only [Q, pow_two] using hNat
      have hx := Nat.isSquare_mul_trans_of_pos (a := 1) (b := Q * Q)
        (c := P.prod (fun p => p ^ nativePrimeVertexCycleDegree C p))
        (Nat.mul_pos hQ hQ) (Exists.intro Q (by simp)) hwhole
      simpa only [one_mul] using hx
    exact And.intro
      (native_prime_power_product_even_of_square P hP
        (fun p => nativePrimeVertexCycleDegree C p) hvertex) hcard
  . intro h
    exact native_signed_cycle_product_isSquare P C hC h.1 h.2

end PrimeFactorOscillations.FiniteFieldIntegerSignature

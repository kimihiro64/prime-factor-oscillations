/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Assembly.FiniteFieldNativeRowFibres
import PrimeFactorOscillations.Definitions.NativePrimeVertexExtension
import PrimeFactorOscillations.Mathlib.Data.Nat.IsSquareTrans

/-! # Complete collision control for a new largest prime vertex

The old/new upper row is excluded by prime endpoint recovery.
The other three rows retain their complete signed integer polynomials.
-/

set_option autoImplicit false
set_option Elab.async false

namespace PrimeFactorOscillations.FiniteFieldIntegerSignature

theorem native_prime_vertex_new_old_compatible (P : Finset Nat) (q : Nat)
    (hP : forall p : Nat, Membership.mem P p -> Nat.Prime p)
    (hq : Nat.Prime q) (hlarge : forall p : Nat, Membership.mem P p -> p < q)
    (hclear : nativePrimeVertexExtensionClear P q)
    (p n m : Nat) (hp : Membership.mem P p)
    (hn : Membership.mem P n) (hm : Membership.mem P m) (hnm : n < m) :
    nativePrimePairSquareCompatible (p, q - p) (n, m - n) := by
  unfold nativePrimePairSquareCompatible
  constructor
  . intro hs
    have hi := hs.map (Nat.castRingHom Int)
    have heq :
        (Nat.castRingHom Int) (((q - p) * p) * ((m - n) * n)) =
          (((p * n * (m - n) : Nat) : Int) * ((q : Int) - (p : Int))) := by
      change (((q - p) * p * ((m - n) * n) : Nat) : Int) = _
      simp only [Nat.cast_mul, Nat.cast_sub (hlarge p hp).le, Nat.cast_sub hnm.le]
      ring
    rw [heq] at hi
    exact hclear.1 p hp n hn m hm hnm hi
  . intro hs
    have hqeq : p + (q - p) = q := Nat.add_sub_of_le (hlarge p hp).le
    have hmeq : n + (m - n) = m := Nat.add_sub_of_le hnm.le
    have hrow : IsSquare ((q - p) * (m - n) * (p + (q - p)) * (n + (m - n))) := by
      simpa only [mul_assoc, mul_comm, mul_left_comm] using hs
    have heq := (native_square_rows_recover_endpoints p (q - p) n (m - n)
      (hP p hp) (by simpa only [hqeq] using hq)
      (hP n hn) (by simpa only [hmeq] using hP m hm)
      (Nat.sub_pos_of_lt (hlarge p hp)) (Nat.sub_pos_of_lt hnm)).2 hrow
    rw [hqeq, hmeq] at heq
    have hmq := hlarge m hm
    omega

theorem native_prime_vertex_new_new_compatible (P : Finset Nat) (q : Nat)
    (hq : Nat.Prime q) (hlarge : forall p : Nat, Membership.mem P p -> p < q)
    (hclear : nativePrimeVertexExtensionClear P q)
    (p r : Nat) (hp : Membership.mem P p) (hr : Membership.mem P r)
    (hpr : Not (p = r)) :
    nativePrimePairSquareCompatible (p, q - p) (r, q - r) := by
  unfold nativePrimePairSquareCompatible
  constructor
  . intro hs
    have hi := hs.map (Nat.castRingHom Int)
    have heq :
        (Nat.castRingHom Int) (((q - p) * p) * ((q - r) * r)) =
          (((p * r : Nat) : Int) * ((q : Int) - (p : Int)) *
            ((q : Int) - (r : Int))) := by
      change (((q - p) * p * ((q - r) * r) : Nat) : Int) = _
      simp only [Nat.cast_mul, Nat.cast_sub (hlarge p hp).le,
        Nat.cast_sub (hlarge r hr).le]
      ring
    rw [heq] at hi
    exact hclear.2.1 p hp r hr hpr hi
  . intro hs
    have hqeq : p + (q - p) = q := Nat.add_sub_of_le (hlarge p hp).le
    have hreq : r + (q - r) = q := Nat.add_sub_of_le (hlarge r hr).le
    have hprod : IsSquare (((q - p) * (q - r)) * (q * q)) := by
      simpa only [hqeq, hreq, mul_assoc, mul_comm, mul_left_comm] using hs
    have hself : IsSquare ((q * q) * 1) := Exists.intro q (by ring)
    have hc : IsSquare ((q - p) * (q - r)) := by
      simpa only [mul_one] using Nat.isSquare_mul_trans_of_pos
        (Nat.mul_pos hq.pos hq.pos) hprod hself
    have hi := hc.map (Nat.castRingHom Int)
    have heq : (Nat.castRingHom Int) ((q - p) * (q - r)) =
        ((q : Int) - (p : Int)) * ((q : Int) - (r : Int)) := by
      change (((q - p) * (q - r) : Nat) : Int) = _
      simp only [Nat.cast_mul, Nat.cast_sub (hlarge p hp).le,
        Nat.cast_sub (hlarge r hr).le]
    rw [heq] at hi
    exact hclear.2.2 p hp r hr hpr hi

theorem native_prime_vertex_clear_insertion_flat (P : Finset Nat) (q : Nat)
    (hP : forall p : Nat, Membership.mem P p -> Nat.Prime p)
    (hflat : nativePrimeVertexSquareFlat P) (hq : Nat.Prime q)
    (hlarge : forall p : Nat, Membership.mem P p -> p < q)
    (hclear : nativePrimeVertexExtensionClear P q) :
    nativePrimeVertexSquareFlat (insert q P) := by
  have hlower (a b : Nat) (ha : Membership.mem (insert q P) a)
      (hb : Membership.mem (insert q P) b) (hab : a < b) : Membership.mem P a := by
    rcases Finset.mem_insert.mp ha with heq | haP
    . subst a
      rcases Finset.mem_insert.mp hb with heq | hbP
      . omega
      . have hless := hlarge b hbP
        omega
    . exact haP
  intro p hp b hb hpb r hr d hd hrd hdistinct
  have hpP := hlower p b hp hb hpb
  have hrP := hlower r d hr hd hrd
  rcases Finset.mem_insert.mp hb with hbq | hbP
  . subst b
    rcases Finset.mem_insert.mp hd with hdq | hdP
    . subst d
      apply native_prime_vertex_new_new_compatible P q hq hlarge hclear p r hpP hrP
      intro heq
      exact hdistinct (And.intro heq rfl)
    . exact native_prime_vertex_new_old_compatible P q hP hq hlarge hclear
        p r d hpP hrP hdP hrd
  . rcases Finset.mem_insert.mp hd with hdq | hdP
    . subst d
      have hcomp := native_prime_vertex_new_old_compatible P q hP hq hlarge hclear
        r p b hrP hpP hbP hpb
      unfold nativePrimePairSquareCompatible at hcomp
      unfold nativePrimePairSquareCompatible
      simpa only [mul_comm, mul_left_comm, mul_assoc] using hcomp
    . exact hflat p hpP b hbP hpb r hrP d hdP hrd hdistinct

end PrimeFactorOscillations.FiniteFieldIntegerSignature

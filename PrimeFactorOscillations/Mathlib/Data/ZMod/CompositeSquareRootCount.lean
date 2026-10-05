/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.ZMod.QuotientRing
import PrimeFactorOscillations.Mathlib.Data.ZMod.IntervalResidueCount
import PrimeFactorOscillations.Mathlib.Data.ZMod.PrimeSquareRootCount

/-!
# Square-root counts under finite Chinese remaindering

Square-root counts factor exactly over pairwise coprime moduli.
For x^2 + c*b^(2*h), an odd prime p contributes at most p roots modulo
p^2 when p divides c*b, and at most two otherwise. The coefficient c,
base b and exponent h remain parameters throughout the composite bound.
-/

set_option autoImplicit false
set_option Elab.async false

namespace ZMod

/-- Square-root counts multiply over a finite family of coprime moduli. -/
theorem card_sq_roots_prod {I : Type*} [Fintype I]
    (m : I -> Nat) [forall i : I, NeZero (m i)]
    [NeZero (Finset.univ.prod m)]
    (hc : Pairwise (fun i j : I => (m i).Coprime (m j))) (a : Int) :
    (Finset.univ.filter fun x : ZMod (Finset.univ.prod m) =>
      x ^ 2 = (a : ZMod (Finset.univ.prod m))).card =
    Finset.univ.prod (fun i : I =>
      (Finset.univ.filter fun x : ZMod (m i) => x ^ 2 = (a : ZMod (m i))).card) := by
  classical
  let e := ZMod.prodEquivPi m hc
  let A := {x : ZMod (Finset.univ.prod m) // x ^ 2 = (a : ZMod (Finset.univ.prod m))}
  let B := fun i : I => {x : ZMod (m i) // x ^ 2 = (a : ZMod (m i))}
  let E : Equiv A (forall i : I, B i) := {
    toFun := fun x i => Subtype.mk (e x.val i) (by
      have he := congrArg e x.property
      have he' : (e x.val) ^ 2 = (a : forall j : I, ZMod (m j)) := by
        simpa only [map_pow, map_intCast] using he
      exact congrFun he' i)
    invFun := fun y => Subtype.mk (e.symm (fun i => (y i).val)) (by
      apply e.injective
      rw [map_pow, map_intCast, e.apply_symm_apply]
      funext i
      exact (y i).property)
    left_inv := by
      intro x
      apply Subtype.ext
      exact e.symm_apply_apply x.val
    right_inv := by
      intro y
      funext i
      apply Subtype.ext
      exact congrFun (e.apply_symm_apply (fun j => (y j).val)) i
  }
  have he : Fintype.card A = Finset.univ.prod (fun i => Fintype.card (B i)) :=
    (Fintype.card_congr E).trans Fintype.card_pi
  simpa only [A, B, Fintype.card_subtype] using he

/-- Retain the singular primes dividing the coefficient or powered variable. -/
theorem card_sparse_sq_roots_prime_sq_le
    (p : Nat) [Fact (Nat.Prime p)] (c b : Int) (h : Nat)
    (htwo : Not (p = 2)) :
    (Finset.univ.filter fun x : ZMod (p ^ 2) =>
      x ^ 2 + (c : ZMod (p ^ 2)) * (b : ZMod (p ^ 2)) ^ (2 * h) = 0).card <=
      if Dvd.dvd (p : Int) (c * b) then p else 2 := by
  classical
  have hsame :
      (Finset.univ.filter fun x : ZMod (p ^ 2) =>
        x ^ 2 + (c : ZMod (p ^ 2)) * (b : ZMod (p ^ 2)) ^ (2 * h) = 0) =
      (Finset.univ.filter fun x : ZMod (p ^ 2) =>
        x ^ 2 = (-(c * b ^ (2 * h)) : Int)) := by
    apply Finset.ext
    intro x
    simp only [Finset.mem_filter, Finset.mem_univ, true_and,
      Int.cast_neg, Int.cast_mul, Int.cast_pow, eq_neg_iff_add_eq_zero]
  rw [hsame]
  by_cases hd : Dvd.dvd (p : Int) (c * b)
  case pos =>
    rw [ite_eq_left hd]
    exact card_sq_roots_prime_sq_le p _ htwo
  case neg =>
    rw [ite_eq_right hd]
    apply card_unit_sq_roots_prime_sq_le_two p _ htwo
    intro hz
    have hp : Prime (p : Int) := Nat.prime_iff_prime_int.mp (Fact.out : Nat.Prime p)
    have hz' : Dvd.dvd (p : Int) (c * b ^ (2 * h)) := dvd_neg.mp hz
    cases hp.dvd_mul.mp hz' with
    | inl hpc => exact hd (dvd_mul_of_dvd_left hpc b)
    | inr hpb => exact hd (dvd_mul_of_dvd_right (hp.dvd_of_dvd_pow hpb) c)

/-- Composite square-divisor root bound with the singular-prime factors explicit. -/
theorem card_sparse_sq_roots_prod_prime_sq_le {I : Type*} [Fintype I]
    (p : I -> Nat) [forall i : I, Fact (Nat.Prime (p i))]
    [NeZero (Finset.univ.prod (fun i => p i ^ 2))]
    (hc : Pairwise (fun i j : I => (p i).Coprime (p j)))
    (htwo : forall i : I, Not (p i = 2)) (c b : Int) (h : Nat) :
    (Finset.univ.filter fun x : ZMod (Finset.univ.prod (fun i => p i ^ 2)) =>
      x ^ 2 + (c : ZMod (Finset.univ.prod (fun i => p i ^ 2))) *
        (b : ZMod (Finset.univ.prod (fun i => p i ^ 2))) ^ (2 * h) = 0).card <=
      Finset.univ.prod (fun i => if Dvd.dvd (p i : Int) (c * b) then p i else 2) := by
  classical
  have hcp : Pairwise (fun i j : I => (p i ^ 2).Coprime (p j ^ 2)) :=
    fun i j hij => (hc hij).pow 2 2
  have he := card_sq_roots_prod (fun i => p i ^ 2) hcp (-(c * b ^ (2 * h)))
  have he' :
      (Finset.univ.filter fun x : ZMod (Finset.univ.prod (fun i => p i ^ 2)) =>
        x ^ 2 + (c : ZMod (Finset.univ.prod (fun i => p i ^ 2))) *
          (b : ZMod (Finset.univ.prod (fun i => p i ^ 2))) ^ (2 * h) = 0).card =
      Finset.univ.prod (fun i => (Finset.univ.filter fun x : ZMod (p i ^ 2) =>
        x ^ 2 + (c : ZMod (p i ^ 2)) * (b : ZMod (p i ^ 2)) ^ (2 * h) = 0).card) := by
    simpa only [Int.cast_neg, Int.cast_mul, Int.cast_pow,
      eq_neg_iff_add_eq_zero] using he
  rw [he']
  exact Finset.prod_le_prod (fun i _ => card_sparse_sq_roots_prime_sq_le
    (p i) c b h (htwo i))

/-- Count sparse-family square divisibility in any inclusive integer block. -/
theorem card_sparse_dvd_range_succ_le {I : Type*} [Fintype I]
    (p : I -> Nat) [forall i : I, Fact (Nat.Prime (p i))]
    [NeZero (Finset.univ.prod (fun i => p i ^ 2))]
    (hc : Pairwise (fun i j : I => (p i).Coprime (p j)))
    (htwo : forall i : I, Not (p i = 2)) (s c b : Int) (h N : Nat) :
    ((Finset.range (N + 1)).filter fun n : Nat =>
      Dvd.dvd ((Finset.univ.prod (fun i => p i ^ 2) : Nat) : Int)
        ((s + n) ^ 2 + c * b ^ (2 * h))).card <=
      (N / Finset.univ.prod (fun i => p i ^ 2) + 1) *
        Finset.univ.prod (fun i => if Dvd.dvd (p i : Int) (c * b) then p i else 2) := by
  classical
  let q := Finset.univ.prod (fun i => p i ^ 2)
  let R : Finset (ZMod q) := Finset.univ.filter
    (fun x => x ^ 2 + (c : ZMod q) * (b : ZMod q) ^ (2 * h) = 0)
  have hsub :
      ((Finset.range (N + 1)).filter fun n : Nat =>
        Dvd.dvd (q : Int) ((s + n) ^ 2 + c * b ^ (2 * h))) <=
      ((Finset.range (N + 1)).filter fun n : Nat =>
        Membership.mem R ((n : ZMod q) + (s : ZMod q))) := by
    intro n hn
    have hd := (Finset.mem_filter.mp hn).2
    have hz := (ZMod.intCast_zmod_eq_zero_iff_dvd
      ((s + n) ^ 2 + c * b ^ (2 * h)) q).mpr hd
    apply Finset.mem_filter.mpr
    refine And.intro (Finset.mem_filter.mp hn).1 ?_
    apply Finset.mem_filter.mpr
    refine And.intro (Finset.mem_univ _) ?_
    simpa only [Int.cast_add, Int.cast_pow, Int.cast_mul,
      Int.cast_natCast, add_comm (s : ZMod q) (n : ZMod q)] using hz
  calc
    _ <= ((Finset.range (N + 1)).filter fun n : Nat =>
        Membership.mem R ((n : ZMod q) + (s : ZMod q))).card := Finset.card_le_card hsub
    _ <= (N / q + 1) * R.card := card_filter_range_succ_add_mem_le q N (s : ZMod q) R
    _ <= (N / q + 1) *
        Finset.univ.prod (fun i => if Dvd.dvd (p i : Int) (c * b) then p i else 2) :=
      Nat.mul_le_mul_left _ (card_sparse_sq_roots_prod_prime_sq_le p hc htwo c b h)

end ZMod

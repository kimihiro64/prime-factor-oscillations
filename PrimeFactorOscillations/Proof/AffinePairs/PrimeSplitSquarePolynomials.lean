/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Mathlib.Data.Nat.SplitSquareCertificate
import PrimeFactorOscillations.Proof.AffinePairs.FiniteEventProbability
import PrimeFactorOscillations.Proof.AffinePairs.PrimeSquarePolynomials

/-! # Prime square sparsity for split products of arbitrary fixed degree

The roots form a nonempty finite set and the leading coefficient is positive.
Natural differences agree with the usual split polynomial above the fixed
root bound; every smaller input belongs to an explicitly bounded event.
-/

set_option autoImplicit false
set_option Elab.async false

namespace PrimeFactorOscillations

open scoped Classical
attribute [local instance] Classical.propDecidable

theorem tendsto_prime_split_product_square_values_zero
    (A : Finset Nat) (c : Nat) (hA : A.Nonempty) (hc : 0 < c) :
    Filter.Tendsto (fun N : Nat => primeEventProbability N
      (fun q => IsSquare (c * A.prod (fun a => q - a))))
        Filter.atTop (nhds 0) := by
  choose a ha using hA
  choose B hB using A.finite_toSet.bddAbove
  let D : Nat := c * (A.erase a).prod (fun b => (b - a) + (a - b))
  have hD : 0 < D := by
    apply Nat.mul_pos hc
    apply Finset.prod_pos
    intro b hb
    have hne := (Finset.mem_erase.mp hb).1
    omega
  let I : Type := D.divisors
  let F : Option I -> Nat -> Prop
    | none, q => q <= B
    | some i, q => IsSquare ((i.val : Int) * ((q : Int) - (a : Int)))
  have hEach : forall i : Option I,
      Filter.Tendsto (fun N : Nat => primeEventProbability N (F i))
        Filter.atTop (nhds 0) := by
    intro i
    cases i with
    | none => exact tendsto_prime_probability_bounded_zero B
    | some i =>
      have hdiv : Dvd.dvd i.val D := (Nat.mem_divisors.mp i.property).1
      have hi0 : Not (i.val = 0) := by
        intro hz
        have hDz : D = 0 := by simpa only [hz, zero_dvd_iff] using hdiv
        exact (Nat.ne_of_gt hD) hDz
      have hipos : 0 < i.val := by omega
      simpa only [prime_filter_ratio_eq_probability, F] using
        tendsto_prime_affine_square_values_zero i.val a hipos
  have hImp : forall q : Nat, IsSquare (c * A.prod (fun b => q - b)) ->
      exists i : Option I, F i q := by
    intro q hq
    by_cases hle : q <= B
    . exact Exists.intro none hle
    . have hlarge : forall b : Nat, Membership.mem A b -> b < q := by
        intro b hb
        exact (hB hb).trans_lt (lt_of_not_ge hle)
      choose d hd using Nat.split_square_has_root_difference_divisor A a c q ha hc hlarge hq
      let i : I := Subtype.mk d (Nat.mem_divisors.mpr (And.intro hd.2.1 (Nat.ne_of_gt hD)))
      choose w hw using hd.2.2
      have hcast : ((d * (q - a) : Nat) : Int) = (w : Int) * (w : Int) := by
        exact_mod_cast hw
      have hqa : a <= q := (hlarge a ha).le
      have hint : IsSquare ((d : Int) * ((q : Int) - (a : Int))) :=
        Exists.intro (w : Int) (by
          simpa only [Nat.cast_mul, Nat.cast_sub hqa] using hcast)
      exact Exists.intro (some i) hint
  exact tendsto_prime_probability_zero_of_imp
    (fun q => IsSquare (c * A.prod (fun a => q - a)))
    (fun q => exists i : Option I, F i q) hImp
    (tendsto_prime_probability_finite_union_zero F hEach)

end PrimeFactorOscillations

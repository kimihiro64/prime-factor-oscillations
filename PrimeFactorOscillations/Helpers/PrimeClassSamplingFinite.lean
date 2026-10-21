/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Nat.GCD.BigOperators
import Mathlib.Data.Nat.Prime.Basic
import PrimeFactorOscillations.Helpers.PrimeClassSamplingFloor

/-!
# Exact finite prime-support sampling

The generating polynomial of the literal integer sample is expanded over
all subsets of a finite set of distinct primes. The prime-product divisor
condition and every floor endpoint are retained. This is the exact finite
arithmetic input for the uniform coefficient-error estimate.
-/

set_option autoImplicit false
set_option Elab.async false

namespace PrimeFactorOscillations.PrimeClassSampling

universe u

theorem primeSupport_prod_dvd_iff
    (s : Finset Nat) (hprime : forall p, Membership.mem s p -> Nat.Prime p)
    (m : Nat) :
    Dvd.dvd (s.prod (fun p => p)) m <->
      forall p, Membership.mem s p -> Dvd.dvd p m := by
  constructor
  case mp =>
    intro h p hp
    exact dvd_trans (Finset.dvd_prod_of_mem (fun q : Nat => q) hp) h
  case mpr =>
    intro hall
    have hbuild : forall t : Finset Nat,
        (forall p, Membership.mem t p -> Nat.Prime p) ->
        (forall p, Membership.mem t p -> Dvd.dvd p m) ->
        Dvd.dvd (t.prod (fun p => p)) m := by
      intro t
      induction t using Finset.induction_on with
      | empty =>
          intro ht hd
          simp
      | @insert p t hpt ih =>
          intro ht hd
          have hpprime := ht p (Finset.mem_insert_self p t)
          have htprime : forall q, Membership.mem t q -> Nat.Prime q :=
            fun q hq => ht q (Finset.mem_insert_of_mem hq)
          have htdiv : forall q, Membership.mem t q -> Dvd.dvd q m :=
            fun q hq => hd q (Finset.mem_insert_of_mem hq)
          have hcop : Nat.Coprime p (t.prod (fun q => q)) := by
            apply Nat.coprime_prod_right_iff.mpr
            intro q hq
            apply hpprime.coprime_iff_not_dvd.mpr
            intro hdiv
            have heq : p = q :=
              (Nat.prime_dvd_prime_iff_eq hpprime (htprime q hq)).mp hdiv
            apply hpt
            rw [heq]
            exact hq
          rw [Finset.prod_insert hpt]
          exact hcop.mul_dvd_of_dvd_of_dvd
            (hd p (Finset.mem_insert_self p t)) (ih htprime htdiv)
    exact hbuild s hprime hall

theorem primeSupport_generating_powerset
    {R : Type u} [CommRing R]
    (s : Finset Nat) (hprime : forall p, Membership.mem s p -> Nat.Prime p)
    (m : Nat) (z : R) :
    z ^ (s.filter (fun p => Dvd.dvd p m)).card =
      s.powerset.sum (fun t => (z - 1) ^ t.card *
        (if Dvd.dvd (t.prod (fun p => p)) m then 1 else 0)) := by
  classical
  let f : Nat -> R := fun p => if Dvd.dvd p m then z - 1 else 0
  have hleft : z ^ (s.filter (fun p => Dvd.dvd p m)).card =
      s.prod (fun p => if Dvd.dvd p m then z else 1) := by
    rw [<- Finset.prod_const z, Finset.prod_filter]
  have hfactor : forall p,
      (if Dvd.dvd p m then z else 1) = f p + 1 := by
    intro p
    by_cases hp : Dvd.dvd p m <;> simp [f, hp]
  calc
    z ^ (s.filter (fun p => Dvd.dvd p m)).card =
        s.prod (fun p => if Dvd.dvd p m then z else 1) := hleft
    _ = s.prod (fun p => f p + 1) := by
      apply Finset.prod_congr rfl
      intro p hp
      exact hfactor p
    _ = s.powerset.sum (fun t => t.prod f) := Finset.prod_add_one s
    _ = s.powerset.sum (fun t => (z - 1) ^ t.card *
        (if Dvd.dvd (t.prod (fun p => p)) m then 1 else 0)) := by
      apply Finset.sum_congr rfl
      intro t ht
      have htprime : forall p, Membership.mem t p -> Nat.Prime p :=
        fun p hp => hprime p ((Finset.mem_powerset.mp ht) hp)
      have hiff := primeSupport_prod_dvd_iff t htprime m
      by_cases hall : forall p, Membership.mem t p -> Dvd.dvd p m
      case pos =>
        rw [ite_eq_left (hiff.mpr hall), mul_one]
        calc
          t.prod f = t.prod (fun _ => z - 1) := by
            apply Finset.prod_congr rfl
            intro p hp
            exact ite_eq_left (hall p hp)
          _ = (z - 1) ^ t.card := Finset.prod_const _
      case neg =>
        have hnot : Not (Dvd.dvd (t.prod (fun p => p)) m) := fun h => hall (hiff.mp h)
        rw [ite_eq_right hnot, mul_zero]
        have hex : Exists (fun p => And (Membership.mem t p) (Not (Dvd.dvd p m))) := by
          by_contra hnone
          apply hall
          intro p hp
          by_contra hdiv
          exact hnone (Exists.intro p (And.intro hp hdiv))
        cases hex with
        | intro p hp =>
            apply Finset.prod_eq_zero hp.1
            exact ite_eq_right hp.2

theorem finitePrimeSupport_sampling_identity
    {R : Type u} [CommRing R]
    (s : Finset Nat) (hprime : forall p, Membership.mem s p -> Nat.Prime p)
    (N : Nat) (z : R) :
    (Finset.Icc 1 N).sum (fun m =>
      z ^ (s.filter (fun p => Dvd.dvd p m)).card) =
      s.powerset.sum (fun t => (z - 1) ^ t.card *
        ((N / t.prod (fun p => p) : Nat) : R)) := by
  classical
  calc
    (Finset.Icc 1 N).sum (fun m =>
        z ^ (s.filter (fun p => Dvd.dvd p m)).card) =
        (Finset.Icc 1 N).sum (fun m => s.powerset.sum
          (fun t => (z - 1) ^ t.card *
            (if Dvd.dvd (t.prod (fun p => p)) m then 1 else 0))) := by
      apply Finset.sum_congr rfl
      intro m hm
      exact primeSupport_generating_powerset s hprime m z
    _ = s.powerset.sum (fun t => (Finset.Icc 1 N).sum
        (fun m => (z - 1) ^ t.card *
          (if Dvd.dvd (t.prod (fun p => p)) m then 1 else 0))) := Finset.sum_comm
    _ = s.powerset.sum (fun t => (z - 1) ^ t.card *
        ((N / t.prod (fun p => p) : Nat) : R)) := by
      apply Finset.sum_congr rfl
      intro t ht
      have hprodpos : 0 < t.prod (fun p => p) := by
        apply Finset.prod_pos
        intro p hp
        exact (hprime p ((Finset.mem_powerset.mp ht) hp)).pos
      rw [<- Finset.mul_sum, Finset.sum_boole,
        card_positive_multiples N (t.prod (fun p => p)) hprodpos]

end PrimeFactorOscillations.PrimeClassSampling

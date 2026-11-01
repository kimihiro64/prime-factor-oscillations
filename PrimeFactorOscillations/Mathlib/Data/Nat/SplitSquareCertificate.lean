/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import Lean.Elab.Tactic.Omega
import Mathlib.Tactic.Ring
import PrimeFactorOscillations.Mathlib.Data.Nat.SquareProductSupport

/-! # A fixed divisor certificate for square values of split products

A selected shifted factor has a square-class representative dividing the
fixed leading coefficient times all its nonzero root differences.
-/

set_option autoImplicit false
set_option Elab.async false

namespace Nat

theorem dvd_root_difference_of_dvd_shifts (p q a b : Nat)
    (ha : a <= q) (hb : b <= q)
    (hpa : Dvd.dvd p (q - a)) (hpb : Dvd.dvd p (q - b)) :
    Dvd.dvd p ((a - b) + (b - a)) := by
  choose u hu using hpa
  choose v hv using hpb
  by_cases hab : a <= b
  . refine Exists.intro (u - v) ?_
    have heq : (a - b) + (b - a) = (q - a) - (q - b) := by omega
    rw [heq, hu, hv, Nat.mul_sub]
  . refine Exists.intro (v - u) ?_
    have heq : (a - b) + (b - a) = (q - b) - (q - a) := by omega
    rw [heq, hu, hv, Nat.mul_sub]

theorem split_square_has_root_difference_divisor (A : Finset Nat) (a c q : Nat)
    (ha : Membership.mem A a) (hc : 0 < c)
    (hlarge : forall b : Nat, Membership.mem A b -> b < q)
    (hsq : IsSquare (c * A.prod (fun b => q - b))) :
    exists d : Nat, And (0 < d)
      (And (Dvd.dvd d (c * (A.erase a).prod (fun b => (b - a) + (a - b))))
        (IsSquare (d * (q - a)))) := by
  let n := c * (A.erase a).prod (fun b => q - b)
  let D := c * (A.erase a).prod (fun b => (b - a) + (a - b))
  have hm : 0 < q - a := Nat.sub_pos_of_lt (hlarge a ha)
  have hn : 0 < n := by
    apply Nat.mul_pos hc
    apply Finset.prod_pos
    intro b hb
    exact Nat.sub_pos_of_lt (hlarge b (Finset.mem_erase.mp hb).2)
  have hD : 0 < D := by
    apply Nat.mul_pos hc
    apply Finset.prod_pos
    intro b hb
    have hne := (Finset.mem_erase.mp hb).1
    omega
  have hprod : (q - a) * (A.erase a).prod (fun b => q - b) =
      A.prod (fun b => q - b) := Finset.mul_prod_erase A (fun b => q - b) ha
  have hmn : IsSquare ((q - a) * n) := by
    have heq : (q - a) * n = c * A.prod (fun b => q - b) := by
      dsimp only [n]
      rw [<- hprod]
      ring
    rw [heq]
    exact hsq
  apply exists_square_class_divisor_of_common_prime_support (q - a) n D hm hn hD hmn
  intro p hp hpm hpn
  change Dvd.dvd p (c * (A.erase a).prod (fun b => q - b)) at hpn
  rcases hp.dvd_mul.mp hpn with hpc | hprest
  . exact dvd_mul_of_dvd_left hpc _
  . choose b hb using (_root_.Prime.dvd_finsetProd_iff hp.prime (fun b => q - b)).mp hprest
    have hbq := hlarge b (Finset.mem_erase.mp hb.1).2
    have hdiff : Dvd.dvd p ((b - a) + (a - b)) :=
      dvd_root_difference_of_dvd_shifts p q b a hbq.le (hlarge a ha).le hb.2 hpm
    have htotal : Dvd.dvd p ((A.erase a).prod (fun b => (b - a) + (a - b))) :=
      dvd_trans hdiff (Finset.dvd_prod_of_mem (fun b => (b - a) + (a - b)) hb.1)
    exact dvd_mul_of_dvd_right htotal c

end Nat

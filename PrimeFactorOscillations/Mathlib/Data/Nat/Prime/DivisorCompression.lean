/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import Mathlib.NumberTheory.ArithmeticFunction.Misc
import PrimeFactorOscillations.Mathlib.Algebra.Order.BigOperators.Group.BalancedProduct

/-!
# Small divisors retaining divisor-function mass

Every positive natural has a divisor below its square root whose divisor
count, squared and doubled, bounds the original divisor count. Take half
of every prime exponent, then use a balanced product for the primes of
exponent one. The result includes repeated prime factors.
-/

set_option autoImplicit false

namespace Nat

private theorem prod_membership_indicator (s t : Finset Nat) (hst : t <= s)
    (w : Nat -> Nat) :
    s.prod (fun p => if Membership.mem t p then w p else 1) = t.prod w := by
  classical
  have hf : s.filter (fun p => Membership.mem t p) = t := by
    ext p
    simp only [Finset.mem_filter]
    exact Iff.intro (fun hp => hp.2) (fun hp => And.intro (hst hp) hp)
  simpa only [hf] using (Finset.prod_filter (s := s)
    (fun p => Membership.mem t p) w).symm

private theorem factorization_half_card_bound (e : Nat) :
    e + 1 <= (e / 2 + 1) ^ 2 * (if e = 1 then 2 else 1) := by
  by_cases he0 : e = 0
  case pos => simp [he0]
  case neg =>
    by_cases he1 : e = 1
    case pos => simp [he1]
    case neg =>
      have hk : 1 <= e / 2 := by omega
      have hsq : 1 <= (e / 2) * (e / 2) := Nat.mul_le_mul hk hk
      have he : e <= 2 * (e / 2) + 1 := by omega
      simp only [ite_eq_right he1, Nat.mul_one, pow_two, Nat.add_mul,
        Nat.mul_add, Nat.one_mul, Nat.mul_one]
      omega

/-- A positive natural has a divisor below its square root retaining enough
of its divisor count to give a quadratic bound with factor two. -/
theorem exists_dvd_sq_le_and_divisors_card_le_twice_sq
    {n : Nat} (hn : 0 < n) :
    Exists (fun d : Nat => And (Dvd.dvd d n)
      (And (d ^ 2 <= n) (n.divisors.card <= 2 * d.divisors.card ^ 2))) := by
  classical
  have hn0 : Not (n = 0) := Nat.ne_of_gt hn
  let S := n.primeFactors
  let e := n.factorization
  let R := S.filter (fun p => e p = 1)
  cases Finset.exists_subset_sq_prod_le_and_card R id with
  | intro t ht =>
    have htS : t <= S := by
      intro p hp
      exact (Finset.mem_filter.mp (ht.1 hp)).1
    have hte : forall p, Membership.mem t p -> e p = 1 := by
      intro p hp
      exact (Finset.mem_filter.mp (ht.1 hp)).2
    let f : Nat -> Nat := fun p => e p / 2 + if Membership.mem t p then 1 else 0
    have hfS : forall p, Not (f p = 0) -> Membership.mem S p := by
      intro p hp
      by_contra hnot
      have he0 : e p = 0 := by
        by_contra he
        have hs : Membership.mem e.support p := by
          simpa only [Finsupp.mem_support_iff] using he
        exact hnot (by simpa only [e, S, Nat.support_factorization] using hs)
      have hpt : Not (Membership.mem t p) := fun h => hnot (htS h)
      exact hp (by simp [f, he0, hpt])
    let g : Finsupp Nat Nat := Finsupp.onFinset S f hfS
    have hgp : forall p, g p = f p := by
      intro p
      rfl
    have hgS : g.support <= S := Finsupp.support_onFinset_subset
    have hge : g <= n.factorization := by
      intro p
      rw [hgp]
      change e p / 2 + (if Membership.mem t p then 1 else 0) <= e p
      by_cases hp : Membership.mem t p
      case pos => simp [hp, hte p hp]
      case neg =>
        simp only [ite_eq_right hp, Nat.add_zero]
        exact Nat.div_le_self (e p) 2
    let d := g.prod (fun p k => p ^ k)
    let B := S.prod (fun p => p ^ (e p / 2))
    let C := S.prod (fun p => e p / 2 + 1)
    have hdvd : Dvd.dvd d n := Nat.prod_pow_dvd_of_le_factorization hge
    have hd0 : Not (d = 0) := by
      intro hz
      exact hn0 (by simpa [hz] using hdvd)
    have hdfact : d.factorization = g :=
      Nat.factorization_prod_pow_eq_self_of_le_factorization hge
    have hdprod : d = S.prod (fun p => p ^ f p) := by
      simpa only [hgp] using
        (Finsupp.prod_of_support_subset g hgS (fun p k => p ^ k)
          (by intro p hp; exact pow_zero p))
    have hcardd : d.divisors.card = S.prod (fun p => f p + 1) := by
      calc
        d.divisors.card = d.factorization.prod (fun _ k => k + 1) := by
          rw [Nat.prod_factorization_eq_prod_primeFactors, Nat.card_divisors hd0]
        _ = g.prod (fun _ k => k + 1) := by rw [hdfact]
        _ = S.prod (fun p => f p + 1) := by
          simpa only [hgp] using
            (Finsupp.prod_of_support_subset g hgS (fun _ k => k + 1)
              (by intro p hp; rfl))
    have hnprod : S.prod (fun p => p ^ e p) = n := by
      exact (Nat.prod_factorization_eq_prod_primeFactors (n := n)
        (fun p k => p ^ k)).symm.trans (Nat.prod_factorization_pow_eq_self hn0)
    have hdfactor : d = B * t.prod id := by
      calc
        d = S.prod (fun p => p ^ f p) := hdprod
        _ = S.prod (fun p => p ^ (e p / 2) *
              (if Membership.mem t p then p else 1)) := by
          apply Finset.prod_congr rfl
          intro p hp
          by_cases hpt : Membership.mem t p
          case pos => simp [f, hpt, pow_succ]
          case neg => simp [f, hpt]
        _ = B * t.prod id := by
          rw [Finset.prod_mul_distrib]
          exact congrArg (fun x => B * x)
            (prod_membership_indicator S t htS (fun p => p))
    have hRprod : R.prod id = S.prod (fun p => if e p = 1 then p else 1) := by
      exact Finset.prod_filter (s := S) (fun p => e p = 1) id
    have hBineq : B ^ 2 * R.prod id <= n := by
      calc
        B ^ 2 * R.prod id =
            S.prod (fun p => (p ^ (e p / 2)) ^ 2 *
              (if e p = 1 then p else 1)) := by
          rw [Finset.prod_mul_distrib, Finset.prod_pow, hRprod]
        _ <= S.prod (fun p => p ^ e p) := by
          apply Finset.prod_le_prod
          intro p hp
          by_cases he1 : e p = 1
          case pos => simp [he1]
          case neg =>
            simp only [ite_eq_right he1, Nat.mul_one, <- pow_mul]
            apply Nat.pow_le_pow_right (Nat.mem_primeFactors.mp hp).1.pos
            omega
        _ = n := hnprod
    have hdsmall : d ^ 2 <= n := by
      calc
        d ^ 2 = (B * t.prod id) ^ 2 := by rw [hdfactor]
        _ = B ^ 2 * (t.prod id) ^ 2 := mul_pow B (t.prod id) 2
        _ <= B ^ 2 * R.prod id := Nat.mul_le_mul_left (B ^ 2) ht.2.1
        _ <= n := hBineq
    have hCd : d.divisors.card = C * 2 ^ t.card := by
      calc
        d.divisors.card = S.prod (fun p => f p + 1) := hcardd
        _ = S.prod (fun p => (e p / 2 + 1) *
              (if Membership.mem t p then 2 else 1)) := by
          apply Finset.prod_congr rfl
          intro p hp
          by_cases hpt : Membership.mem t p
          case pos => simp [f, hpt, hte p hpt]
          case neg => simp [f, hpt]
        _ = C * 2 ^ t.card := by
          rw [Finset.prod_mul_distrib,
            prod_membership_indicator S t htS (fun _ => 2), Finset.prod_const]
    have hRtwo : S.prod (fun p => if e p = 1 then 2 else 1) = 2 ^ R.card := by
      rw [<- Finset.prod_filter]
      exact Finset.prod_const 2
    have hncard : n.divisors.card <= C ^ 2 * 2 ^ R.card := by
      calc
        n.divisors.card = S.prod (fun p => e p + 1) := Nat.card_divisors hn0
        _ <= S.prod (fun p => (e p / 2 + 1) ^ 2 *
              (if e p = 1 then 2 else 1)) := by
          apply Finset.prod_le_prod
          intro p hp
          exact factorization_half_card_bound (e p)
        _ = C ^ 2 * 2 ^ R.card := by
          rw [Finset.prod_mul_distrib, Finset.prod_pow, hRtwo]
    have hcards : R.card <= t.card * 2 + 1 := by omega
    have htwopow : 2 ^ R.card <= 2 * (2 ^ t.card) ^ 2 := by
      calc
        2 ^ R.card <= 2 ^ (t.card * 2 + 1) :=
          Nat.pow_le_pow_right (by decide) hcards
        _ = 2 * (2 ^ t.card) ^ 2 := by
          rw [pow_add, pow_mul, pow_one, Nat.mul_comm]
    have hdcard : n.divisors.card <= 2 * d.divisors.card ^ 2 := by
      calc
        n.divisors.card <= C ^ 2 * 2 ^ R.card := hncard
        _ <= C ^ 2 * (2 * (2 ^ t.card) ^ 2) :=
          Nat.mul_le_mul_left (C ^ 2) htwopow
        _ = 2 * (C * 2 ^ t.card) ^ 2 := by
          rw [mul_pow]
          ac_rfl
        _ = 2 * d.divisors.card ^ 2 := by rw [hCd]
    exact Exists.intro d (And.intro hdvd (And.intro hdsmall hdcard))

end Nat

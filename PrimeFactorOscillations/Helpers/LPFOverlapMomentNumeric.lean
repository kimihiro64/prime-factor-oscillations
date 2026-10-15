/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.LPFOverlapEulerNumeric

/-!
# Numerical growing-order LPF singular moments

For primes at least five and moment order at least five, the complete
principal Euler product is bounded by (72 log(q+2))^q. The high-prime
tail is retained before absorbing its uniform exp(3) bound.
-/

set_option autoImplicit false
set_option Elab.async false

namespace PrimeFactorOscillations.LPF

private theorem lpf_nonneg_product_compare (P : Finset Nat) (f g : Nat -> Real)
    (h0 : forall p, Membership.mem P p -> 0 <= f p)
    (hle : forall p, Membership.mem P p -> f p <= g p) :
    Finset.prod P f <= Finset.prod P g := by
  classical
  revert h0 hle
  induction P using Finset.induction_on with
  | empty => intro _ _; simp
  | @insert p P hp ih =>
    intro h0 hle
    have h0P := fun r hr => h0 r (Finset.mem_insert_of_mem hr)
    have hleP := fun r hr => hle r (Finset.mem_insert_of_mem hr)
    rw [Finset.prod_insert hp, Finset.prod_insert hp]
    exact mul_le_mul (hle p (Finset.mem_insert_self p P)) (ih h0P hleP)
      (Finset.prod_nonneg h0P)
      ((h0 p (Finset.mem_insert_self p P)).trans (hle p (Finset.mem_insert_self p P)))

theorem lpf_singular_euler_moment_numeric (P : Finset Nat) (N q : Nat)
    (hq : 5 <= q)
    (hP : forall p, Membership.mem P p -> And (Nat.Prime p) (And (5 <= p) (p < N))) :
    Finset.prod P (fun p => 1 + (singularFactor p ^ q - 1) / ((p : Real) - 1)) <=
      (72 * Real.log ((q : Real) + 2)) ^ q := by
  classical
  let L := P.filter (fun p => p <= 2 * q + 2)
  let H := P.filter (fun p => 2 * q + 2 < p)
  let F : Nat -> Real := fun p => 1 + (singularFactor p ^ q - 1) / ((p : Real) - 1)
  let A : Real := 36 * Real.log ((q : Real) + 2)
  have hF : forall p, Membership.mem P p -> 0 <= F p := by
    intro p hp
    have hpR : (5 : Real) <= (p : Real) := by exact_mod_cast (hP p hp).2.1
    exact add_nonneg zero_le_one (div_nonneg
      (singular_moment_weight_nonneg p q (by have h := (hP p hp).2.1; omega)) (by linarith))
  have hS : forall p, Membership.mem P p -> 0 <= singularFactor p := by
    intro p hp
    have hpR : (5 : Real) <= (p : Real) := by exact_mod_cast (hP p hp).2.1
    exact add_nonneg zero_le_one (one_div_nonneg.mpr (by linarith))
  have hLogQ : 0 <= Real.log ((q : Real) + 2) :=
    Real.log_nonneg (by have h : (0 : Real) <= (q : Real) := Nat.cast_nonneg q; linarith)
  have hA : 0 <= A := mul_nonneg (by norm_num) hLogQ
  have hLogCompare : Real.log ((max 5 (2 * q + 2) : Nat) : Real) <=
      2 * Real.log ((q : Real) + 2) := by
    have hqR : (5 : Real) <= (q : Real) := by exact_mod_cast hq
    have hInside : ((max 5 (2 * q + 2) : Nat) : Real) <= ((q : Real) + 2) ^ 2 := by
      simp only [Nat.cast_max, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat]
      apply max_le
      next => nlinarith only [hqR, sq_nonneg (q : Real)]
      next => nlinarith only [hqR, sq_nonneg (q : Real)]
    have h := Real.log_le_log
      (by positivity : (0 : Real) < ((max 5 (2 * q + 2) : Nat) : Real)) hInside
    rw [Real.log_pow] at h
    norm_num only [Nat.cast_ofNat] at h
    exact h
  have hLowPrime : Finset.prod L singularFactor <=
      18 * Real.log ((max 5 (2 * q + 2) : Nat) : Real) := by
    apply lpf_singular_prime_product_numeric L (max 5 (2 * q + 2)) (le_max_left _ _)
    intro p hp
    have hm := Finset.mem_filter.mp hp
    exact And.intro (hP p hm.1).1
      (And.intro (hP p hm.1).2.1 (hm.2.trans (le_max_right _ _)))
  have hLowCore : Finset.prod L singularFactor <= A := by
    have h := mul_le_mul_of_nonneg_left hLogCompare (by norm_num : (0 : Real) <= 18)
    exact hLowPrime.trans (by dsimp [A]; linarith only [h])
  have hProd0 : 0 <= Finset.prod L singularFactor :=
    Finset.prod_nonneg (fun p hp => hS p (Finset.mem_filter.mp hp).1)
  have hPower : (Finset.prod L singularFactor) ^ q <= A ^ q := by
    simpa only [Real.rpow_natCast] using
      Real.rpow_le_rpow hProd0 hLowCore (Nat.cast_nonneg q)
  have hLow : Finset.prod L F <= A ^ q := by
    calc
      _ <= Finset.prod L (fun p => singularFactor p ^ q) := by
        apply lpf_nonneg_product_compare
        next => exact fun p hp => hF p (Finset.mem_filter.mp hp).1
        next =>
          intro p hp
          have hpP := (Finset.mem_filter.mp hp).1
          have hpR : (5 : Real) <= (p : Real) := by exact_mod_cast (hP p hpP).2.1
          have hWeight := singular_moment_weight_nonneg p q
            (by have h := (hP p hpP).2.1; omega)
          have hDiv := div_le_div_of_nonneg_left hWeight (by norm_num : (0 : Real) < 1)
            (show (1 : Real) <= (p : Real) - 1 by linarith)
          simp only [div_one] at hDiv
          dsimp [F]
          linarith only [hDiv]
      _ = (Finset.prod L singularFactor) ^ q := Finset.prod_pow _ _ _
      _ <= A ^ q := hPower
  have hExp : Real.exp (3 : Real) <= 27 := by
    have hE1 : Real.exp 1 <= 3 := Real.exp_one_lt_three.le
    have hPower := Real.rpow_le_rpow (Real.exp_pos 1).le hE1
      (show (0 : Real) <= ((3 : Nat) : Real) by norm_num)
    simp only [Real.rpow_natCast] at hPower
    norm_num at hPower
    exact hPower
  have hTwoPow : (27 : Real) <= 2 ^ q := by
    have h := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : Real) <= 2)
      (show ((5 : Nat) : Real) <= (q : Real) by exact_mod_cast hq)
    simp only [Real.rpow_natCast] at h
    norm_num at h
    exact (by norm_num : (27 : Real) <= 32).trans h
  have hHigh : Finset.prod H F <= 2 ^ q := by
    have h := singular_high_euler_product_uniform_le H N q (by omega)
      (fun p hp => by
        have hm := Finset.mem_filter.mp hp
        exact And.intro hm.2 (hP p hm.1).2.2)
    exact h.trans (hExp.trans hTwoPow)
  have hSplit : Finset.prod P F = Finset.prod L F * Finset.prod H F := by
    dsimp [L, H]
    rw [Finset.prod_filter, Finset.prod_filter, <- Finset.prod_mul_distrib]
    apply Finset.prod_congr rfl
    intro p hp
    by_cases h : p <= 2 * q + 2
    next => simp only [F, ite_eq_left h, ite_eq_right (not_lt.mpr h), mul_one]
    next => simp only [F, ite_eq_right h, ite_eq_left (Nat.lt_of_not_ge h), one_mul]
  change Finset.prod P F <= _
  rw [hSplit]
  calc
    _ <= A ^ q * 2 ^ q := mul_le_mul hLow hHigh
      (Finset.prod_nonneg (fun p hp => hF p (Finset.mem_filter.mp hp).1)) (pow_nonneg hA q)
    _ = (A * 2) ^ q := (mul_pow _ _ _).symm
    _ = _ := by congr 1; dsimp [A]; ring

end PrimeFactorOscillations.LPF

/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.ModifiedLcmUpperBand

/-!
# A finite positive lower comparison for the zeta tail

Retain finitely many geometric thresholds. Their nonnegative power
increments telescope pointwise below the actual prime power.
-/

set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace PrimeFactorOscillations
open Filter

def lcmSquareTailIndicator (x : Real) : Nat.Primes -> Real :=
  @Set.indicator Nat.Primes Real _ {p : Nat.Primes | x < (p.val : Real)}
    (fun p : Nat.Primes => 1 / (p.val : Real) ^ (2 : Nat))

def lcmRealSquareTail (x : Real) : Real :=
  tsum (lcmSquareTailIndicator x)

def lcmTailStaircase (N q a : Real) (m : Nat) (p : Real) : Real :=
  N ^ a + (Finset.range m).sum (fun j =>
    if N * q ^ (j + 1) < p then
      (N * q ^ (j + 1)) ^ a - (N * q ^ j) ^ a else 0)

theorem lcmTailStaircase_bounds (N q a p : Real)
    (hN : 0 < N) (hq : 1 <= q) (ha : 0 <= a) (hNp : N <= p) (m : Nat) :
    lcmTailStaircase N q a m p <= (N * q ^ m) ^ a /\
      lcmTailStaircase N q a m p <= p ^ a := by
  have hq0 : 0 <= q := (by norm_num : (0 : Real) <= 1).trans hq
  induction m with
  | zero =>
    simp only [lcmTailStaircase, Finset.sum_range_zero, add_zero, pow_zero, mul_one]
    exact And.intro le_rfl (Real.rpow_le_rpow hN.le hNp ha)
  | succ m ih =>
    have hStep : N * q ^ m <= N * q ^ (m + 1) := by
      rw [pow_succ]
      have h := mul_le_mul_of_nonneg_left hq (mul_nonneg hN.le (pow_nonneg hq0 m))
      nlinarith only [h]
    have hPower := Real.rpow_le_rpow (mul_nonneg hN.le (pow_nonneg hq0 m)) hStep ha
    have hRec : lcmTailStaircase N q a (m + 1) p =
        lcmTailStaircase N q a m p +
          (if N * q ^ (m + 1) < p then
            (N * q ^ (m + 1)) ^ a - (N * q ^ m) ^ a else 0) := by
      simp only [lcmTailStaircase, Finset.sum_range_succ, add_assoc]
    rw [hRec]
    by_cases hCut : N * q ^ (m + 1) < p
    . rw [ite_eq_left hCut]
      have hBound : lcmTailStaircase N q a m p +
          ((N * q ^ (m + 1)) ^ a - (N * q ^ m) ^ a) <=
            (N * q ^ (m + 1)) ^ a := by linarith only [ih.1]
      exact And.intro hBound (hBound.trans
        (Real.rpow_le_rpow (mul_nonneg hN.le (pow_nonneg hq0 _)) hCut.le ha))
    . rw [ite_eq_right hCut, add_zero]
      exact And.intro (ih.1.trans hPower) ih.2

theorem lcmSquareTailIndicator_summable (x : Real) :
    Summable (lcmSquareTailIndicator x) := by
  have hs : Summable (fun p : Nat.Primes => 1 / (p.val : Real) ^ (2 : Nat)) :=
    summable_prime_reciprocal_sq
  exact @Summable.indicator Real Nat.Primes _ _ _
    (fun p : Nat.Primes => 1 / (p.val : Real) ^ (2 : Nat)) _ hs
    {p : Nat.Primes | x < (p.val : Real)}

theorem lcmRealSquareTail_nat (N : Nat) :
    lcmRealSquareTail (N : Real) = primeReciprocalSquareTail N := by
  classical
  have h : primeReciprocalSquareTail N =
      tsum (@Set.indicator Nat.Primes Real _ {p : Nat.Primes | N < p.val}
        (fun p : Nat.Primes => 1 / (p.val : Real) ^ (2 : Nat))) :=
    @tsum_subtype Real Nat.Primes _ _ {p : Nat.Primes | N < p.val}
      (fun p : Nat.Primes => 1 / (p.val : Real) ^ (2 : Nat))
  have hPred : {p : Nat.Primes | N < p.val} =
      {p : Nat.Primes | (N : Real) < (p.val : Real)} := by
    ext p
    simp only [Set.mem_ofPred_eq, Nat.cast_lt]
  change tsum (@Set.indicator Nat.Primes Real _ {p : Nat.Primes | (N : Real) < (p.val : Real)}
    (fun p : Nat.Primes => 1 / (p.val : Real) ^ (2 : Nat))) = _
  rw [<- hPred]
  exact h.symm

theorem lcmFiniteZetaTail_eq_real_indicator (k : Real) (N : Nat) :
    lcmFiniteZetaTail k (primeProfilePrefixSet N) =
      tsum (@Set.indicator Nat.Primes Real _
        {p : Nat.Primes | (N : Real) < (p.val : Real)}
        (fun p : Nat.Primes => -Real.log (1 - (p.val : Real) ^ (-k)))) := by
  classical
  have hPred : {p : Nat.Primes | Not (Membership.mem (primeProfilePrefixSet N) p)} =
      {p : Nat.Primes | (N : Real) < (p.val : Real)} := by
    ext p
    simp only [Set.mem_ofPred_eq, mem_primeProfilePrefixSet, not_le, Nat.cast_lt]
  have h : lcmFiniteZetaTail k (primeProfilePrefixSet N) =
      tsum (@Set.indicator Nat.Primes Real _
        {p : Nat.Primes | Not (Membership.mem (primeProfilePrefixSet N) p)}
        (fun p : Nat.Primes => -Real.log (1 - (p.val : Real) ^ (-k)))) :=
    @tsum_subtype Real Nat.Primes _ _
      {p : Nat.Primes | Not (Membership.mem (primeProfilePrefixSet N) p)}
      (fun p : Nat.Primes => -Real.log (1 - (p.val : Real) ^ (-k)))
  rw [hPred] at h
  exact h

theorem lcmTailStaircase_prime_log_le (N q k : Real) (m : Nat)
    (hN : 0 < N) (hq : 1 <= q) (hk : 1 < k) (hkTwo : k <= 2)
    (p : Nat.Primes) (hNp : N < (p.val : Real)) :
    lcmTailStaircase N q (2 - k) m (p.val : Real) / (p.val : Real) ^ (2 : Nat) <=
      -Real.log (1 - (p.val : Real) ^ (-k)) := by
  have hp : (0 : Real) < p := by exact_mod_cast p.property.pos
  have hBound := (lcmTailStaircase_bounds N q (2 - k) (p.val : Real)
    hN hq (by linarith) hNp.le m).2
  have hPower : (p.val : Real) ^ (2 - k) / (p.val : Real) ^ (2 : Nat) =
      (p.val : Real) ^ (-k) := by
    rw [<- Real.rpow_natCast, <- Real.rpow_sub hp]
    norm_num only [Nat.cast_ofNat]
    congr 1
    ring
  have hLog := Real.log_le_sub_one_of_pos (lcmPrimeEulerFactor_pos k (by linarith) p)
  calc
    _ <= (p.val : Real) ^ (2 - k) / (p.val : Real) ^ (2 : Nat) :=
      div_le_div_of_nonneg_right hBound (sq_nonneg _)
    _ = (p.val : Real) ^ (-k) := hPower
    _ <= _ := by linarith

theorem lcmFiniteZetaTail_staircase_lower
    (N m : Nat) (q k : Real) (hN : 0 < N) (hq : 1 <= q)
    (hk : 1 < k) (hkTwo : k <= 2) :
    (N : Real) ^ (2 - k) * primeReciprocalSquareTail N +
      (Finset.range m).sum (fun j =>
        (((N : Real) * q ^ (j + 1)) ^ (2 - k) -
          ((N : Real) * q ^ j) ^ (2 - k)) *
            lcmRealSquareTail ((N : Real) * q ^ (j + 1))) <=
      lcmFiniteZetaTail k (primeProfilePrefixSet N) := by
  classical
  let d : Nat -> Real := fun j =>
    ((N : Real) * q ^ (j + 1)) ^ (2 - k) - ((N : Real) * q ^ j) ^ (2 - k)
  let f : Nat.Primes -> Real := fun p =>
    (N : Real) ^ (2 - k) * lcmSquareTailIndicator (N : Real) p +
      (Finset.range m).sum (fun j =>
        d j * lcmSquareTailIndicator ((N : Real) * q ^ (j + 1)) p)
  let g : Nat.Primes -> Real := @Set.indicator Nat.Primes Real _
    {p : Nat.Primes | (N : Real) < (p.val : Real)}
    (fun p : Nat.Primes => -Real.log (1 - (p.val : Real) ^ (-k)))
  have hNReal : (0 : Real) < N := by exact_mod_cast hN
  have hq0 : 0 <= q := (by norm_num : (0 : Real) <= 1).trans hq
  have hPow (j : Nat) : (1 : Real) <= q ^ j := by
    induction j with
    | zero => simp only [pow_zero, le_refl]
    | succ j ih =>
      rw [pow_succ]
      nlinarith only [ih, hq, mul_nonneg (sub_nonneg.mpr ih) (sub_nonneg.mpr hq)]
  have hThreshold (j : Nat) : (N : Real) <= (N : Real) * q ^ j := by
    simpa only [mul_one] using mul_le_mul_of_nonneg_left (hPow j) hNReal.le
  have hBase := (lcmSquareTailIndicator_summable (N : Real)).mul_left ((N : Real) ^ (2 - k))
  have hTerm (j : Nat) := (lcmSquareTailIndicator_summable ((N : Real) * q ^ (j + 1))).mul_left (d j)
  have hTerms (r : Nat) : Summable (fun p : Nat.Primes =>
      (Finset.range r).sum (fun j =>
        d j * lcmSquareTailIndicator ((N : Real) * q ^ (j + 1)) p)) := by
    induction r with
    | zero => simpa only [Finset.sum_range_zero] using
        (summable_zero : Summable (fun _ : Nat.Primes => (0 : Real)))
    | succ r ih =>
      simpa only [Finset.sum_range_succ] using ih.add (hTerm r)
  have hf : Summable f := hBase.add (hTerms m)
  have hg : Summable g := by
    have hs : Summable (fun p : Nat.Primes => -Real.log (1 - (p.val : Real) ^ (-k))) :=
      lcmPrimeLog_summable k hk
    exact @Summable.indicator Real Nat.Primes _ _ _
      (fun p : Nat.Primes => -Real.log (1 - (p.val : Real) ^ (-k))) _ hs
      {p : Nat.Primes | (N : Real) < (p.val : Real)}
  have hPoint (p : Nat.Primes) : f p <= g p := by
    by_cases hNp : (N : Real) < (p.val : Real)
    . have hEq : f p =
          lcmTailStaircase (N : Real) q (2 - k) m (p.val : Real) / (p.val : Real) ^ (2 : Nat) := by
        simp only [f, d, lcmTailStaircase, lcmSquareTailIndicator, @Set.indicator_apply Nat.Primes Real _,
          Set.mem_ofPred_eq, ite_eq_left hNp,
          add_div, Finset.sum_div, ite_div, zero_div, mul_ite, mul_zero, mul_one_div]
      rw [hEq]
      simp only [g, @Set.indicator_apply Nat.Primes Real _, Set.mem_ofPred_eq,
        ite_eq_left hNp]
      exact lcmTailStaircase_prime_log_le _ _ _ _ hNReal hq hk hkTwo p hNp
    . have hCut (j : Nat) : Not ((N : Real) * q ^ (j + 1) < (p.val : Real)) :=
        not_lt_of_ge ((not_lt.mp hNp).trans (hThreshold (j + 1)))
      simp only [f, g, lcmSquareTailIndicator, @Set.indicator_apply Nat.Primes Real _,
        Set.mem_ofPred_eq, ite_eq_right hNp, ite_eq_right (hCut _),
        mul_zero, Finset.sum_const_zero, add_zero, le_refl]
  have hIneq := hf.tsum_le_tsum hPoint hg
  have hSwap := Summable.tsum_finsetSum (s := Finset.range m) (fun j _ => hTerm j)
  have hTotal : tsum f =
      (N : Real) ^ (2 - k) * lcmRealSquareTail (N : Real) +
        (Finset.range m).sum (fun j =>
          d j * lcmRealSquareTail ((N : Real) * q ^ (j + 1))) := by
    change tsum (fun p : Nat.Primes =>
      (N : Real) ^ (2 - k) * lcmSquareTailIndicator (N : Real) p +
        (Finset.range m).sum (fun j =>
          d j * lcmSquareTailIndicator ((N : Real) * q ^ (j + 1)) p)) = _
    rw [hBase.tsum_add (hTerms m), hSwap]
    simp only [tsum_mul_left, lcmRealSquareTail]
  rw [hTotal, lcmRealSquareTail_nat] at hIneq
  simpa only [d, g, <- lcmFiniteZetaTail_eq_real_indicator] using hIneq

end PrimeFactorOscillations

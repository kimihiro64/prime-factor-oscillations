/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.NormNum.Prime
import PrimeFactorOscillations.Helpers.LPFSieveDenominator
import PrimeFactorUnimodality.Helpers.Analytic.MertensProvider

/-!
# A checked prime-cutoff condition for the arithmetic sieve

The bounded-error first Mertens theorem supplies the logarithmic-mean estimate.
The old coarse sufficient test is retained for compatibility. After removing
2 and 3, the sharper prime-log bound has no additive constant. For K < 4,
z^4 <= Q retains the fraction 1 - K/4 of the complete sieve weight.
-/

namespace PrimeFactorOscillations.LPF

/-- The exact local mean is bounded uniformly for every subset of the prime cutoff. -/
theorem sieveLogarithmicMean_le_prime_cutoff (P : Finset Nat)
    (A : (p : Nat) -> Finset (ZMod p)) (z K : Nat) (hz : 1 <= z)
    (hP : forall p, Membership.mem P p -> And (Nat.Prime p) (p <= z))
    (hCard : forall p, Membership.mem P p -> (A p).card <= K) :
    sieveLogarithmicMean P A <=
      (K : Real) * (Real.log (z : Real) + Real.log 4 + 4) := by
  classical
  let R := (Finset.Ioc 0 z).filter Nat.Prime
  have hSub : P <= R := by
    intro p hp
    exact Finset.mem_filter.mpr
      (And.intro (Finset.mem_Ioc.mpr (And.intro (hP p hp).1.pos (hP p hp).2))
        (hP p hp).1)
  have hTerm : forall p, Membership.mem R p -> 0 <= Real.log (p : Real) / (p : Real) := by
    intro p hp
    have hpPrime := (Finset.mem_filter.mp hp).2
    apply div_nonneg
    next => exact Real.log_nonneg (by exact_mod_cast le_of_lt hpPrime.one_lt)
    next => exact Nat.cast_nonneg p
  have hSubset : Finset.sum P (fun p => Real.log (p : Real) / (p : Real)) <=
      Finset.sum R (fun p => Real.log (p : Real) / (p : Real)) :=
    Finset.sum_le_sum_of_subset_of_nonneg hSub (fun p hp _ => hTerm p hp)
  have hMertens := Mertens.sum_log_prime_div_eq_log (x := (z : Real))
    (by exact_mod_cast hz)
  simp only [Nat.floor_natCast] at hMertens
  have hFull : Finset.sum R (fun p => Real.log (p : Real) / (p : Real)) <=
      Real.log (z : Real) + Real.log 4 + 4 := by
    have hAbs := le_abs_self
      (Finset.sum R (fun p => Real.log (p : Real) / (p : Real)) - Real.log (z : Real))
    linarith
  calc
    _ <= Finset.sum P (fun p => (K : Real) * (Real.log (p : Real) / (p : Real))) := by
      apply Finset.sum_le_sum
      intro p hp
      have h := mul_le_mul_of_nonneg_right
        (show ((A p).card : Real) <= (K : Real) by exact_mod_cast hCard p hp)
        (hTerm p (hSub hp))
      convert h using 1 <;> ring
    _ = (K : Real) * Finset.sum P (fun p => Real.log (p : Real) / (p : Real)) :=
      (Finset.mul_sum _ _ _).symm
    _ <= _ := mul_le_mul_of_nonneg_left (hSubset.trans hFull) (Nat.cast_nonneg K)

/-- Integer power cutoffs discharge the log-mean condition without a distribution premise. -/
theorem sieveLogarithmicMean_half_of_prime_cutoff (P : Finset Nat)
    (A : (p : Nat) -> Finset (ZMod p)) (z K Q : Nat)
    (hz : 1 <= z)
    (hP : forall p, Membership.mem P p -> And (Nat.Prime p) (p <= z))
    (hCard : forall p, Membership.mem P p -> (A p).card <= K)
    (hLarge : Real.log 4 + 4 <= Real.log (z : Real))
    (hPower : z ^ (4 * K) <= Q) :
    sieveLogarithmicMean P A <= Real.log (Q : Real) / 2 := by
  have hzPos : 0 < z := lt_of_lt_of_le Nat.zero_lt_one hz
  have hLog := Real.log_le_log
    (show (0 : Real) < ((z ^ (4 * K) : Nat) : Real) by
      exact_mod_cast pow_pos hzPos (4 * K))
    (show ((z ^ (4 * K) : Nat) : Real) <= (Q : Real) by exact_mod_cast hPower)
  simp only [Nat.cast_pow, Real.log_pow, Nat.cast_mul, Nat.cast_ofNat] at hLog
  have hLargeScaled := mul_le_mul_of_nonneg_left hLarge (Nat.cast_nonneg K)
  have hMean := sieveLogarithmicMean_le_prime_cutoff P A z K hz hP hCard
  nlinarith

/-- A fully arithmetic finite upper sieve at a prescribed integer prime cutoff. -/
theorem sieve_card_le_euler_of_prime_cutoff (P : Finset Nat)
    (A : (p : Nat) -> Finset (ZMod p)) (z K : Nat)
    (hP : forall p, Membership.mem P p -> And (Nat.Prime p) (p <= z))
    (hA : forall p, Membership.mem P p -> And (0 < (A p).card) ((A p).card < p))
    (hCard : forall p, Membership.mem P p -> (A p).card <= K)
    (X : Finset Nat) {N Q : Nat} (hN : 0 < N) (hQ : 1 < Q)
    (hX : X <= Finset.range N)
    (hAvoid : forall k, Membership.mem X k ->
      forall p, Membership.mem P p -> Not (Membership.mem (A p) (k : ZMod p)))
    (hz : 1 <= z) (hLarge : Real.log 4 + 4 <= Real.log (z : Real))
    (hPower : z ^ (4 * K) <= Q) :
    (X.card : Real) <= 72 * ((N : Real) + (Q : Real) ^ 2) / sieveEulerProduct P A :=
  sieve_card_le_euler P A (fun p hp => (hP p hp).1) hA X hN hQ hX hAvoid
    (sieveLogarithmicMean_half_of_prime_cutoff P A z K Q hz
      hP hCard hLarge hPower)

def sharpPrimeCutoff (z : Nat) : Finset Nat :=
  (Finset.Ioc 0 z).filter (fun p => And (Nat.Prime p) (5 <= p))

theorem mem_sharpPrimeCutoff {z p : Nat} :
    Membership.mem (sharpPrimeCutoff z) p <-> Nat.Prime p /\ 5 <= p /\ p <= z := by
  simp only [sharpPrimeCutoff, Finset.mem_filter, Finset.mem_Ioc]
  constructor
  next => intro h; exact And.intro h.2.1 (And.intro h.2.2 h.1.2)
  next => intro h; exact And.intro (And.intro (by omega) h.2.2) (And.intro h.1 h.2.1)

theorem log_two_le_five_sevenths : Real.log 2 <= (5 / 7 : Real) := by
  have hp : (2 : Real) <= ((29 : Real) / 28) ^ 20 := by norm_num
  have hl := Real.log_le_log (show (0 : Real) < 2 by norm_num) hp
  rw [Real.log_pow] at hl
  have hr := Real.log_le_sub_one_of_pos (show (0 : Real) < (29 : Real) / 28 by norm_num)
  norm_num at hl hr
  linarith

theorem one_le_log_three : (1 : Real) <= Real.log 3 := by
  have h := Real.log_le_log (Real.exp_pos 1) (le_of_lt Real.exp_one_lt_three)
  simpa only [Real.log_exp] using h

theorem floor_error_integral_le (x : Real) (hx : 1 <= x) :
    intervalIntegral (fun t : Real => (t - (Nat.floor t : Real) - 1 / 2) / t)
      1 x MeasureTheory.volume <= Real.log x / 2 := by
  classical
  let f := fun t : Real => (t - (Nat.floor t : Real) - 1 / 2) / t
  have hCont : ContinuousOn (fun t : Real => 1 / t) (Set.uIcc 1 x) := by
    apply continuousOn_const.div continuousOn_id
    intro t ht
    rw [Set.uIcc_of_le hx] at ht
    change Not (t = 0)
    exact ne_of_gt (by linarith [(Set.mem_Icc.mp ht).1])
  have hg : IntervalIntegrable (fun t : Real => 1 / t) MeasureTheory.volume 1 x :=
    hCont.intervalIntegrable
  have hDeriv : forall t, Membership.mem (Set.uIcc 1 x) t ->
      HasDerivAt Real.log (1 / t) t := by
    intro t ht
    rw [Set.uIcc_of_le hx] at ht
    have htPos : 0 < t := by linarith [(Set.mem_Icc.mp ht).1]
    simpa only [one_div] using Real.hasDerivAt_log (ne_of_gt htPos)
  have hInv : intervalIntegral (fun t : Real => 1 / t) 1 x MeasureTheory.volume =
      Real.log x := by
    have h := intervalIntegral.integral_eq_sub_of_hasDerivAt hDeriv hg
    simpa only [Real.log_one, sub_zero] using h
  by_cases hf : IntervalIntegrable f MeasureTheory.volume 1 x
  next =>
    have hBound := intervalIntegral.integral_mono_on hx hf (hg.const_mul (1 / 2 : Real))
      (fun t ht => by
        have htPos : 0 < t := by linarith [(Set.mem_Icc.mp ht).1]
        have hFloor := Nat.lt_floor_add_one t
        have hNum : t - (Nat.floor t : Real) - 1 / 2 <= (1 / 2 : Real) := by linarith
        have hDiv := div_le_div_of_nonneg_right hNum (le_of_lt htPos)
        change (t - (Nat.floor t : Real) - 1 / 2) / t <= (1 / 2 : Real) * (1 / t)
        convert hDiv using 1 <;> ring)
    rw [intervalIntegral.integral_const_mul, hInv] at hBound
    simpa only [f, div_eq_mul_inv, one_mul, mul_comm] using hBound
  next =>
    rw [intervalIntegral.integral_undef hf]
    exact div_nonneg (Real.log_nonneg hx) (by norm_num)

theorem log_factorial_stirling_upper (n : Nat) (hn : 1 <= n) :
    Finset.sum (Finset.Ioc 0 n) (fun k => Real.log (k : Real)) <=
      (n : Real) * Real.log (n : Real) - (n : Real) + Real.log (n : Real) + 1 := by
  have hnR : (1 : Real) <= (n : Real) := by exact_mod_cast hn
  have he := Mertens.sum_log_eq (x := (n : Real)) hnR
  have hi := floor_error_integral_le (n : Real) hnR
  simp only [Nat.floor_natCast] at he
  nlinarith

theorem prime_log_sum_floor_bound (n : Nat) :
    (n : Real) * Finset.sum ((Finset.Ioc 0 n).filter Nat.Prime)
      (fun p => Real.log (p : Real) / (p : Real)) <=
      Finset.sum (Finset.Ioc 0 n) (fun k => Real.log (k : Real)) + Chebyshev.theta n := by
  classical
  let R := (Finset.Ioc 0 n).filter Nat.Prime
  have hTerm : forall p, Membership.mem R p ->
      (n : Real) * (Real.log (p : Real) / (p : Real)) <=
        ArithmeticFunction.vonMangoldt p * (Nat.floor ((n : Real) / (p : Real)) : Real) +
          Real.log (p : Real) := by
    intro p hp
    have hpr : Nat.Prime p := (Finset.mem_filter.mp hp).2
    have hLog : 0 <= Real.log (p : Real) := Real.log_nonneg
      (by exact_mod_cast le_of_lt hpr.one_lt)
    have h := mul_le_mul_of_nonneg_right
      (Nat.lt_floor_add_one ((n : Real) / (p : Real))).le hLog
    rw [ArithmeticFunction.vonMangoldt_apply_prime hpr]
    convert h using 1 <;> ring
  have hTheta : Finset.sum R (fun p => Real.log (p : Real)) = Chebyshev.theta n := by
    have h := Chebyshev.theta.eq_1 (n : Real)
    simpa only [Nat.floor_natCast] using h.symm
  have hMangoldt : Finset.sum (Finset.Ioc 0 n)
      (fun d => ArithmeticFunction.vonMangoldt d *
        (Nat.floor ((n : Real) / (d : Real)) : Real)) =
        Finset.sum (Finset.Ioc 0 n) (fun k => Real.log (k : Real)) := by
    have h := Mertens.sum_log_eq_sum_mangoldt (x := (n : Real))
    simpa only [Nat.floor_natCast] using h.symm
  calc
    _ = Finset.sum R (fun p => (n : Real) * (Real.log (p : Real) / (p : Real))) :=
      Finset.mul_sum _ _ _
    _ <= Finset.sum R (fun p => ArithmeticFunction.vonMangoldt p *
        (Nat.floor ((n : Real) / (p : Real)) : Real) + Real.log (p : Real)) :=
      Finset.sum_le_sum hTerm
    _ = Finset.sum R (fun p => ArithmeticFunction.vonMangoldt p *
        (Nat.floor ((n : Real) / (p : Real)) : Real)) + Chebyshev.theta n := by
      rw [Finset.sum_add_distrib, hTheta]
    _ <= _ := by
      rw [<- hMangoldt]
      apply _root_.add_le_add
      next =>
        apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
        intro d hd hNot
        exact mul_nonneg (show (0 : Real) <= ArithmeticFunction.vonMangoldt d from
          ArithmeticFunction.vonMangoldt_nonneg) (Nat.cast_nonneg _)
      next => exact le_refl _

theorem prime_log_sum_remove_two_three (n : Nat) (hn : 5 <= n) :
    Finset.sum ((Finset.Ioc 0 n).filter Nat.Prime)
      (fun p => Real.log (p : Real) / (p : Real)) =
      Real.log 2 / 2 + Real.log 3 / 3 +
        Finset.sum (sharpPrimeCutoff n) (fun p => Real.log (p : Real) / (p : Real)) := by
  classical
  have hSet : (Finset.Ioc 0 n).filter Nat.Prime = insert 2 (insert 3 (sharpPrimeCutoff n)) := by
    ext p
    simp only [Finset.mem_filter, Finset.mem_Ioc, Finset.mem_insert]
    constructor
    next =>
      intro hp
      by_cases h2 : p = 2
      next => exact Or.inl h2
      next =>
        by_cases h3 : p = 3
        next => exact Or.inr (Or.inl h3)
        next =>
          have hp2 := hp.2.two_le
          have hp4 : Not (p = 4) := by intro h; subst p; norm_num at hp
          exact Or.inr (Or.inr (mem_sharpPrimeCutoff.mpr
            (And.intro hp.2 (And.intro (by omega) hp.1.2))))
    next =>
      intro hp
      rcases hp with hp | hp
      next => subst p; norm_num; omega
      next =>
        rcases hp with hp | hp
        next => subst p; norm_num; omega
        next =>
          have h := mem_sharpPrimeCutoff.mp hp
          exact And.intro (And.intro (by omega) h.2.2) h.1
  have h2 : Not (Membership.mem (insert 3 (sharpPrimeCutoff n)) 2) := by
    simp only [Finset.mem_insert]
    intro h
    rcases h with h | h
    next => omega
    next => have h5 := (mem_sharpPrimeCutoff.mp h).2.1; omega
  have h3 : Not (Membership.mem (sharpPrimeCutoff n) 3) := by
    intro h
    have h5 := (mem_sharpPrimeCutoff.mp h).2.1
    omega
  rw [hSet, Finset.sum_insert h2, Finset.sum_insert h3]
  norm_num
  ring

theorem prime_log_sum_large_sharp (n : Nat) (hn : 16 <= n) :
    Finset.sum (sharpPrimeCutoff n) (fun p => Real.log (p : Real) / (p : Real)) <=
      Real.log (n : Real) := by
  have hnR : (16 : Real) <= (n : Real) := by exact_mod_cast hn
  have hnPos : (0 : Real) < (n : Real) := by linarith
  have hFloor := prime_log_sum_floor_bound n
  rw [prime_log_sum_remove_two_three n (by omega)] at hFloor
  have hFact := log_factorial_stirling_upper n (by omega)
  have hTheta := Chebyshev.theta_le_log4_mul_x (le_of_lt hnPos)
  have hFour : Real.log 4 = 2 * Real.log 2 := by
    rw [show (4 : Real) = 2 ^ 2 by norm_num, Real.log_pow]
    norm_num
  rw [hFour] at hTheta
  have ht := Real.log_le_sub_one_of_pos (div_pos hnPos (by norm_num : (0 : Real) < 8))
  rw [Real.log_div (ne_of_gt hnPos) (by norm_num)] at ht
  have hEight : Real.log 8 = 3 * Real.log 2 := by
    rw [show (8 : Real) = 2 ^ 3 by norm_num, Real.log_pow]
    norm_num
  rw [hEight] at ht
  have h2 := log_two_le_five_sevenths
  have h3 := one_le_log_three
  have h2Scaled := mul_le_mul_of_nonneg_left h2 (le_of_lt hnPos)
  have h3Scaled := mul_le_mul_of_nonneg_left h3 (le_of_lt hnPos)
  have hTarget : (n : Real) *
      Finset.sum (sharpPrimeCutoff n) (fun p => Real.log (p : Real) / (p : Real)) <=
        (n : Real) * Real.log (n : Real) := by
    nlinarith only [hFloor, hFact, hTheta, ht, h2, h2Scaled, h3Scaled, hnR]
  exact (mul_le_mul_iff_of_pos_left hnPos).mp hTarget

theorem prime_log_sum_sharp (n : Nat) (hn : 5 <= n) :
    Finset.sum (sharpPrimeCutoff n) (fun p => Real.log (p : Real) / (p : Real)) <=
      Real.log (n : Real) := by
  classical
  by_cases hLarge : 16 <= n
  next => exact prime_log_sum_large_sharp n hLarge
  next =>
    let F : Finset Nat := {5, 7, 11, 13}
    have hSub : sharpPrimeCutoff n <= F := by
      intro p hp
      have h := mem_sharpPrimeCutoff.mp hp
      have hpr := h.1
      have hp5 : 5 <= p := h.2.1
      have hp15 : p <= 15 := by omega
      interval_cases p <;> norm_num [F] at hpr <;> norm_num [F]
    have hRec : Finset.sum F (fun p => 1 / (p : Real)) <= (1 : Real) := by
      norm_num [F]
    have hSmallRec : Finset.sum (sharpPrimeCutoff n) (fun p => 1 / (p : Real)) <= 1 := by
      exact (Finset.sum_le_sum_of_subset_of_nonneg hSub
        (fun p _ _ => by positivity)).trans hRec
    have hLogN : 0 <= Real.log (n : Real) := Real.log_nonneg
      (by exact_mod_cast (show 1 <= n by omega))
    calc
      _ <= Finset.sum (sharpPrimeCutoff n)
          (fun p => Real.log (n : Real) * (1 / (p : Real))) := by
        apply Finset.sum_le_sum
        intro p hp
        have h := mem_sharpPrimeCutoff.mp hp
        have hpPos : (0 : Real) < (p : Real) := by exact_mod_cast h.1.pos
        have hLog := Real.log_le_log hpPos
          (show (p : Real) <= (n : Real) by exact_mod_cast h.2.2)
        have hDiv := div_le_div_of_nonneg_right hLog (le_of_lt hpPos)
        convert hDiv using 1 <;> ring
      _ = Real.log (n : Real) * Finset.sum (sharpPrimeCutoff n)
          (fun p => 1 / (p : Real)) := (Finset.mul_sum _ _ _).symm
      _ <= Real.log (n : Real) * 1 := mul_le_mul_of_nonneg_left hSmallRec hLogN
      _ = _ := by ring

theorem sieveLogarithmicMean_le_sharp (P : Finset Nat)
    (A : (p : Nat) -> Finset (ZMod p)) (z K : Nat) (hz : 5 <= z)
    (hP : forall p, Membership.mem P p -> Nat.Prime p /\ 5 <= p /\ p <= z)
    (hCard : forall p, Membership.mem P p -> (A p).card <= K) :
    sieveLogarithmicMean P A <= (K : Real) * Real.log (z : Real) := by
  classical
  have hSub : P <= sharpPrimeCutoff z := fun p hp => mem_sharpPrimeCutoff.mpr (hP p hp)
  have hTerm : forall p, Membership.mem P p ->
      ((A p).card : Real) / (p : Real) * Real.log (p : Real) <=
        (K : Real) * (Real.log (p : Real) / (p : Real)) := by
    intro p hp
    have hpPos : (0 : Real) < (p : Real) := by exact_mod_cast (hP p hp).1.pos
    have hpLog : 0 <= Real.log (p : Real) := Real.log_nonneg
      (by exact_mod_cast (show 1 <= p by have h := (hP p hp).2.1; omega))
    have hCardR : ((A p).card : Real) <= (K : Real) := by exact_mod_cast hCard p hp
    have h := mul_le_mul_of_nonneg_right
      (div_le_div_of_nonneg_right hCardR (le_of_lt hpPos)) hpLog
    convert h using 1 <;> ring
  have hSum : Finset.sum P (fun p => Real.log (p : Real) / (p : Real)) <=
      Real.log (z : Real) := by
    apply le_trans _ (prime_log_sum_sharp z hz)
    apply Finset.sum_le_sum_of_subset_of_nonneg hSub
    intro p hp hNot
    have h := mem_sharpPrimeCutoff.mp hp
    exact div_nonneg (Real.log_nonneg
      (by exact_mod_cast (show 1 <= p by omega))) (Nat.cast_nonneg p)
  calc
    _ <= Finset.sum P (fun p => (K : Real) * (Real.log (p : Real) / (p : Real))) :=
      Finset.sum_le_sum hTerm
    _ = (K : Real) * Finset.sum P (fun p => Real.log (p : Real) / (p : Real)) :=
      (Finset.mul_sum _ _ _).symm
    _ <= _ := mul_le_mul_of_nonneg_left hSum (Nat.cast_nonneg K)

theorem sieve_card_le_euler_of_sharp_cutoff (P : Finset Nat)
    (A : (p : Nat) -> Finset (ZMod p)) (z K : Nat) (hz : 5 <= z) (hK : K < 4)
    (hP : forall p, Membership.mem P p -> Nat.Prime p /\ 5 <= p /\ p <= z)
    (hA : forall p, Membership.mem P p -> And (0 < (A p).card) ((A p).card < p))
    (hCard : forall p, Membership.mem P p -> (A p).card <= K)
    (X : Finset Nat) {N Q : Nat} (hN : 0 < N) (hQ : 1 < Q)
    (hX : X <= Finset.range N)
    (hAvoid : forall k, Membership.mem X k ->
      forall p, Membership.mem P p -> Not (Membership.mem (A p) (k : ZMod p)))
    (hPower : z ^ 4 <= Q) :
    (X.card : Real) <= (36 / (1 - (K : Real) / 4)) *
      ((N : Real) + (Q : Real) ^ 2) / sieveEulerProduct P A := by
  have hzPos : (0 : Real) < (z : Real) := by exact_mod_cast (show 0 < z by omega)
  have hPowR : (z : Real) ^ 4 <= (Q : Real) := by exact_mod_cast hPower
  have hLog := Real.log_le_log (pow_pos hzPos 4) hPowR
  rw [Real.log_pow] at hLog
  have hMean := sieveLogarithmicMean_le_sharp P A z K hz hP hCard
  have hScale := mul_le_mul_of_nonneg_left hLog
    (div_nonneg (Nat.cast_nonneg K) (by norm_num : (0 : Real) <= 4))
  have hMeanQ : sieveLogarithmicMean P A <= (K : Real) / 4 * Real.log (Q : Real) := by
    norm_num at hScale
    nlinarith only [hMean, hScale]
  have hKR : (K : Real) < 4 := by exact_mod_cast hK
  exact sieve_card_le_euler_retained_fraction P A (fun p hp => (hP p hp).1)
    hA X hN hQ hX hAvoid ((K : Real) / 4) (by linarith) hMeanQ

end PrimeFactorOscillations.LPF

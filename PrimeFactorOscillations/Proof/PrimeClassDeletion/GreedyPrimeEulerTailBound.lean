/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Proof.PrimeClassDeletion.GreedyPrimeNicolasIntegral

/-!
# A quantitative selected Euler tail from the literal theta cap

All selected primes beyond the cutoff are partitioned into relative dyadic
shells. The cap bounds each shell's logarithmic mass; no RH input is used.
-/

set_option autoImplicit false
set_option Elab.async false

open Filter
open PrimeFactorOscillations.PrimeClassSampling
open Robin1984

namespace PrimeFactorOscillations.PrimeClassDeletion

private theorem greedyPrimeEulerTail_finite_bound
    (n : Nat) (hn : 2 <= n) (u : Finset Nat) :
    u.sum (fun p => -primeClassMertensTail greedyPrimeClass (n : Real) p) <=
      8 / ((n : Real) * Real.log (n : Real)) := by
  classical
  have hn0 : 0 < n := by omega
  have hN : (0 : Real) < n := Nat.cast_pos.mpr hn0
  have hL : 0 < Real.log (n : Real) :=
    Real.log_pos (by exact_mod_cast (show 1 < n by omega))
  let v := u.filter (fun p => And (Membership.mem greedyPrimeClass p) (n < p))
  let J := v.image (fun p => Nat.log 2 (p / n))
  let g : Nat -> Real := fun j => (4 / ((n : Real) * Real.log (n : Real))) * (1 / 2) ^ j
  have hg : HasSum g (8 / ((n : Real) * Real.log (n : Real))) := by
    have hGeo : HasSum (fun j : Nat => (1 / 2 : Real) ^ j) 2 := by
      convert hasSum_geometric_of_norm_lt_one
        (by norm_num : norm (1 / 2 : Real) < 1) using 1; norm_num
    convert hGeo.mul_left (4 / ((n : Real) * Real.log (n : Real))) using 1; ring
  have hTotal : J.sum g <= 8 / ((n : Real) * Real.log (n : Real)) := by
    rw [<- hg.tsum_eq]
    exact Summable.sum_le_tsum J
      (fun j _ => mul_nonneg (div_nonneg (by norm_num) (mul_pos hN hL).le)
        (pow_nonneg (by norm_num : (0 : Real) <= 1 / 2) j)) hg.summable
  have heq : u.sum (fun p => -primeClassMertensTail greedyPrimeClass (n : Real) p) =
      v.sum (fun p => -Mertens.M_eq_summand p) := by
    simp only [v, Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro p _
    by_cases h : And (Membership.mem greedyPrimeClass p) (n < p)
    case pos =>
      have hR : And (Membership.mem greedyPrimeClass p) ((n : Real) < p) :=
        And.intro h.1 (by exact_mod_cast h.2)
      simp only [primeClassMertensTail, ite_eq_left hR, ite_eq_left h]
    case neg =>
      have hR : Not (And (Membership.mem greedyPrimeClass p) ((n : Real) < p)) := by
        intro hR
        exact h (And.intro hR.1 (by exact_mod_cast hR.2))
      simp only [primeClassMertensTail, ite_eq_right hR, ite_eq_right h, neg_zero]
  rw [heq]
  rw [<- Finset.sum_fiberwise_of_maps_to
    (s := v) (t := J) (g := fun p => Nat.log 2 (p / n))
    (fun p hp => Finset.mem_image.mpr (Exists.intro p (And.intro hp rfl)))
    (fun p => -Mertens.M_eq_summand p)]
  apply le_trans (Finset.sum_le_sum (fun j _ => ?_)) hTotal
  let w := v.filter (fun p => Nat.log 2 (p / n) = j)
  let q : Real := 2 ^ j
  let Y : Nat := 2 ^ (j + 1) * n
  have hq : 0 < q := pow_pos (by norm_num) j
  have hBounds : forall p, Membership.mem w p ->
      And (2 ^ j * n <= p) (p < Y) := by
    intro p hp
    have hw := Finset.mem_filter.mp hp
    have hv := Finset.mem_filter.mp hw.1
    have hdiv : 0 < p / n := Nat.div_pos (Nat.le_of_lt hv.2.2) hn0
    have hLow := Nat.pow_log_le_self 2 (Nat.ne_of_gt hdiv)
    have hHigh := Nat.lt_pow_succ_log_self (by norm_num : 1 < 2) (p / n)
    rw [hw.2] at hLow hHigh
    exact And.intro
      ((Nat.mul_le_mul_right n hLow).trans (Nat.div_mul_le_self p n))
      ((Nat.div_lt_iff_lt_mul hn0).mp hHigh)
  have hsub : forall p, Membership.mem w p -> Membership.mem (primeClassPrefix greedyPrimeClass Y) p := by
    intro p hp
    have hw := Finset.mem_filter.mp hp
    have hv := Finset.mem_filter.mp hw.1
    have hs := hv.2.1
    change And (Nat.Prime p) (greedyPrimeIndices (Nat.count Nat.Prime p)) at hs
    exact (primeClassPrefix_mem_iff greedyPrimeClass Y p).mpr
      (And.intro hs.1.two_le (And.intro (hBounds p hp).2.le (And.intro hs.1 hv.2.1)))
  have hMass : (w.card : Real) * Real.log (n : Real) <= (Y : Real) := by
    calc
      (w.card : Real) * Real.log (n : Real) = w.sum (fun _ => Real.log (n : Real)) := by
        simp only [Finset.sum_const, nsmul_eq_mul]
      _ <= w.sum (fun p => Real.log (p : Real)) := by
        apply Finset.sum_le_sum
        intro p hp
        exact Real.log_le_log hN (by exact_mod_cast
          (Nat.le_of_lt (Finset.mem_filter.mp (Finset.mem_filter.mp hp).1).2.2))
      _ <= (primeClassPrefix greedyPrimeClass Y).sum (fun p => Real.log (p : Real)) := by
        apply Finset.sum_le_sum_of_subset_of_nonneg hsub
        intro p hp _
        have hm := (primeClassPrefix_mem_iff greedyPrimeClass Y p).mp hp
        exact Real.log_nonneg (by exact_mod_cast (show 1 <= p by omega))
      _ <= (Y : Real) := greedyPrimeClass_theta_le Y
  have hterm : forall p, Membership.mem w p ->
      -Mertens.M_eq_summand p <= 2 / (q * (n : Real)) ^ 2 := by
    intro p hp
    have hm := Mertens.M_eq_summand_bound p
    rw [abs_of_nonpos (mertensSummand_nonpos p)] at hm
    apply hm.trans
    have hpn : q * (n : Real) <= p := by
      dsimp only [q]
      exact_mod_cast (hBounds p hp).1
    exact div_le_div_of_nonneg_left (by norm_num)
      (pow_pos (mul_pos hq hN) 2)
      (by simpa only [pow_two] using
        mul_self_le_mul_self (mul_pos hq hN).le hpn)
  have hY : (Y : Real) = 2 * q * (n : Real) := by
    simp only [Y, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat, pow_succ, q]
    ring
  calc
    w.sum (fun p => -Mertens.M_eq_summand p) <=
        (w.card : Real) * (2 / (q * (n : Real)) ^ 2) := by
      simpa only [Finset.sum_const, nsmul_eq_mul] using
        Finset.sum_le_sum (fun p hp => hterm p hp)
    _ = ((w.card : Real) * Real.log (n : Real)) *
        (2 / ((q * (n : Real)) ^ 2 * Real.log (n : Real))) := by
      field_simp [hL.ne']
    _ <= (Y : Real) * (2 / ((q * (n : Real)) ^ 2 * Real.log (n : Real))) :=
      mul_le_mul_of_nonneg_right hMass
        (div_nonneg (by norm_num) (mul_nonneg (sq_nonneg _) hL.le))
    _ = g j := by
      rw [hY]
      have hPow : (1 / 2 : Real) ^ j = 1 / q := by
        simp only [div_pow, one_pow, q]
      dsimp only [g]
      rw [hPow]
      field_simp [hq.ne', hN.ne', hL.ne']; ring

theorem greedyPrimeNicolasEulerTail_nat_bound (n : Nat) (hn : 2 <= n) :
    greedyPrimeNicolasEulerTail (n : Real) <=
      8 / ((n : Real) * Real.log (n : Real)) := by
  have hsum : HasSum (fun p => -primeClassMertensTail greedyPrimeClass (n : Real) p)
      (greedyPrimeNicolasEulerTail (n : Real)) :=
    (primeClassMertensTail_summable greedyPrimeClass (n : Real)).hasSum.neg
  exact le_of_tendsto hsum (Filter.Eventually.of_forall
    (greedyPrimeEulerTail_finite_bound n hn))


theorem greedyPrimeNicolasEulerTail_real_bound (x : Real) (hx : 4 <= x) :
    greedyPrimeNicolasEulerTail x <= 32 / (x * Real.log x) := by
  classical
  let n := Nat.floor x
  have hx0 : 0 < x := by linarith only [hx]
  have hn : 2 <= n := Nat.le_floor (by norm_num; linarith only [hx])
  have hN : (0 : Real) < n := by exact_mod_cast (show 0 < n by omega)
  have hfloor : (n : Real) <= x := Nat.floor_le hx0.le
  have hfloorUpper : x < (n : Real) + 1 := Nat.lt_floor_add_one x
  have hhalf : x / 2 <= (n : Real) := by linarith only [hx, hfloorUpper]
  have hLx : 0 < Real.log x := Real.log_pos (by linarith only [hx])
  have hLn : 0 < Real.log (n : Real) :=
    Real.log_pos (by exact_mod_cast (show 1 < n by omega))
  have hlog4 : Real.log (4 : Real) = 2 * Real.log (2 : Real) := by
    rw [show (4 : Real) = 2 * 2 by norm_num, Real.log_mul (by norm_num) (by norm_num)]
    ring
  have hLogLarge := Real.log_le_log (by norm_num : (0 : Real) < 4) hx
  rw [hlog4] at hLogLarge
  have hLogHalf : Real.log x / 2 <= Real.log (n : Real) := by
    have h := Real.log_le_log (div_pos hx0 (by norm_num)) hhalf
    rw [Real.log_div hx0.ne' (by norm_num)] at h
    linarith only [h, hLogLarge]
  have hden : x * Real.log x <= 4 * ((n : Real) * Real.log (n : Real)) := by
    have h := mul_le_mul hhalf hLogHalf (by linarith only [hLx]) hN.le
    nlinarith only [h]
  have hCompare : 8 / ((n : Real) * Real.log (n : Real)) <=
      32 / (x * Real.log x) := by
    calc
      8 / ((n : Real) * Real.log (n : Real)) =
          32 / (4 * ((n : Real) * Real.log (n : Real))) := by
        field_simp; ring
      _ <= 32 / (x * Real.log x) :=
        div_le_div_of_nonneg_left (by norm_num) (mul_pos hx0 hLx) hden
  have hmono : forall p : Nat,
      -primeClassMertensTail greedyPrimeClass x p <=
        -primeClassMertensTail greedyPrimeClass (n : Real) p := by
    intro p
    by_cases h : And (Membership.mem greedyPrimeClass p) (x < (p : Real))
    case pos =>
      have hnP : And (Membership.mem greedyPrimeClass p) ((n : Real) < p) :=
        And.intro h.1 (hfloor.trans_lt h.2)
      simp only [primeClassMertensTail, ite_eq_left h, ite_eq_left hnP, le_refl]
    case neg =>
      simp only [primeClassMertensTail, ite_eq_right h, neg_zero]
      split_ifs
      case pos => exact neg_nonneg.mpr (mertensSummand_nonpos p)
      case neg => simp only [neg_zero, le_refl]
  have hsum : HasSum (fun p => -primeClassMertensTail greedyPrimeClass x p)
      (greedyPrimeNicolasEulerTail x) :=
    (primeClassMertensTail_summable greedyPrimeClass x).hasSum.neg
  apply le_trans _ hCompare
  apply le_of_tendsto hsum
  exact Filter.Eventually.of_forall (fun u =>
    (Finset.sum_le_sum (fun p _ => hmono p)).trans
      (greedyPrimeEulerTail_finite_bound n hn u))

theorem greedyPrimeCalibratedError_le_integral_add_log_tail
    (x : Real) (hx : 4 <= x)
    (hS : 1 < primeClassThetaReal greedyPrimeClass x) :
    greedyPrimeCalibratedError x <=
      greedyPrimeNicolasIntegral x + 32 / (x * Real.log x) := by
  have hSigned := greedyPrimeCalibratedError_le_integral_add_tail x
    (by linarith only [hx]) hS
  have hTail := greedyPrimeNicolasEulerTail_real_bound x hx
  linarith only [hSigned, hTail]

end PrimeFactorOscillations.PrimeClassDeletion

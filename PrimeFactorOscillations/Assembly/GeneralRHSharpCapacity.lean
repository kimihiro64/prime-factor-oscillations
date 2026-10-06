/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Assembly.GeneralRHAscentCapacity
import PrimeFactorOscillations.Helpers.PrimeProfileReferenceCapacity
import PrimeFactorOscillations.Helpers.PrimeProfileRootShift

/-!
# Sharp RH capacity at any eventual lower gap

The actual attained reversal maximum and last ascent use the same reference
root. Its first displacement and the resulting double-logarithmic count
bound retain the threshold H+1, with every constant chosen before the rank.
-/

set_option autoImplicit false
set_option Elab.async false
namespace PrimeFactorOscillations

theorem exists_ordinary_loglog_capacity_of_RH_gap_lower
    (H : Nat) (hGaps : exists Q : Nat, forall i : Nat,
      Q <= PrimeFactorUnimodality.primeAt i -> H <= PrimeFactorUnimodality.primeGap i)
    (hRH : RiemannHypothesis) :
    exists (c A C : Real) (K : Nat), 0 < c /\ 0 < A /\ 0 <= C /\ 2 <= K /\
      forall k : Nat, K <= k -> exists N i : Nat, exists u : Real,
        HasReversalNumber (ordinaryDensity k) N /\
        Real.exp (Real.exp (c * (k : Real))) <= (N : Real) /\
        ordinaryDensity k i < ordinaryDensity k (i + 1) /\
        (forall j : Nat, ordinaryDensity k j < ordinaryDensity k (j + 1) -> j <= i) /\
        Set.Ioo (((k - 1 : Nat) : Real) / ((H : Real) + 1) - A)
          (((k - 1 : Nat) : Real) / ((H : Real) + 1) + A) u /\
        Nat.factorialConvolution primeProfileRealCoefficient (k - 2) u /
          Nat.factorialConvolution primeProfileRealCoefficient (k - 1) u = (H : Real) + 1 /\
        Chebyshev.theta ((PrimeFactorUnimodality.primeAt i - 1 : Nat) : Real) <
          Real.exp (Real.exp (u - Real.eulerMascheroniConstant)) /\
        N <= primeThetaEndpointCount (Real.exp (Real.exp (u - Real.eulerMascheroniConstant))) /\
        abs (u - ((k - 1 : Nat) : Real) / ((H : Real) + 1) +
          deriv (fun x : Real => (primeProfile (x : Complex)).re) ((H : Real) + 1) /
            (primeProfile (((H : Real) + 1 : Real) : Complex)).re) <= C / ((k - 1 : Nat) : Real) /\
        Real.log (Real.log (N : Real)) <=
          ((k - 1 : Nat) : Real) / ((H : Real) + 1) - Real.eulerMascheroniConstant -
            deriv (fun x : Real => (primeProfile (x : Complex)).re) ((H : Real) + 1) /
              (primeProfile (((H : Real) + 1 : Real) : Complex)).re +
              (C + 32 * ((H : Real) + 1)) / ((k - 1 : Nat) : Real) := by
  let s : Real := (H : Real) + 1
  have hs : 0 < s := by dsimp [s]; positivity
  choose c A K0 hc hA hK0 hbase using
    exists_ordinary_last_ascent_and_capacity_of_RH_gap_lower H hGaps hRH
  choose C rD hC hrD hshiftBound using
    exists_primeProfile_reference_root_shift_bound s A hs hA.le
  choose rB hrB hcountB using
    exists_primeThetaEndpointCount_near_rank_loglog_error s A hs hA.le
  choose n0 hn0 using exists_nat_gt (2 * s * A)
  let K := max K0 (max (rD + 1) (max (rB + 1) (n0 + 2)))
  refine Exists.intro c (Exists.intro A (Exists.intro C (Exists.intro K
    (And.intro hc (And.intro hA (And.intro hC (And.intro ?_ ?_)))))))
  . exact hK0.trans (le_max_left _ _)
  . intro k hk
    have hk0 : K0 <= k := (max_le_iff.mp hk).1
    have hkD : rD + 1 <= k := (max_le_iff.mp (max_le_iff.mp hk).2).1
    have hkB : rB + 1 <= k := (max_le_iff.mp (max_le_iff.mp (max_le_iff.mp hk).2).2).1
    have hkn : n0 + 2 <= k := (max_le_iff.mp (max_le_iff.mp (max_le_iff.mp hk).2).2).2
    have hk2 : 2 <= k := hK0.trans hk0
    have hrD' : rD <= k - 1 := by omega
    have hrB' : rB <= k - 1 := by omega
    have hnR : (n0 : Real) < ((k - 1 : Nat) : Real) := by exact_mod_cast (show n0 < k - 1 by omega)
    have hrLarge : 2 * s * A < ((k - 1 : Nat) : Real) := hn0.trans hnR
    choose N i u hN hlo hi hlast hu heq htheta hcount hcapacity using hbase k hk0
    change Set.Ioo (((k - 1 : Nat) : Real) / s - A) (((k - 1 : Nat) : Real) / s + A) u at hu
    have hLow := mul_lt_mul_of_pos_right hu.1 hs
    have hCancel : (((k - 1 : Nat) : Real) / s) * s = ((k - 1 : Nat) : Real) := by field_simp
    rw [sub_mul, hCancel] at hLow
    have hu0 : 0 < u := by
      by_contra hn
      have hum : u * s <= 0 := mul_nonpos_of_nonpos_of_nonneg (le_of_not_gt hn) hs.le
      have ha0 : 0 <= s * A := mul_nonneg hs.le hA.le
      nlinarith
    have hRu : ((k - 1 : Nat) : Real) / u <= 2 * s := by
      have hcan : (((k - 1 : Nat) : Real) / u) * u = ((k - 1 : Nat) : Real) := by field_simp
      by_contra hn
      have hh := mul_lt_mul_of_pos_right (lt_of_not_ge hn) hu0
      rw [hcan] at hh
      nlinarith
    have hnear : abs (((k - 1 : Nat) : Real) / s - u) <= A := by
      apply abs_le.mpr
      constructor <;> linarith [hu.1, hu.2]
    have hroot : Nat.factorialConvolution primeProfileRealCoefficient (k - 1 - 1) u /
        Nat.factorialConvolution primeProfileRealCoefficient (k - 1) u = s := by
      simpa only [show k - 1 - 1 = k - 2 by omega] using heq
    have hshift := hshiftBound (k - 1) hrD' u hu0 hRu hnear hroot
    have hnear' : abs (u - ((k - 1 : Nat) : Real) / s) <= A := by
      rwa [abs_sub_comm]
    have hb := hcountB (k - 1) hrB' u hnear'
    let T := Real.exp (Real.exp (u - Real.eulerMascheroniConstant))
    let center := ((k - 1 : Nat) : Real) / s - Real.eulerMascheroniConstant -
      deriv (fun x : Real => (primeProfile (x : Complex)).re) s /
        (primeProfile (s : Complex)).re
    have hBerror : abs (Real.log (Real.log (primeThetaEndpointCount T : Real)) - center) <=
        (C + 32 * s) / ((k - 1 : Nat) : Real) := by
      have hcenter : (u - Real.eulerMascheroniConstant) - center =
          u - ((k - 1 : Nat) : Real) / s +
            deriv (fun x : Real => (primeProfile (x : Complex)).re) s /
              (primeProfile (s : Complex)).re := by dsimp [center]; ring
      calc
        _ <= abs (Real.log (Real.log (primeThetaEndpointCount T : Real)) -
            (u - Real.eulerMascheroniConstant)) +
            abs ((u - Real.eulerMascheroniConstant) - center) := abs_sub_le _ _ _
        _ <= (32 * s) / ((k - 1 : Nat) : Real) + C / ((k - 1 : Nat) : Real) := by
          rw [hcenter]
          exact add_le_add hb.2 hshift
        _ = _ := by ring
    have hNpos : 1 < (N : Real) := by
      have h := Real.exp_lt_exp.mpr (Real.exp_pos (c * (k : Real)))
      have h1 : 1 < Real.exp (Real.exp (c * (k : Real))) := by simpa only [Real.exp_zero] using h
      exact h1.trans_le hlo
    have hNB : (N : Real) <= primeThetaEndpointCount T := by exact_mod_cast hcount.trans hcapacity
    have hlog := Real.log_le_log (zero_lt_one.trans hNpos) hNB
    have hloglog := Real.log_le_log (Real.log_pos hNpos) hlog
    have hNbound : Real.log (Real.log (N : Real)) <= center +
        (C + 32 * s) / ((k - 1 : Nat) : Real) := by
      have htop := (abs_le.mp hBerror).2
      linarith only [hloglog, htop]
    refine Exists.intro N (Exists.intro i (Exists.intro u
      (And.intro hN (And.intro hlo (And.intro hi (And.intro hlast
        (And.intro hu (And.intro heq (And.intro htheta (And.intro (hcount.trans hcapacity)
          (And.intro hshift hNbound)))))))))))
end PrimeFactorOscillations



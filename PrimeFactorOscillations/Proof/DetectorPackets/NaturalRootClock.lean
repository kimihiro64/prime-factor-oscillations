/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/

import PrimeFactorOscillations.Helpers.PowerPolynomialLaw

/-!
# NaturalRootClock

Maintained extraction of completed detector/packet proof components.
All original theorem hypotheses and retained proof bodies are preserved.
This module alone asserts no improved zero-free boundary.
-/

set_option autoImplicit false
set_option Elab.async false

noncomputable section

namespace Real

theorem natural_odds_linear_error (q k M : Nat) (hq : 0 < q)
    (hkq : k <= q) (hkM : k <= M) :
    abs ((k : Real) / ((q : Real) - k) - (k : Real) / q) <=
      ((M : Real) ^ 2 * ((M : Real) + 1)) / (q : Real) ^ 2 := by
  have hqR : (0 : Real) < q := by exact_mod_cast hq
  have hk0 : (0 : Real) <= k := Nat.cast_nonneg k
  have hM0 : (0 : Real) <= M := Nat.cast_nonneg M
  have hkMR : (k : Real) <= M := by exact_mod_cast hkM
  have hSq : (k : Real) ^ 2 <= (M : Real) ^ 2 := by
    nlinarith only [mul_nonneg (sub_nonneg.mpr hkMR) (add_nonneg hk0 hM0)]
  have hBig : (M : Real) ^ 2 <= (M : Real) ^ 2 * ((M : Real) + 1) := by
    nlinarith only [mul_nonneg (sq_nonneg (M : Real)) hM0]
  by_cases heq : k = q
  . subst k
    rw [sub_self, div_zero, div_self hqR.ne', zero_sub, abs_neg, abs_one]
    calc
      (1 : Real) = (q : Real) ^ 2 / (q : Real) ^ 2 := by field_simp [hqR.ne']
      _ <= _ := div_le_div_of_nonneg_right (hSq.trans hBig) (sq_nonneg _)
  . have hlt : k < q := lt_of_le_of_ne hkq heq
    have hGap : (1 : Real) <= (q : Real) - k := by
      have hCast : (k : Real) + 1 <= q := by exact_mod_cast hlt
      linarith only [hCast]
    have hGapPos : 0 < (q : Real) - k := by linarith
    have hNonneg : 0 <= (k : Real) / ((q : Real) - k) - (k : Real) / q := by
      have hIdentity : (k : Real) / ((q : Real) - k) - (k : Real) / q =
          (k : Real) ^ 2 / ((q : Real) * ((q : Real) - k)) := by
        field_simp [hqR.ne', hGapPos.ne']
        ring
      rw [hIdentity]
      exact div_nonneg (sq_nonneg _) (mul_nonneg hqR.le hGapPos.le)
    rw [abs_of_nonneg hNonneg]
    have hLocal :
        ((k : Real) / ((q : Real) - k) - (k : Real) / q) <=
          ((k : Real) ^ 2 * ((k : Real) + 1)) / (q : Real) ^ 2 := by
      have hIdentity :
          ((k : Real) / ((q : Real) - k) - (k : Real) / q) * (q : Real) ^ 2 =
            (k : Real) ^ 2 * q / ((q : Real) - k) := by
        field_simp [hqR.ne', hGapPos.ne']
        ring
      have hProduct : 0 <= (k : Real) ^ 3 * (((q : Real) - k) - 1) :=
        mul_nonneg (pow_nonneg hk0 3) (by linarith)
      have hNum : (k : Real) ^ 2 * q <=
          ((k : Real) ^ 2 * ((k : Real) + 1)) * ((q : Real) - k) := by
        nlinarith only [hProduct]
      have hMul :
          ((k : Real) / ((q : Real) - k) - (k : Real) / q) * (q : Real) ^ 2 <=
            (k : Real) ^ 2 * ((k : Real) + 1) := by
        rw [hIdentity]
        calc
          _ <= (((k : Real) ^ 2 * ((k : Real) + 1)) * ((q : Real) - k)) /
              ((q : Real) - k) := div_le_div_of_nonneg_right hNum hGapPos.le
          _ = _ := by field_simp [hGapPos.ne']
      calc
        _ = (((k : Real) / ((q : Real) - k) - (k : Real) / q) * (q : Real) ^ 2) /
            (q : Real) ^ 2 := by field_simp [hqR.ne']
        _ <= _ := div_le_div_of_nonneg_right hMul (sq_nonneg _)
    have hNum :
        (k : Real) ^ 2 * ((k : Real) + 1) <=
          (M : Real) ^ 2 * ((M : Real) + 1) :=
      mul_le_mul hSq (by linarith only [hkMR]) (by positivity) (sq_nonneg _)
    exact hLocal.trans (div_le_div_of_nonneg_right hNum (sq_nonneg _))

theorem natural_odds_log_error (q k M : Nat) (hq : 0 < q)
    (hkq : k <= q) (hkM : k <= M) :
    abs ((k : Real) / ((q : Real) - k) -
      (k : Real) * Real.log (1 + 1 / (q : Real))) <=
      ((M : Real) ^ 2 * ((M : Real) + 1) + (M : Real) / 2) / (q : Real) ^ 2 := by
  have hqR : (0 : Real) < q := by exact_mod_cast hq
  have hk0 : (0 : Real) <= k := Nat.cast_nonneg k
  have hkMR : (k : Real) <= M := by exact_mod_cast hkM
  have hLog := Real.sub_log_one_add_bounds (1 / (q : Real)) (by positivity)
  have hLogError :
      abs ((k : Real) / q - (k : Real) * Real.log (1 + 1 / (q : Real))) <=
        ((M : Real) / 2) / (q : Real) ^ 2 := by
    have hIdentity : (k : Real) / q - (k : Real) * Real.log (1 + 1 / (q : Real)) =
        (k : Real) * (1 / (q : Real) - Real.log (1 + 1 / (q : Real))) := by ring
    rw [hIdentity, abs_of_nonneg (mul_nonneg hk0 hLog.1)]
    calc
      _ <= (k : Real) * ((1 / (q : Real)) ^ 2 / 2) :=
        mul_le_mul_of_nonneg_left hLog.2 hk0
      _ <= (M : Real) * ((1 / (q : Real)) ^ 2 / 2) :=
        mul_le_mul_of_nonneg_right hkMR (by positivity)
      _ = _ := by field_simp
  calc
    _ <= abs ((k : Real) / ((q : Real) - k) - (k : Real) / q) +
        abs ((k : Real) / q - (k : Real) * Real.log (1 + 1 / (q : Real))) :=
      abs_sub_le _ _ _
    _ <= ((M : Real) ^ 2 * ((M : Real) + 1)) / (q : Real) ^ 2 +
        ((M : Real) / 2) / (q : Real) ^ 2 :=
      add_le_add (natural_odds_linear_error q k M hq hkq hkM) hLogError
    _ = _ := by ring

end Real

namespace PrimeFactorOscillations.PrimeClockLaw

def ofRootLogCounts (rho : Nat.Primes -> Nat) (M : Nat) (hM : 0 < M)
    (hRho : forall p : Nat.Primes, rho p <= (p : Nat) - 1)
    (hDegree : forall p, rho p <= M) : PrimeClockLaw where
  weight := fun p => (rho p : Real) / ((((p : Nat) - 1 : Nat) : Real) - rho p)
  compensator := fun p => (rho p : Real) * Real.log (1 + primeProfileWeight (p : Nat))
  scale := M
  error := (M : Real) ^ 2 * ((M : Real) + 1) + (M : Real) / 2
  scale_pos := by exact_mod_cast hM
  error_nonneg := by positivity
  weight_nonneg := by
    intro p
    exact div_nonneg (Nat.cast_nonneg _)
      (sub_nonneg.mpr (by exact_mod_cast hRho p))
  compensator_nonneg := by
    intro p
    have hv : 0 <= primeProfileWeight (p : Nat) := by
      unfold primeProfileWeight
      positivity
    exact mul_nonneg (Nat.cast_nonneg _) (Real.log_nonneg (by linarith))
  compensator_le := by
    intro p
    have hv : 0 <= primeProfileWeight (p : Nat) := by
      unfold primeProfileWeight
      positivity
    have hLog := Real.sub_log_one_add_bounds (primeProfileWeight (p : Nat)) hv
    have hCast : (rho p : Real) <= M := by exact_mod_cast hDegree p
    calc
      _ <= (rho p : Real) * primeProfileWeight (p : Nat) :=
        mul_le_mul_of_nonneg_left (by linarith only [hLog.1]) (Nat.cast_nonneg _)
      _ <= _ := mul_le_mul_of_nonneg_right hCast hv
  quadratic_error := by
    intro p
    have hq : 0 < (p : Nat) - 1 := Nat.sub_pos_of_lt p.property.one_lt
    have h := Real.natural_odds_log_error ((p : Nat) - 1) (rho p) M hq
      (hRho p) (hDegree p)
    simpa only [primeProfileWeight, one_div, div_eq_mul_inv, one_mul, inv_pow] using h

theorem rootLogCounts_weight_eq_rootCounts
    (rho : Nat.Primes -> Nat) (M : Nat) (hM : 0 < M)
    (hRho : forall p : Nat.Primes, rho p <= (p : Nat) - 1)
    (hDegree : forall p, rho p <= M) (p : Nat.Primes) :
    (ofRootLogCounts rho M hM hRho hDegree).weight p =
      (ofRootCounts rho (fun p => (p : Nat) - 1) M hM hRho hDegree
        (fun _ => le_rfl)).weight p := rfl

end PrimeFactorOscillations.PrimeClockLaw

namespace PrimeFactorOscillations.PowerPolynomialLaw

def primeLogLaw (d : Nat) (a : Int) (hd : 0 < d) : PrimeClockLaw :=
  PrimeClockLaw.ofRootLogCounts (unitRootCount d a) d hd
    (unitRootCount_le_predecessor d a) (unitRootCount_le_degree d a hd)

theorem primeLogLaw_comparison (d : Nat) (a : Int) (hd : 0 < d)
    (b : Real) (hb : 0 < b) :
    ComparisonClaim (primeLogLaw d a hd) b :=
  (primeLogLaw d a hd).exists_densityRatio_linearization b hb

theorem primeLogLaw_weight_eq_primeLaw (d : Nat) (a : Int) (hd : 0 < d)
    (p : Nat.Primes) :
    (primeLogLaw d a hd).weight p = (primeLaw d a hd).weight p := rfl

theorem primeLogLaw_error_le_eighty_two (d : Nat) (a : Int) (hd : 0 < d)
    (hdFour : d <= 4) :
    (primeLogLaw d a hd).error <= 82 := by
  change (d : Real) ^ 2 * ((d : Real) + 1) + (d : Real) / 2 <= 82
  have hd0 : (0 : Real) <= d := Nat.cast_nonneg d
  have hd4 : (d : Real) <= 4 := by exact_mod_cast hdFour
  have hs : (d : Real) ^ 2 <= 16 := by nlinarith only [hd0, hd4]
  have hp : (d : Real) ^ 2 * ((d : Real) + 1) <= 80 := by
    calc
      _ <= 16 * 5 := mul_le_mul hs (by linarith only [hd4]) (by positivity)
        (by norm_num)
      _ = _ := by norm_num
  linarith only [hp, hd4]


theorem primeLogLaw_compensator (d : Nat) (a : Int) (hd : 0 < d)
    (p : Nat.Primes) :
    (primeLogLaw d a hd).compensator p =
      (unitRootCount d a p : Real) * Real.log ((p : Real) / ((p : Real) - 1)) := by
  change (unitRootCount d a p : Real) * Real.log (1 + primeProfileWeight (p : Nat)) = _
  congr 1
  congr 1
  unfold primeProfileWeight
  rw [Nat.cast_sub (Nat.le_of_lt p.property.one_lt), Nat.cast_one]
  have hp : (1 : Real) < (p : Nat) := by exact_mod_cast p.property.one_lt
  have hDen : Not ((p : Real) - 1 = 0) := by linarith only [hp]
  field_simp [hDen]
  ring

def logLawProbability (d : Nat) (a : Int) (n : Nat) : Real :=
  if hp : Nat.Prime n then
    (unitRootCount d a (Subtype.mk n hp) : Real) / (((n - 1 : Nat) : Real))
  else 0

theorem logLawProbability_le_one (d : Nat) (a : Int) (n : Nat) (hn : Nat.Prime n) :
    logLawProbability d a n <= 1 := by
  simp only [logLawProbability, dite_eq_left hn]
  have hqNat : 0 < n - 1 := Nat.sub_pos_of_lt hn.one_lt
  have hq : (0 : Real) < (n - 1 : Nat) := by exact_mod_cast hqNat
  have hRoot : (unitRootCount d a (Subtype.mk n hn) : Real) <= (n - 1 : Nat) := by
    exact_mod_cast unitRootCount_le_predecessor d a (Subtype.mk n hn)
  calc
    _ <= (((n - 1 : Nat) : Real)) / (((n - 1 : Nat) : Real)) :=
      div_le_div_of_nonneg_right hRoot hq.le
    _ = 1 := div_self hq.ne'

theorem primeLogLaw_probability_odds (d : Nat) (a : Int) (hd : 0 < d)
    (p : Nat.Primes) :
    (primeLogLaw d a hd).weight p =
      logLawProbability d a (p : Nat) / (1 - logLawProbability d a (p : Nat)) := by
  have h := PrimeClockLaw.rootCounts_weight_eq_probability_odds
    (unitRootCount d a) (fun p => (p : Nat) - 1) d hd
    (unitRootCount_le_predecessor d a) (unitRootCount_le_degree d a hd)
    (fun _ => le_rfl) p
  simp only [logLawProbability, dite_eq_left p.property]
  change (unitRootCount d a p : Real) /
      ((((p : Nat) - 1 : Nat) : Real) - unitRootCount d a p) =
    ((unitRootCount d a p : Real) / ((((p : Nat) - 1 : Nat) : Real))) /
      (1 - (unitRootCount d a p : Real) / ((((p : Nat) - 1 : Nat) : Real)))
  exact h

theorem primeLogLaw_probabilityMass_ratio (d : Nat) (a : Int) (hd : 0 < d)
    (N r : Nat) (hr : 1 <= r) :
    let s := familyPrefixProbabilities (logLawProbability d a) N
    List.bernoulliMass s (s.count 1 + r - 1) /
      List.bernoulliMass s (s.count 1 + r) = (primeLogLaw d a hd).densityRatio N r :=
  (primeLogLaw d a hd).probabilityMass_ratio_eq_densityRatio (logLawProbability d a)
    (logLawProbability_le_one d a) (primeLogLaw_probability_odds d a hd) N r hr

end PrimeFactorOscillations.PowerPolynomialLaw

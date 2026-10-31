/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Assembly.FiniteFieldIntegerWeightExponent
import PrimeFactorOscillations.Assembly.FiniteFieldQuasipolynomialHeight

/-!
# Sharp weight exponent across all fixed quasipolynomial heights

Two absolute constants precede the height degree. Every fixed degree
admits a uniform two-sided bound and exponent two on actual prime pairs.
The same cutoff witnesses retain genuine least-gap integer frames.
-/

set_option autoImplicit false
set_option Elab.async false

noncomputable section
namespace PrimeFactorOscillations.FiniteFieldQuasipolynomialWeight

open FiniteFieldIntegerMass
open FiniteFieldPrimePairHeight
open FiniteFieldQuasipolynomialHeight
open FiniteFieldIntegerWeightExponent
open FiniteFieldIntegerGapWindows
open PrimeProfileRigidity
open Filter

theorem exists_uniform_quasipolynomial_weights :
    exists a b : Real, And (0 < a) (And (0 < b)
      (forall m : Nat, 1 <= m -> exists Q0 : Nat,
        forall Q : Nat, Q0 <= Q ->
          And (1 <= Real.log (Q : Real)) (And (1 <= Real.log (Real.log (Q : Real)))
            (forall h n : Nat, 0 < h -> h < Q -> Q < n ->
              Nat.Prime n -> Nat.Prime (n + h) ->
              Real.log ((n + h : Nat) : Real) <= 2 * (Real.log (Q : Real)) ^ m ->
              And
                ((a / (degreeCost m) ^ 2) * (Real.log (Q : Real)) ^ 2 /
                    (Real.log (Real.log (Q : Real))) ^ 2 <= actualPacket (h : Int) Q n)
                (actualPacket (h : Int) Q n <=
                  (b * (degreeCost m) ^ 2) * (Real.log (Q : Real)) ^ 2 *
                    (Real.log (Real.log (Q : Real))) ^ 2))))) := by
  let a : Real := Classical.choose exists_prime_pair_split_bounds
  let b : Real := Classical.choose (Classical.choose_spec exists_prime_pair_split_bounds)
  have hAB := Classical.choose_spec (Classical.choose_spec exists_prime_pair_split_bounds)
  refine Exists.intro a (Exists.intro b (And.intro hAB.1 (And.intro hAB.2.1 ?_)))
  intro m hm
  let Q0 : Nat := Classical.choose (eventually_quasi_core_fits m)
  have hQ0 := Classical.choose_spec (eventually_quasi_core_fits m)
  refine Exists.intro Q0 ?_
  intro Q hQQ
  have hf := hQ0 Q hQQ
  refine And.intro hf.2.1 (And.intro hf.2.2.1 ?_)
  intro h n hh hhQ hQn hn hnh hheight
  have hK := quasi_core_supply m Q hm hf.2.1
  have hshift : Real.log (h : Real) <= ((quasiCore m Q : Nat) : Real) :=
    (Real.log_le_log (show 0 < (h : Real) by exact_mod_cast hh)
      (show (h : Real) <= (Q : Real) by exact_mod_cast hhQ.le)).trans hK.2
  have hcut := quasi_core_covers_pair_level m h Q n hm hh (by omega) hhQ hf.2.1 hheight
  have hsplit := hAB.2.2 (quasiCore m Q) h Q n hK.1 hf.2.2.2 hh hhQ hQn hn hnh hshift hcut
  have hLKpos : 0 < Real.log ((quasiCore m Q : Nat) : Real) :=
    Real.log_pos (by exact_mod_cast (show 1 < quasiCore m Q by omega))
  have hLLpos : 0 < Real.log (Real.log (Q : Real)) := by linarith only [hf.2.2.1]
  have hFpos := degree_cost_pos m
  have hLK := quasi_core_log_bound m Q hm hf.2.1 hf.2.2.1
  have hs := mul_self_le_mul_self hLKpos.le hLK
  have hpow : (Real.log ((quasiCore m Q : Nat) : Real)) ^ 2 <=
      (degreeCost m * Real.log (Real.log (Q : Real))) ^ 2 := by nlinarith only [hs]
  have hr := div_le_div_of_nonneg_left (sq_nonneg (Real.log (Q : Real)))
    (sq_pos_of_pos hLKpos) hpow
  have hscaled :
      a * ((Real.log (Q : Real)) ^ 2 /
        (degreeCost m * Real.log (Real.log (Q : Real))) ^ 2) <=
      a * ((Real.log (Q : Real)) ^ 2 / (Real.log ((quasiCore m Q : Nat) : Real)) ^ 2) :=
    mul_le_mul_of_nonneg_left hr hAB.1.le
  have hlo : (a / (degreeCost m) ^ 2) * (Real.log (Q : Real)) ^ 2 /
      (Real.log (Real.log (Q : Real))) ^ 2 <=
        a * (Real.log (Q : Real) / Real.log ((quasiCore m Q : Nat) : Real)) ^ 2 := by
    convert hscaled using 1 <;>
      field_simp [ne_of_gt hLKpos, ne_of_gt hLLpos, ne_of_gt hFpos] <;> ring
  refine And.intro (hlo.trans hsplit.1) ?_
  calc
    _ <= b * (Real.log (Q : Real)) ^ 2 *
        (Real.log ((quasiCore m Q : Nat) : Real)) ^ 2 := hsplit.2
    _ <= b * (Real.log (Q : Real)) ^ 2 *
        (degreeCost m * Real.log (Real.log (Q : Real))) ^ 2 :=
      mul_le_mul_of_nonneg_left hpow (mul_nonneg hAB.2.1.le (sq_nonneg _))
    _ = _ := by ring

theorem uniform_quasipolynomial_weight_exponent (m : Nat) (hm : 1 <= m)
    (eps : Real) (heps : 0 < eps) :
    exists Q0 : Nat, forall Q : Nat, Q0 <= Q ->
      forall h n : Nat, 0 < h -> h < Q -> Q < n ->
        Nat.Prime n -> Nat.Prime (n + h) ->
        Real.log ((n + h : Nat) : Real) <= 2 * (Real.log (Q : Real)) ^ m ->
        abs (Real.log (actualPacket (h : Int) Q n) /
          Real.log (Real.log (Q : Real)) - 2) <= eps := by
  let a : Real := Classical.choose exists_uniform_quasipolynomial_weights
  let b : Real := Classical.choose (Classical.choose_spec exists_uniform_quasipolynomial_weights)
  have hAB := Classical.choose_spec (Classical.choose_spec exists_uniform_quasipolynomial_weights)
  let QB : Nat := Classical.choose (hAB.2.2 m hm)
  have hQB := Classical.choose_spec (hAB.2.2 m hm)
  let c : Real := a / (degreeCost m) ^ 2
  let B : Real := b * (degreeCost m) ^ 2
  have hc : 0 < c := div_pos hAB.1 (sq_pos_of_pos (degree_cost_pos m))
  have hB : 0 < B := mul_pos hAB.2.1 (sq_pos_of_pos (degree_cost_pos m))
  have hevent : Filter.Eventually (fun Q : Nat => weightExponentError c B Q < eps) atTop :=
    (weight_exponent_error_tendsto_zero c B).eventually (Iio_mem_nhds heps)
  let QE : Nat := Classical.choose (Filter.eventually_atTop.mp hevent)
  have hQE := Classical.choose_spec (Filter.eventually_atTop.mp hevent)
  refine Exists.intro (max QB QE) ?_
  intro Q hQQ h n hh hhQ hQn hn hnh hheight
  have hb := hQB Q (le_trans (le_max_left _ _) hQQ)
  have hp := hb.2.2 h n hh hhQ hQn hn hnh hheight
  have ht := log_weight_ratio_band c B (Real.log (Q : Real))
    (actualPacket (h : Int) Q n) hc hB (by linarith only [hb.1]) hb.2.1 hp.1 hp.2
  exact ht.trans (hQE Q (le_trans (le_max_right _ _) hQQ)).le

theorem uniform_polynomial_prime_pair_weight_exponent (d : Nat)
    (eps : Real) (heps : 0 < eps) :
    exists Q0 : Nat, forall Q : Nat, Q0 <= Q ->
      forall h n : Nat, 0 < h -> h < Q -> Q < n ->
        Nat.Prime n -> Nat.Prime (n + h) -> n + h <= Q ^ d ->
        abs (Real.log (actualPacket (h : Int) Q n) /
          Real.log (Real.log (Q : Real)) - 2) <= eps := by
  let QW : Nat := Classical.choose (uniform_quasipolynomial_weight_exponent 2 (by omega) eps heps)
  have hQW := Classical.choose_spec (uniform_quasipolynomial_weight_exponent 2 (by omega) eps heps)
  have hNat : Tendsto (fun Q : Nat => (Q : Real)) atTop atTop := tendsto_natCast_atTop_atTop
  have hlog := (Real.tendsto_log_atTop.comp hNat).eventually_ge_atTop ((d : Real) + 1)
  let QL : Nat := Classical.choose (Filter.eventually_atTop.mp hlog)
  have hQL := Classical.choose_spec (Filter.eventually_atTop.mp hlog)
  refine Exists.intro (max 6 (max QW QL)) ?_
  intro Q hQQ h n hh hhQ hQn hn hnh hnQ
  have hQ6 : 6 <= Q := le_trans (le_max_left _ _) hQQ
  have hW : QW <= Q := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hQQ
  have hL : QL <= Q := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hQQ
  have hDL : (d : Real) + 1 <= Real.log (Q : Real) := hQL Q hL
  have hD0 : (0 : Real) <= (d : Real) := Nat.cast_nonneg d
  have hLpos : 0 <= Real.log (Q : Real) := by linarith only [hDL, hD0]
  have hpairlog := Real.log_le_log
    (show 0 < ((n + h : Nat) : Real) by exact_mod_cast hnh.pos)
    (show ((n + h : Nat) : Real) <= ((Q ^ d : Nat) : Real) by exact_mod_cast hnQ)
  rw [Nat.cast_pow, Real.log_pow] at hpairlog
  have hmul := mul_le_mul_of_nonneg_right
    (show (d : Real) <= Real.log (Q : Real) by linarith only [hDL]) hLpos
  have hheight : Real.log ((n + h : Nat) : Real) <= 2 * (Real.log (Q : Real)) ^ 2 := by
    nlinarith only [hpairlog, hmul, sq_nonneg (Real.log (Q : Real))]
  exact hQW Q hW h n hh hhQ hQn hn hnh hheight

theorem unbounded_quasipolynomial_frames (m : Nat) (hm : 1 <= m)
    (eps : Real) (heps : 0 < eps) (R : Nat) :
    exists Q i : Nat, And (R <= Q) (And (leastGapFrame Q i)
      (And (Real.log ((Q + 1 + leastRecurringPrimeGap : Nat) : Real) <=
          2 * (Real.log (Q : Real)) ^ m)
        (And
          (abs (Real.log (actualPacket (leastRecurringPrimeGap : Int) Q (Q + 1)) /
            Real.log (Real.log (Q : Real)) - 2) <= eps)
          (forall h n : Nat, 0 < h -> h < Q -> Q < n ->
            Nat.Prime n -> Nat.Prime (n + h) ->
            Real.log ((n + h : Nat) : Real) <= 2 * (Real.log (Q : Real)) ^ m ->
            abs (Real.log (actualPacket (h : Int) Q n) /
              Real.log (Real.log (Q : Real)) - 2) <= eps)))) := by
  let Q0 : Nat := Classical.choose (uniform_quasipolynomial_weight_exponent m hm eps heps)
  have hQ0 := Classical.choose_spec (uniform_quasipolynomial_weight_exponent m hm eps heps)
  let Q : Nat := Classical.choose (unbounded_least_gap_positive_windows (max R Q0))
  let i : Nat := Classical.choose (Classical.choose_spec
    (unbounded_least_gap_positive_windows (max R Q0)))
  have hi : max R Q0 <= Q /\ leastGapFrame Q i :=
    Classical.choose_spec (Classical.choose_spec
      (unbounded_least_gap_positive_windows (max R Q0)))
  have hhQ : leastRecurringPrimeGap < Q := hi.2.2.2.2.2.1
  have hp : Nat.Prime (Q + 1) := by
    rw [<- hi.2.2.2.2.2.2.1]
    exact PrimeFactorUnimodality.prime_primeAt i
  have hq : Nat.Prime (Q + 1 + leastRecurringPrimeGap) := by
    rw [<- hi.2.2.2.2.2.2.2.1]
    exact PrimeFactorUnimodality.prime_primeAt (i + 1)
  have hrange : Q + 1 + leastRecurringPrimeGap <= Q * Q := by
    have hQ6 := hi.2.1
    nlinarith only [hQ6, hhQ]
  have hQR : 0 < (Q : Real) := by exact_mod_cast (show 0 < Q by have ht := hi.2.1; omega)
  have hlogpair := Real.log_le_log
    (show 0 < ((Q + 1 + leastRecurringPrimeGap : Nat) : Real) by positivity)
    (show ((Q + 1 + leastRecurringPrimeGap : Nat) : Real) <= ((Q * Q : Nat) : Real)
      by exact_mod_cast hrange)
  rw [Nat.cast_mul, Real.log_mul (ne_of_gt hQR) (ne_of_gt hQR)] at hlogpair
  have hpow := base_le_positive_power (Real.log (Q : Real)) m hi.2.2.1 hm
  have hheight : Real.log ((Q + 1 + leastRecurringPrimeGap : Nat) : Real) <=
      2 * (Real.log (Q : Real)) ^ m := by linarith only [hlogpair, hpow]
  have hall := hQ0 Q (le_trans (le_max_right _ _) hi.1)
  have hpoint := hall leastRecurringPrimeGap (Q + 1)
    (by have ht := two_le_leastRecurringPrimeGap; omega) hhQ (by omega) hp hq hheight
  exact Exists.intro Q (Exists.intro i (And.intro
    (le_trans (le_max_left _ _) hi.1) (And.intro hi.2
      (And.intro hheight (And.intro hpoint hall)))))

end PrimeFactorOscillations.FiniteFieldQuasipolynomialWeight

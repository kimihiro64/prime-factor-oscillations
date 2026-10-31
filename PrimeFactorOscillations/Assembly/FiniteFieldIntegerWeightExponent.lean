/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Assembly.FiniteFieldIntegerWeightGrowth

/-!
# Sharp logarithmic exponent on genuine integer prime pairs

The pointwise two-sided weight theorem gives exponent two uniformly over
all natural-height prime pairs. Actual adjacent primes at the least
recurring gap attain this exponent along an unbounded sequence of cutoffs.
-/

set_option autoImplicit false
set_option Elab.async false

noncomputable section
namespace PrimeFactorOscillations.FiniteFieldIntegerWeightExponent

open FiniteFieldIntegerMass
open FiniteFieldIntegerWeightGrowth
open FiniteFieldIntegerGapWindows
open PrimeProfileRigidity
open Filter

def weightExponentError (c B : Real) (Q : Nat) : Real :=
  (abs (Real.log c) + abs (Real.log B) +
    2 * Real.log (Real.log (Real.log (Q : Real)))) /
      Real.log (Real.log (Q : Real))

theorem log_weight_ratio_band (c B L U : Real) (hc : 0 < c) (hB : 0 < B)
    (hL : 0 < L) (hT : 1 <= Real.log L)
    (hlo : c * L ^ 2 / (Real.log L) ^ 2 <= U)
    (hhi : U <= B * L ^ 2 * (Real.log L) ^ 2) :
    abs (Real.log U / Real.log L - 2) <=
      (abs (Real.log c) + abs (Real.log B) + 2 * Real.log (Real.log L)) /
        Real.log L := by
  have hTpos : 0 < Real.log L := by linarith only [hT]
  have hlo0 : 0 < c * L ^ 2 / (Real.log L) ^ 2 := by positivity
  have hlow := Real.log_le_log hlo0 hlo
  have hU : 0 < U := hlo0.trans_le hlo
  have hhigh := Real.log_le_log hU hhi
  rw [Real.log_div (mul_ne_zero (ne_of_gt hc) (pow_ne_zero 2 (ne_of_gt hL)))
      (pow_ne_zero 2 (ne_of_gt hTpos)),
    Real.log_mul (ne_of_gt hc) (pow_ne_zero 2 (ne_of_gt hL)),
    Real.log_pow, Real.log_pow] at hlow
  rw [Real.log_mul (mul_ne_zero (ne_of_gt hB) (pow_ne_zero 2 (ne_of_gt hL)))
      (pow_ne_zero 2 (ne_of_gt hTpos)),
    Real.log_mul (ne_of_gt hB) (pow_ne_zero 2 (ne_of_gt hL)),
    Real.log_pow, Real.log_pow] at hhigh
  norm_num at hlow hhigh
  have habs : abs (Real.log U - 2 * Real.log L) <=
      abs (Real.log c) + abs (Real.log B) + 2 * Real.log (Real.log L) := by
    apply abs_le.mpr
    constructor
    . linarith only [hlow, neg_abs_le (Real.log c), abs_nonneg (Real.log B)]
    . linarith only [hhigh, le_abs_self (Real.log B), abs_nonneg (Real.log c)]
  have hid : Real.log U / Real.log L - 2 =
      (Real.log U - 2 * Real.log L) / Real.log L := by
    field_simp [ne_of_gt hTpos]
  rw [hid, abs_div, abs_of_pos hTpos]
  exact div_le_div_of_nonneg_right habs hTpos.le

theorem weight_exponent_error_tendsto_zero (c B : Real) :
    Tendsto (weightExponentError c B) atTop (nhds 0) := by
  have hNat : Tendsto (fun Q : Nat => (Q : Real)) atTop atTop :=
    tendsto_natCast_atTop_atTop
  have hT := Real.tendsto_log_atTop.comp (Real.tendsto_log_atTop.comp hNat)
  have hi := tendsto_inv_atTop_zero.comp hT
  have hlog : Tendsto
      (fun Q : Nat => Real.log (Real.log (Real.log (Q : Real))) /
        Real.log (Real.log (Q : Real))) atTop (nhds 0) := by
    simpa only [Function.comp_def, pow_one, one_mul, add_zero] using
      (Real.tendsto_pow_log_div_mul_add_atTop 1 0 1 (by norm_num)).comp hT
  have hs := (hi.const_mul (abs (Real.log c) + abs (Real.log B))).add (hlog.const_mul 2)
  have heq : weightExponentError c B =
      (fun Q : Nat => (abs (Real.log c) + abs (Real.log B)) *
          (Real.log (Real.log (Q : Real))) ^ (-1 : Int) +
        2 * (Real.log (Real.log (Real.log (Q : Real))) /
          Real.log (Real.log (Q : Real)))) := by
    funext Q
    simp only [weightExponentError, zpow_neg_one]
    ring
  rw [heq]
  simpa only [Function.comp_def, zpow_neg_one, mul_zero, add_zero] using hs

theorem uniform_prime_pair_weight_exponent (eps : Real) (heps : 0 < eps) :
    exists Q0 : Nat, forall Q : Nat, Q0 <= Q ->
      forall h n : Nat, 0 < h -> h < Q -> Q < n -> n + h <= Q * Q ->
        Nat.Prime n -> Nat.Prime (n + h) ->
        abs (Real.log (actualPacket (h : Int) Q n) /
          Real.log (Real.log (Q : Real)) - 2) <= eps := by
  let c : Real := Classical.choose exists_uniform_prime_pair_weight_bounds
  let B : Real := Classical.choose (Classical.choose_spec exists_uniform_prime_pair_weight_bounds)
  have hCB := Classical.choose_spec (Classical.choose_spec exists_uniform_prime_pair_weight_bounds)
  let QB : Nat := Classical.choose hCB.2.2
  have hQB := Classical.choose_spec hCB.2.2
  have hevent : Filter.Eventually (fun Q : Nat => weightExponentError c B Q < eps) atTop :=
    (weight_exponent_error_tendsto_zero c B).eventually (Iio_mem_nhds heps)
  let QE : Nat := Classical.choose (Filter.eventually_atTop.mp hevent)
  have hQE := Classical.choose_spec (Filter.eventually_atTop.mp hevent)
  refine Exists.intro (max QB QE) ?_
  intro Q hQQ h n hh hhQ hQn hnQ hn hnh
  have hb := hQB Q (le_trans (le_max_left _ _) hQQ)
  have hp := hb.2.2 h n hh hhQ hQn hnQ hn hnh
  have ht := log_weight_ratio_band c B (Real.log (Q : Real))
    (actualPacket (h : Int) Q n) hCB.1 hCB.2.1
    (by linarith only [hb.1]) hb.2.1 hp.1 hp.2
  exact ht.trans (hQE Q (le_trans (le_max_right _ _) hQQ)).le

theorem unbounded_least_gap_weight_exponent (eps : Real) (heps : 0 < eps) (R : Nat) :
    exists Q i : Nat, And (R <= Q) (And (leastGapFrame Q i)
      (abs (Real.log (actualPacket (leastRecurringPrimeGap : Int) Q (Q + 1)) /
        Real.log (Real.log (Q : Real)) - 2) <= eps)) := by
  let Q0 : Nat := Classical.choose (uniform_prime_pair_weight_exponent eps heps)
  have hQ0 := Classical.choose_spec (uniform_prime_pair_weight_exponent eps heps)
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
  have hb := hQ0 Q (le_trans (le_max_right _ _) hi.1)
    leastRecurringPrimeGap (Q + 1) (by have ht := two_le_leastRecurringPrimeGap; omega)
    hhQ (by omega) hrange hp hq
  exact Exists.intro Q (Exists.intro i (And.intro
    (le_trans (le_max_left _ _) hi.1) (And.intro hi.2 hb)))

end PrimeFactorOscillations.FiniteFieldIntegerWeightExponent

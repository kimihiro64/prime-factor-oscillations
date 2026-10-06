/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Assembly.ConditionalLocation.GapCutoffRankBand
import PrimeFactorOscillations.Helpers.PrimePrefixClockStability

/-!
# Reference clocks at hypothetical gap cutoffs

Consecutive prime-prefix signs give a logarithmic physical error.
The reference root sequence is supplied by the local crossing theorem.
-/

set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace PrimeFactorOscillations
open Filter
open PrimeFactorUnimodality

private theorem rank_band_segment (r a b B u : Real) (hr : 0 <= r)
    (hB : 0 < B /\ a <= r / B /\ r / B <= b)
    (hu : 0 < u /\ a <= r / u /\ r / u <= b) :
    forall v : Real, Set.Icc (min B u) (max B u) v ->
      0 < v /\ a <= r / v /\ r / v <= b := by
  intro v hv
  rcases le_total B u with hBu | huB
  . rw [min_eq_left hBu, max_eq_right hBu] at hv
    have hv0 := hB.1.trans_le hv.1
    exact And.intro hv0 (And.intro
      (hu.2.1.trans (div_le_div_of_nonneg_left hr hv0 hv.2))
      ((div_le_div_of_nonneg_left hr hB.1 hv.1).trans hB.2.2))
  . rw [min_eq_right huB, max_eq_left huB] at hv
    have hv0 := hu.1.trans_le hv.1
    exact And.intro hv0 (And.intro
      (hB.2.1.trans (div_le_div_of_nonneg_left hr hv0 hv.2))
      ((div_le_div_of_nonneg_left hr hu.1 hv.1).trans hu.2.2))

/-- Every reference root in its proved compact rank band tracks the
hypothetical cutoff to a logarithmic physical error. -/
theorem eventually_gap_cutoff_reference_clock_bound (H : Nat) (hH : 2 <= H) :
    exists M : Real, 0 < M /\ Filter.Eventually (fun k : Nat => forall u : Real,
      0 < u /\ ((H : Real) + 1) / 2 <= ((k - 1 : Nat) : Real) / u /\
        ((k - 1 : Nat) : Real) / u <= 2 * ((H : Real) + 1) ->
      Nat.factorialConvolution primeProfileRealCoefficient (k - 1 - 1) u /
        Nat.factorialConvolution primeProfileRealCoefficient (k - 1) u = (H : Real) + 1 ->
      abs (Real.exp (Real.exp (u - Real.eulerMascheroniConstant)) -
        nicolasPrimeProductClock (primeAt (ordinaryGapCutoffIndex H k) - 1 : Nat)) <=
          M * Real.log (primeAt (ordinaryGapCutoffIndex H k) - 1 : Nat)) atTop := by
  let s : Real := (H : Real) + 1
  let b : Real := 1 / (4 * s)
  have hs3 : 3 <= s := by dsimp [s]; exact_mod_cast (show 3 <= H + 1 by omega)
  have hs : 0 < s := by linarith
  have hb : 0 < b := by dsimp [b]; positivity
  have hbs : b * s = 1 / 4 := by dsimp [b]; field_simp
  have hm : ((H : Real) + 1) * (2 * b) < 1 := by change s * (2 * b) < 1; nlinarith
  choose r0 N0 K hr0 hN0 hK hBracket using
    exists_primePrefix_cutoff_clock_bracket (1 / 8) (16 * s) (by norm_num) (by linarith)
  choose N1 hN1 hStable using eventually_primePrefixClock_stability K hK.le
  refine Exists.intro (36 * K) (And.intro (by positivity) ?_)
  have hN := tendsto_ordinaryGapCutoffPrefix H hH
  filter_upwards [eventually_gap_cutoff_logSum_bounds H hH b hb hm,
    ordinary_gap_cutoff_eventually_spec H hH, hN.eventually (eventually_ge_atTop (max N0 N1)),
    eventually_ge_atTop (max 2 (r0 + 1))]
    with k hB hcut hNlarge hk
  intro u hu hroot
  let C := ordinaryGapCutoffIndex H k
  let r := k - 1
  have hk2 : 2 <= k := (le_max_left _ _).trans hk
  have hr0' : r0 <= r := by have h := (le_max_right 2 (r0 + 1)).trans hk; dsimp [r]; omega
  have hNC : N0 <= primeAt C - 1 := (le_max_left _ _).trans hNlarge
  have hN1C : N1 <= primeAt C - 1 := (le_max_right _ _).trans hNlarge
  have hrR : (r : Real) = (k : Real) - 1 := by
    dsimp [r]
    rw [Nat.cast_sub (show 1 <= k by omega), Nat.cast_one]
  have hkR : (2 : Real) <= k := by exact_mod_cast hk2
  have hBand (j : Nat) (hj : j = C \/ j = C + 1) :
      forall v : Real, Set.Icc (min (primePrefixLogSum (primeAt j - 1)) u)
        (max (primePrefixLogSum (primeAt j - 1)) u) v ->
        0 < v /\ (1 : Real) / 8 <= (r : Real) / v /\ (r : Real) / v <= 16 * s := by
    have hBj := hB j hj
    have hBpos : 0 < primePrefixLogSum (primeAt j - 1) :=
      (mul_pos (by positivity : 0 < b / 2) (by linarith : (0 : Real) < k)).trans_le hBj.1
    have hprod : (k : Real) <= 8 * s * primePrefixLogSum (primeAt j - 1) := by
      have h := mul_le_mul_of_nonneg_left hBj.1 (show 0 <= 8 * s by positivity)
      have heq : 8 * s * (b / 2 * (k : Real)) = k := by
        nlinarith [congrArg (fun v : Real => v * k) hbs]
      rwa [heq] at h
    have hratioId : (r : Real) / primePrefixLogSum (primeAt j - 1) *
        primePrefixLogSum (primeAt j - 1) = r := by field_simp
    have hLower : (1 : Real) / 8 <= (r : Real) / primePrefixLogSum (primeAt j - 1) := by
      by_contra hn
      have hh := mul_lt_mul_of_pos_right (lt_of_not_ge hn) hBpos
      rw [hratioId] at hh
      nlinarith [hBj.2]
    have hUpper : (r : Real) / primePrefixLogSum (primeAt j - 1) <= 16 * s := by
      by_contra hn
      have hh := mul_lt_mul_of_pos_right (lt_of_not_ge hn) hBpos
      rw [hratioId] at hh
      nlinarith
    apply rank_band_segment (r : Real) (1 / 8) (16 * s) _ u (by positivity)
      (And.intro hBpos (And.intro hLower hUpper))
    exact And.intro hu.1 (And.intro (by dsimp [s] at *; linarith [hu.2.1])
      (by dsimp [s] at *; linarith [hu.2.2]))
  have hBefore : s < (densityRatio (primesBelow (primeAt C)) r : Real) := by
    have h := hcut.1.2.2
    rw [ordinary_localPrimeRatio_eq] at h
    dsimp [s, C, r]
    exact_mod_cast h
  have hNext := localPrimeRatio_step _ ordinaryEta_prime_probabilities r C (by dsimp [r]; omega) hcut.1.2.1
  have hAfterRat : localPrimeRatio (fun p => 1 / (p : Rat)) r (C + 1) <= (H : Rat) + 1 := by
    apply le_of_not_gt
    intro h
    have hp : 2 < primeAt (C + 1) := hcut.1.1.trans (primeAt_strictMono (Nat.lt_succ_self C))
    exact Nat.not_succ_le_self C (hcut.2 (C + 1) (And.intro hp (And.intro hNext.1 h)))
  have hAfter : (densityRatio (primesBelow (primeAt (C + 1))) r : Real) <= s := by
    rw [ordinary_localPrimeRatio_eq] at hAfterRat
    dsimp [s]
    exact_mod_cast hAfterRat
  have hClose := hBracket r C hr0' hNC u s hBand hroot hBefore hAfter
  have hClose' : abs (u - primePrefixLogSum (primeAt C - 1)) <= K / ((primeAt C - 1 : Nat) : Real) := by
    rwa [abs_sub_comm] at hClose
  exact hStable (primeAt C - 1) hN1C u hClose'

/-- The local crossing theorem supplies a reference root at every large
rank, with a bounded shift and the same band used by the clock comparison. -/
theorem exists_primeProfile_reference_root_sequence (s : Real) (hs : 0 < s) :
    exists A : Real, exists u : Nat -> Real, 0 < A /\
      Filter.Eventually (fun r : Nat =>
        abs (u r - (r : Real) / s) <= A /\
        (0 < u r /\ s / 2 <= (r : Real) / u r /\ (r : Real) / u r <= 2 * s) /\
        Nat.factorialConvolution primeProfileRealCoefficient (r - 1) (u r) /
          Nat.factorialConvolution primeProfileRealCoefficient r (u r) = s) atTop := by
  choose A r0 hA hr0 hCross using exists_primeProfile_reference_local_crossing s hs
  have hExists (r : Nat) : exists u : Real, r0 <= r ->
      abs (u - (r : Real) / s) <= A /\
      (0 < u /\ s / 2 <= (r : Real) / u /\ (r : Real) / u <= 2 * s) /\
      Nat.factorialConvolution primeProfileRealCoefficient (r - 1) u /
        Nat.factorialConvolution primeProfileRealCoefficient r u = s := by
    by_cases hr : r0 <= r
    . choose u hu hRoot hUnique using (hCross r hr).2
      have hBand := (hCross r hr).1 u (And.intro hu.1.le hu.2.le)
      exact Exists.intro u (fun _ => And.intro (abs_le.mpr (by constructor <;> linarith [hu.1, hu.2]))
        (And.intro (And.intro hBand.1 (And.intro hBand.2.1 hBand.2.2.1)) hRoot))
    . exact Exists.intro 0 (fun h => False.elim (hr h))
  choose u hu using hExists
  refine Exists.intro A (Exists.intro u (And.intro hA ?_))
  filter_upwards [eventually_ge_atTop r0] with r hr
  exact hu r hr

end PrimeFactorOscillations

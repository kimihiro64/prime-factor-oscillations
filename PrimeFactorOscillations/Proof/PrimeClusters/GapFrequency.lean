import PrimeFactorOscillations.Helpers.GapFrequencyBounds
import PrimeFactorOscillations.Helpers.PrimeWindowPairs
import PrimeFactorOscillations.Mathlib.Analysis.SpecialFunctions.Exp.CeilDoubleExpAdditive
import PrimeFactorOscillations.Mathlib.Analysis.SpecialFunctions.Pow.CeilDoubleExpPowerCount
import PrimeFactorOscillations.Proof.PrimeClusters.WindowCount

/-! # Positive-power prime windows have full bounded-gap frequency exponent -/

set_option autoImplicit false
set_option Elab.async false

namespace PrimeFactorOscillations

open PrimeFactorUnimodality

/-- Assign each occupied window an adjacent prime pair and its offset.
A fixed pair has at most H+1 possible offsets, with no disjointness assumption. -/
theorem prime_window_count_le_gap_count
    (H Y : Nat) (S : Finset Nat)
    (hend : forall n : Nat, Membership.mem S n -> n + H <= Y)
    (hwindow : forall n : Nat, Membership.mem S n ->
      2 <= ((Finset.Icc n (n + H)).filter Nat.Prime).card) :
    S.card <= primeGapFrequencyCount H Y * (H + 1) := by
  classical
  have hchoices : forall n : Nat, exists i : Nat, Membership.mem S n ->
      n <= primeAt i /\ primeAt (i + 1) <= n + H := by
    intro n
    by_cases hn : Membership.mem S n
    next =>
      choose i hi using exists_adjacent_primes_in_window (hwindow n hn)
      exact Exists.intro i (fun _ => hi)
    next =>
      exact Exists.intro 0 (fun h => False.elim (hn h))
  choose idx hidx using hchoices
  let G := (Finset.range Y).filter (fun i => primeAt i <= Y /\ primeGap i <= H)
  have hmap : forall n : Nat, Membership.mem S n ->
      Membership.mem (G.product (Finset.range (H + 1))) (idx n, primeAt (idx n) - n) := by
    intro n hn
    have hp := hidx n hn
    have hlt : primeAt (idx n) < primeAt (idx n + 1) :=
      primeAt_strictMono (Nat.lt_succ_self (idx n))
    have hnp := hp.1
    have hpq := hp.2
    have hG : Membership.mem G (idx n) := by
      apply (mem_primeGapFrequency_filter_iff H Y (idx n)).mpr
      refine And.intro (hlt.le.trans (hp.2.trans (hend n hn))) ?_
      change primeAt (idx n + 1) - primeAt (idx n) <= H
      omega
    apply Finset.mem_product.mpr
    exact And.intro hG (Finset.mem_range.mpr (by omega))
  have hinj : Set.InjOn (fun n => (idx n, primeAt (idx n) - n)) (S : Set Nat) := by
    intro n hn m hm heq
    have hi := congrArg Prod.fst heq
    have hoff := congrArg Prod.snd heq
    change idx n = idx m at hi
    change primeAt (idx n) - n = primeAt (idx m) - m at hoff
    have hnp := (hidx n hn).1
    have hmp := (hidx m hm).1
    rw [hi] at hoff hnp
    omega
  have hcard : S.card <= (G.product (Finset.range (H + 1))).card :=
    Finset.card_le_card_of_injOn
      (fun n => (idx n, primeAt (idx n) - n)) hmap hinj
  calc
    S.card <= (G.product (Finset.range (H + 1))).card := hcard
    _ = G.card * (Finset.range (H + 1)).card := Finset.card_product G _
    _ = primeGapFrequencyCount H Y * (H + 1) := by rw [Finset.card_range]; rfl

/-- Any fixed positive-power supply of prime windows forces frequency exponent
one for the actual consecutive gaps, independently of the power's size. -/
theorem primeGapFrequencyExponent_eq_one_of_positive_power_windows
    (H : Nat) (delta : Real) (hd : 0 < delta)
    (hsupply : Filter.Eventually (fun N : Nat =>
      (N : Real) ^ delta <=
        (((Finset.Ioc N (2 * N)).filter (fun n =>
          2 <= ((Finset.Icc n (n + H)).filter Nat.Prime).card)).card : Real))
      Filter.atTop) :
    primeGapFrequencyExponent H = 1 := by
  classical
  apply le_antisymm (primeGapFrequencyExponent_bounds H).2
  have hmodel : exists A : Real, exists K : Nat, forall X : Nat, K <= X ->
      3 + (primeGapFrequencyCount H X : Real) <=
        Real.exp (Real.exp (A * Real.log (Real.log (X : Real)))) :=
    Exists.intro (2 : Real) (Real.eventually_linear_count_le_double_exp_log_log
      (fun X => (primeGapFrequencyCount H X : Real)) (fun X => Nat.cast_nonneg _)
      (fun X => by exact_mod_cast primeGapFrequencyCount_le H X) 2 (by norm_num))
  apply (Real.le_limsup_log_log_div_gauge_iff
    (fun X => (primeGapFrequencyCount H X : Real))
    (fun X : Nat => Real.log (Real.log (X : Real)))
    (fun X => Nat.cast_nonneg _) (Real.eventually_le_log_log_nat 1) hmodel 1).mpr
  intro a ha K
  choose c hc using exists_between (max_lt_iff.mpr (And.intro (by norm_num) ha) :
    max 0 a < (1 : Real))
  have hcpos : 0 < c := (le_max_left 0 a).trans_lt hc.1
  have hac : a < c := (le_max_right 0 a).trans_lt hc.1
  have hdiff : 0 < 1 - c := by linarith only [hc.2]
  choose N0 hN0 using Filter.eventually_atTop.mp hsupply
  choose KL hKL using Real.eventually_le_log_log_nat 1
  let B : Real := (H : Real) + 1
  have hB : 0 < B := by dsimp only [B]; positivity
  let q : Real := (c * Real.log 2 + Real.log (2 / delta)) / (1 - c)
  let t : Real := 8 + 8 * B / delta + max 0 q + N0 + H + K + KL + 1
  let N := Nat.ceil (Real.exp (Real.exp t))
  let X := 2 * N + H
  have hBterm : 0 <= 8 * B / delta := by positivity
  have hmax : 0 <= max 0 q := le_max_left _ _
  have hn0 : (0 : Real) <= N0 := Nat.cast_nonneg _
  have hh0 : (0 : Real) <= H := Nat.cast_nonneg _
  have hk0 : (0 : Real) <= K := Nat.cast_nonneg _
  have hl0 : (0 : Real) <= KL := Nat.cast_nonneg _
  have ht : 8 <= t := by dsimp only [t]; linarith only [hBterm, hmax, hn0, hh0, hk0, hl0]
  have htN : t <= (N : Real) := by
    have he := Nat.le_ceil (Real.exp (Real.exp t))
    change Real.exp (Real.exp t) <= (N : Real) at he
    linarith [Real.add_one_le_exp t, Real.add_one_le_exp (Real.exp t)]
  have hNN0 : N0 <= N := by
    have hle : (N0 : Real) <= t := by
      dsimp only [t]
      linarith only [hBterm, hmax, hh0, hk0, hl0]
    exact_mod_cast hle.trans htN
  have hNH : H + 1 <= N := by
    have hle : (H : Real) + 1 <= t := by
      dsimp only [t]
      linarith only [hBterm, hmax, hn0, hk0, hl0]
    exact_mod_cast hle.trans htN
  have hNK : K <= N := by
    have hle : (K : Real) <= t := by
      dsimp only [t]
      linarith only [hBterm, hmax, hn0, hh0, hl0]
    exact_mod_cast hle.trans htN
  have hNL : KL <= N := by
    have hle : (KL : Real) <= t := by
      dsimp only [t]
      linarith only [hBterm, hmax, hn0, hh0, hk0]
    exact_mod_cast hle.trans htN
  have hsize : 8 * B <= delta * t := by
    have hle : 8 * B / delta <= t := by
      dsimp only [t]
      linarith only [hmax, hn0, hh0, hk0, hl0]
    have hm := mul_le_mul_of_nonneg_left hle hd.le
    have hcancel : delta * (8 * B / delta) = 8 * B := by field_simp [ne_of_gt hd]
    rwa [hcancel] at hm
  have hqt : q <= t := by
    have hq := le_max_right 0 q
    dsimp only [t]
    linarith only [hq, hBterm, hn0, hh0, hk0, hl0]
  have hscaled := mul_le_mul_of_nonneg_right hqt hdiff.le
  have hcancel : q * (1 - c) = c * Real.log 2 + Real.log (2 / delta) := by
    dsimp only [q]
    field_simp [ne_of_gt hdiff]
  rw [hcancel] at hscaled
  have hband := Real.ceil_double_exp_prime_prefix_additive_band ht
    (show N <= X + 1 by dsimp only [X]; omega)
    (show X + 1 <= 4 * N by dsimp only [X]; omega)
  have hLupper : Real.log (Real.log (X : Real)) <= t + Real.log 2 := by
    simpa only [Nat.add_sub_cancel] using hband.2
  have hgap : c * Real.log (Real.log (X : Real)) + Real.log (2 / delta) <= t := by
    have hm := mul_le_mul_of_nonneg_left hLupper hcpos.le
    nlinarith only [hm, hscaled]
  let S := (Finset.Ioc N (2 * N)).filter (fun n =>
    2 <= ((Finset.Icc n (n + H)).filter Nat.Prime).card)
  have hcount := prime_window_count_le_gap_count H X S
    (fun n hn => by
      have hle := (Finset.mem_Ioc.mp (Finset.mem_filter.mp hn).1).2
      dsimp only [X]
      omega)
    (fun n hn => (Finset.mem_filter.mp hn).2)
  have hcountR : (S.card : Real) <= (primeGapFrequencyCount H X : Real) * B := by
    dsimp only [B]
    exact_mod_cast hcount
  have hG0 : (0 : Real) <= primeGapFrequencyCount H X := Nat.cast_nonneg _
  have hmul := mul_nonneg hG0 hB.le
  have hs : (N : Real) ^ delta <= 2 * B * ((primeGapFrequencyCount H X : Real) + 1) := by
    have hsupplyN := hN0 N hNN0
    change (N : Real) ^ delta <= (S.card : Real) at hsupplyN
    nlinarith only [hsupplyN, hcountR, hmul, hB]
  have hgrowth := Real.double_exp_le_of_ceil_positive_power_count hd hgap hB hsize hs
  have hLpos : 0 <= Real.log (Real.log (X : Real)) :=
    (by norm_num : (0 : Real) <= 1).trans (hKL X (by dsimp only [X]; omega))
  have hcoef := mul_le_mul_of_nonneg_right hac.le hLpos
  have hExp := (Real.exp_le_exp.mpr (Real.exp_le_exp.mpr hcoef)).trans hgrowth
  refine Exists.intro X (And.intro (by dsimp only [X]; omega) ?_)
  linarith only [hExp]

/-- The maintained quantitative input discharges a full-frequency class.
Its numerical endpoint is a conservative existing input, not an optimized claim. -/
theorem exists_full_prime_gap_frequency_class :
    exists H : Nat, 2 <= H /\ primeGapFrequencyExponent H = 1 := by
  exact Exists.intro 600 (And.intro (by norm_num)
    (primeGapFrequencyExponent_eq_one_of_positive_power_windows
      600 ((1 : Real) / 3) (by norm_num) PrimeGaps.eventually_many_prime_windows_600))

end PrimeFactorOscillations

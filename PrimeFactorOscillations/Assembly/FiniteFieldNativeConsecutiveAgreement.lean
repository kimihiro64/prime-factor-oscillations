/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import Mathlib.NumberTheory.Bertrand
import PrimeFactorOscillations.Assembly.FiniteFieldNativeShortPairAgreement

/-!
# Sharp three-eighths reconstruction for actual consecutive prime pairs

The integer prime indices are fixed before the independent field scale.
Bertrand includes the initial pair and all seven correlations are retained.
-/

set_option autoImplicit false
set_option Elab.async false

noncomputable section
namespace PrimeFactorOscillations.FiniteFieldIntegerSignature
open Filter PrimeFactorUnimodality
open FiniteFieldIntegerWindowTransfer FiniteFieldIntegerGapWindows PrimeProfileRigidity

theorem native_indexed_gap_lt_lower (i : Nat) : primeGap i < primeAt i := by
  let p : Nat := primeAt i
  let q : Nat := primeAt (i + 1)
  have hp : Nat.Prime p := prime_primeAt i
  have hp0 := hp.pos
  have hp2 := hp.two_le
  have hpq : p < q := primeAt_strictMono (Nat.lt_succ_self i)
  choose r hr using Nat.exists_prime_lt_and_le_two_mul p (ne_of_gt hp0)
  let j : Nat := Nat.count Nat.Prime r
  have hj : primeAt j = r := Nat.nth_count hr.1
  have hij : i < j := by
    by_contra hnot
    have hji : j <= i := by omega
    have hmono := primeAt_strictMono.monotone hji
    rw [hj] at hmono
    change r <= p at hmono
    omega
  have hqr : q <= r := by
    calc
      q = primeAt (i + 1) := rfl
      _ <= primeAt j := primeAt_strictMono.monotone (by omega)
      _ = r := hj
  have hrstrict : r < 2 * p := by
    have hpar := hr.1.eq_two_or_odd
    omega
  change q - p < p
  omega

theorem native_agreement_three_eighths_of_consecutive (i j : Nat) (hij : Not (i = j)) :
    Tendsto (fun U : Nat => nativeAgreementMass (primeAt i) (primeGap i)
      (primeAt j) (primeGap j) (preciseCore U + 1)
        (preciseCore U * preciseCore U + 1) -
      3 * reciprocalBand (preciseCore U + 1)
        (preciseCore U * preciseCore U + 1) / 8) atTop (nhds 0) := by
  have hdata (a : Nat) : And (0 < primeGap a)
      (primeAt a + primeGap a = primeAt (a + 1)) := by
    have hs : primeAt a < primeAt (a + 1) :=
      primeAt_strictMono (show a < a + 1 by omega)
    unfold primeGap
    change And (0 < primeAt (a + 1) - primeAt a)
      (primeAt a + (primeAt (a + 1) - primeAt a) = primeAt (a + 1))
    constructor <;> omega
  have hni : Nat.Prime (primeAt i + primeGap i) := by
    rw [(hdata i).2]
    exact prime_primeAt (i + 1)
  have hnj : Nat.Prime (primeAt j + primeGap j) := by
    rw [(hdata j).2]
    exact prime_primeAt (j + 1)
  have hlow : Not (primeAt i = primeAt j) := fun he => hij (primeAt_strictMono.injective he)
  have hupp : Not (primeAt i + primeGap i = primeAt j + primeGap j) := by
    intro he
    rw [(hdata i).2, (hdata j).2] at he
    have hh := primeAt_strictMono.injective he
    exact hij (by omega)
  exact native_agreement_three_eighths_of_short_gaps (primeAt i) (primeGap i)
    (primeAt j) (primeGap j) (prime_primeAt i) hni (prime_primeAt j) hnj
    (hdata i).1 (hdata j).1 (native_indexed_gap_lt_lower i)
    (native_indexed_gap_lt_lower j) hlow hupp

theorem native_consecutive_pair_rigidity_of_retained_fraction (i j : Nat)
    (S : Nat -> Finset Nat) (delta : Real) (hdelta : 0 < delta)
    (hS : forall U p, Membership.mem (S U) p ->
      Membership.mem ((Finset.Ico (preciseCore U + 1)
        (preciseCore U * preciseCore U + 1)).filter Nat.Prime) p)
    (hw : forall U p, Membership.mem (S U) p ->
      integerNativeWeight (primeAt i) (primeGap i) p =
        integerNativeWeight (primeAt j) (primeGap j) p)
    (hlarge : forall U0 : Nat, exists U : Nat, And (U0 <= U)
      ((3 / 8 + delta) * reciprocalBand (preciseCore U + 1)
        (preciseCore U * preciseCore U + 1) <= (S U).sum (fun p => 1 / (p : Real)))) :
    i = j := by
  classical
  by_contra hij
  have hlim := native_agreement_three_eighths_of_consecutive i j hij
  let eps : Real := delta * Real.log 2 / 4
  have heps : 0 < eps := by dsimp [eps]; positivity
  have herr := hlim.eventually (Iio_mem_nhds heps)
  have hm := precise_core_tendsto_atTop.eventually eventually_reciprocal_square_band_positive
  choose U0 hU0 using eventually_atTop.mp (herr.and hm)
  choose U hUge hmass using hlarge U0
  have hb := hU0 U hUge
  have hr := retained_mass_le_native_agreement (primeAt i) (primeGap i)
    (primeAt j) (primeGap j) (preciseCore U + 1)
    (preciseCore U * preciseCore U + 1) (S U) (hS U) (hw U)
  have hscale := mul_le_mul_of_nonneg_left hb.2 hdelta.le
  dsimp only [eps] at hb heps
  nlinarith only [hb.1, hb.2, hscale, hmass, hr, heps]

theorem native_consecutive_three_eighths_is_sharp (i j : Nat) (hij : Not (i = j)) :
    exists S : Nat -> Finset Nat,
      And (forall U p, Membership.mem (S U) p ->
        Membership.mem ((Finset.Ico (preciseCore U + 1)
          (preciseCore U * preciseCore U + 1)).filter Nat.Prime) p)
        (And (forall U p, Membership.mem (S U) p ->
          integerNativeWeight (primeAt i) (primeGap i) p =
            integerNativeWeight (primeAt j) (primeGap j) p)
          (And (Tendsto (fun U : Nat => (S U).sum (fun p => 1 / (p : Real)) -
              3 * reciprocalBand (preciseCore U + 1)
                (preciseCore U * preciseCore U + 1) / 8) atTop (nhds 0))
            (forall c : Real, c < 3 / 8 -> Filter.Eventually (fun U : Nat =>
              c * reciprocalBand (preciseCore U + 1)
                (preciseCore U * preciseCore U + 1) <
                  (S U).sum (fun p => 1 / (p : Real))) atTop))) := by
  classical
  let S : Nat -> Finset Nat := fun U =>
    ((Finset.Ico (preciseCore U + 1) (preciseCore U * preciseCore U + 1)).filter
      Nat.Prime).filter (fun p => integerNativeWeight (primeAt i) (primeGap i) p =
        integerNativeWeight (primeAt j) (primeGap j) p)
  have hmass (U : Nat) : (S U).sum (fun p => 1 / (p : Real)) =
      nativeAgreementMass (primeAt i) (primeGap i) (primeAt j) (primeGap j)
        (preciseCore U + 1) (preciseCore U * preciseCore U + 1) := by
    dsimp only [S, nativeAgreementMass]
    rw [Finset.sum_filter]
  have hlim := native_agreement_three_eighths_of_consecutive i j hij
  have hs : Tendsto (fun U : Nat => (S U).sum (fun p => 1 / (p : Real)) -
      3 * reciprocalBand (preciseCore U + 1)
        (preciseCore U * preciseCore U + 1) / 8) atTop (nhds 0) := by
    simpa only [hmass] using hlim
  refine Exists.intro S (And.intro ?_ (And.intro ?_ (And.intro hs ?_)))
  . intro U p hp
    exact (Finset.mem_filter.mp hp).1
  . intro U p hp
    exact (Finset.mem_filter.mp hp).2
  . intro c hc
    have hgap : 0 < (3 / 8 : Real) - c := by linarith only [hc]
    let eta : Real := (3 / 8 - c) * Real.log 2 / 4
    have heta : 0 < eta := by dsimp [eta]; positivity
    have hlo := hs.eventually (Ioi_mem_nhds (show -eta < 0 by linarith only [heta]))
    have hm := precise_core_tendsto_atTop.eventually eventually_reciprocal_square_band_positive
    filter_upwards [hlo, hm] with U hl hM
    have hscale := mul_le_mul_of_nonneg_left hM hgap.le
    dsimp only [eta] at hl heta
    nlinarith only [hl, hscale, heta]

theorem unbounded_least_gap_consecutive_native_frames (R : Nat) :
    exists Q i : Nat, And (R <= Q) (And (leastGapFrame Q i)
      (forall j : Nat, forall S : Nat -> Finset Nat, forall delta : Real, 0 < delta ->
        (forall U p, Membership.mem (S U) p ->
          Membership.mem ((Finset.Ico (preciseCore U + 1)
            (preciseCore U * preciseCore U + 1)).filter Nat.Prime) p) ->
        (forall U p, Membership.mem (S U) p ->
          integerNativeWeight (Q + 1) leastRecurringPrimeGap p =
            integerNativeWeight (primeAt j) (primeGap j) p) ->
        (forall U0 : Nat, exists U : Nat, And (U0 <= U)
          ((3 / 8 + delta) * reciprocalBand (preciseCore U + 1)
            (preciseCore U * preciseCore U + 1) <= (S U).sum (fun p => 1 / (p : Real)))) ->
        And (j = i) (primeGap j = leastRecurringPrimeGap))) := by
  choose Q i hRQ hf using unbounded_least_gap_positive_windows R
  refine Exists.intro Q (Exists.intro i (And.intro hRQ (And.intro hf ?_)))
  intro j S delta hdelta hS hw hlarge
  have hbase : primeAt i = Q + 1 := hf.2.2.2.2.2.1
  have hupper : primeAt (i + 1) = Q + 1 + leastRecurringPrimeGap := hf.2.2.2.2.2.2.1
  have hgap : primeGap i = leastRecurringPrimeGap := by
    unfold primeGap
    rw [hbase, hupper]
    omega
  have hwi : forall U p, Membership.mem (S U) p ->
      integerNativeWeight (primeAt i) (primeGap i) p =
        integerNativeWeight (primeAt j) (primeGap j) p := by
    intro U p hp
    simpa only [hbase, hgap] using hw U p hp
  have hij := native_consecutive_pair_rigidity_of_retained_fraction
    i j S delta hdelta hS hwi hlarge
  exact And.intro hij.symm (by rw [<- hij]; exact hgap)

end PrimeFactorOscillations.FiniteFieldIntegerSignature

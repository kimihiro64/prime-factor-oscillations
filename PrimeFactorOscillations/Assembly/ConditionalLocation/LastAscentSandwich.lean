/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Assembly.ConditionalLocation.ActualGapCutoff

/-!
# Last ascents from local exact-gap coverage

Coverage supplies an actual ascent immediately before the attained
hypothetical cutoff; eventual gap lower bounds exclude later ascents.
-/

set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace PrimeFactorOscillations
open Filter
open PrimeFactorUnimodality

/-- Local exact-gap coverage brackets the actual last ascent, with the
eventual minimum-gap hypothesis accounting for every later candidate. -/
theorem eventually_last_ascent_gap_cutoff_sandwich (H : Nat) (hH : 2 <= H)
    (hMin : Filter.Eventually (fun i : Nat => H <= primeGap i) atTop)
    (hCoverage : Filter.Eventually (fun x : Real => exists i : Nat,
      x < (primeAt i : Real) /\ (primeAt i : Real) <= x + gapCoverageLength x /\
      primeGap i = H) atTop) :
    Filter.Eventually (fun k : Nat =>
      IsGreatest {i | ordinaryDensity k i < ordinaryDensity k (i + 1)}
        (sSup {i | ordinaryDensity k i < ordinaryDensity k (i + 1)}) /\
      (primeAt (ordinaryGapCutoffIndex H k) : Real) -
          2 * gapCoverageLength (primeAt (ordinaryGapCutoffIndex H k)) <
        (lastAscentPrime (ordinaryDensity k) : Real) /\
      lastAscentPrime (ordinaryDensity k) <= primeAt (ordinaryGapCutoffIndex H k)) atTop := by
  choose I0 hI0 using hMin.exists_forall_of_atTop
  have hV := tendsto_ordinaryGapCutoffPrime H hH
  have hCover := hV.eventually (eventually_exact_gap_before_of_coverage H hCoverage)
  have hLarge := hV.eventually (eventually_ge_atTop (max 16 (primeAt I0 : Real)))
  have hLog := (Real.tendsto_log_atTop.comp hV).eventually (eventually_ge_atTop 4)
  filter_upwards [ordinary_gap_cutoff_eventually_spec H hH,
    eventually_gap_cutoff_seed_below_half H hH, hCover, hLarge, hLog,
    eventually_ge_atTop (2 : Nat)] with k hcut hseed hcover hlarge hlog hk
  let C := ordinaryGapCutoffIndex H k
  choose t ht using hseed
  choose j hj using hcover
  have hV16 : (16 : Real) <= primeAt C := (le_max_left _ _).trans hlarge
  have hlen := gapCoverageLength_le_quarter (primeAt C) hV16
    ((by norm_num : (1 : Real) <= 4).trans hlog)
  have htj : t <= j := by
    have htR : 2 * (primeAt t : Real) <= primeAt C := by exact_mod_cast ht.1
    have hPrime : primeAt t <= primeAt j := by
      exact_mod_cast (show (primeAt t : Real) <= primeAt j by linarith [hj.1, hlen.2])
    exact primeAt_strictMono.le_iff_le.mp hPrime
  have hjC : j <= C := primeAt_strictMono.le_iff_le.mp (by exact_mod_cast hj.2.1)
  have hIC : I0 <= C := primeAt_strictMono.le_iff_le.mp
    (by exact_mod_cast (le_max_right _ _).trans hlarge)
  have hbound := last_ascent_bracket_of_gap_cutoff H k C t j hk hcut htj hjC ht.2.2.1
    hj.2.2 (fun i hi => hI0 i (hIC.trans hi.le))
  exact And.intro hbound.2.1 (And.intro
    (hj.1.trans_le (by exact_mod_cast hbound.2.2.1)) hbound.2.2.2)

/-- The actual last ascent tends to infinity under the same arithmetic
coverage hypothesis, not under an additional location assumption. -/
theorem tendsto_last_ascent_of_local_gap_coverage (H : Nat) (hH : 2 <= H)
    (hMin : Filter.Eventually (fun i : Nat => H <= primeGap i) atTop)
    (hCoverage : Filter.Eventually (fun x : Real => exists i : Nat,
      x < (primeAt i : Real) /\ (primeAt i : Real) <= x + gapCoverageLength x /\
      primeGap i = H) atTop) :
    Tendsto (fun k : Nat => (lastAscentPrime (ordinaryDensity k) : Real)) atTop atTop := by
  have hV := tendsto_ordinaryGapCutoffPrime H hH
  have hLarge := hV.eventually (eventually_ge_atTop (16 : Real))
  have hLog := (Real.tendsto_log_atTop.comp hV).eventually (eventually_ge_atTop 4)
  apply tendsto_atTop_mono' atTop _ (hV.atTop_div_const (by norm_num : (0 : Real) < 2))
  filter_upwards [eventually_last_ascent_gap_cutoff_sandwich H hH hMin hCoverage,
    hLarge, hLog] with k hs hx hl
  have hlen := gapCoverageLength_le_quarter _ hx
    ((by norm_num : (1 : Real) <= 4).trans hl)
  linarith [hs.2.1, hlen.2]

end PrimeFactorOscillations

/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Assembly.ConditionalLocation.GapCutoffReference
import PrimeFactorOscillations.Assembly.ConditionalLocation.LastAscentClockEnvelope

/-!
# Fine tracking of the actual last ascent

Local exact-gap coverage gives both the relative cutoff limit and the
reference-clock error tending to zero on the actual square-root scale.
-/

set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace PrimeFactorOscillations
open Filter
open PrimeFactorUnimodality

/-- Fine tracking at the actual last ascent, from local coverage and the
reference root equation. No location hypothesis is supplied. -/
theorem tendsto_last_ascent_reference_clock_error (H : Nat) (hH : 2 <= H)
    (hMin : Filter.Eventually (fun i : Nat => H <= primeGap i) atTop)
    (hCoverage : Filter.Eventually (fun x : Real => exists i : Nat,
      x < (primeAt i : Real) /\ (primeAt i : Real) <= x + gapCoverageLength x /\
      primeGap i = H) atTop)
    (u : Nat -> Real)
    (hRoot : Filter.Eventually (fun r : Nat =>
      (0 < u r /\ ((H : Real) + 1) / 2 <= (r : Real) / u r /\
        (r : Real) / u r <= 2 * ((H : Real) + 1)) /\
      Nat.factorialConvolution primeProfileRealCoefficient (r - 1) (u r) /
        Nat.factorialConvolution primeProfileRealCoefficient r (u r) = (H : Real) + 1) atTop) :
    Tendsto (fun k : Nat =>
      (Real.exp (Real.exp (u (k - 1) - Real.eulerMascheroniConstant)) -
        nicolasPrimeProductClock (lastAscentPrime (ordinaryDensity k) - 1 : Nat)) /
          Real.sqrt (lastAscentPrime (ordinaryDensity k))) atTop (nhds 0) := by
  choose M hM hClock using eventually_gap_cutoff_reference_clock_bound H hH
  choose N0 hN0 hEnvelope using exists_last_ascent_clock_error_envelope
  choose R0 hR0 using hRoot.exists_forall_of_atTop
  have hP := tendsto_last_ascent_of_local_gap_coverage H hH hMin hCoverage
  have hV := tendsto_ordinaryGapCutoffPrime H hH
  have hSmall : Tendsto (fun k : Nat =>
      2 * M * Real.log (primeAt (ordinaryGapCutoffIndex H k)) /
        Real.sqrt (primeAt (ordinaryGapCutoffIndex H k)) +
      32 / Real.log (primeAt (ordinaryGapCutoffIndex H k))) atTop (nhds 0) := by
    have hFirst : Tendsto (fun x : Real => Real.log x / Real.sqrt x) atTop (nhds 0) := by
      simpa only [Real.sqrt_eq_rpow] using
        (isLittleO_log_rpow_atTop (by norm_num : (0 : Real) < 1 / 2)).tendsto_div_nhds_zero
    have hSecond : Tendsto (fun k : Nat =>
        (32 : Real) / Real.log (primeAt (ordinaryGapCutoffIndex H k))) atTop (nhds 0) :=
      tendsto_const_nhds.div_atTop (Real.tendsto_log_atTop.comp hV)
    simpa only [Function.comp_def, mul_div_assoc, mul_zero, add_zero] using
      ((hFirst.comp hV).const_mul (2 * M)).add hSecond
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  apply squeeze_zero' (Filter.Eventually.of_forall (fun _ => norm_nonneg _)) _ hSmall
  filter_upwards [eventually_last_ascent_gap_cutoff_sandwich H hH hMin hCoverage,
    hClock, hP.eventually (eventually_ge_atTop ((N0 : Real) + 1)),
    hV.eventually (eventually_ge_atTop (64 : Real)),
    (Real.tendsto_log_atTop.comp hV).eventually (eventually_ge_atTop 4),
    eventually_ge_atTop (R0 + 1)] with k hSand hClockK hPN hV64 hLog hk
  have hPN' : N0 <= lastAscentPrime (ordinaryDensity k) - 1 := by
    have h : N0 + 1 <= lastAscentPrime (ordinaryDensity k) := by exact_mod_cast hPN
    omega
  have hRK := hR0 (k - 1) (by omega)
  rw [Real.norm_eq_abs]
  exact hEnvelope (lastAscentPrime (ordinaryDensity k)) (primeAt (ordinaryGapCutoffIndex H k))
    hPN' (by exact_mod_cast hV64) hSand.2.2 hLog hSand.2.1.le
    _ M hM.le (hClockK (u (k - 1)) hRK.1 hRK.2)

theorem tendsto_last_ascent_div_gap_cutoff (H : Nat) (hH : 2 <= H)
    (hMin : Filter.Eventually (fun i : Nat => H <= primeGap i) atTop)
    (hCoverage : Filter.Eventually (fun x : Real => exists i : Nat,
      x < (primeAt i : Real) /\ (primeAt i : Real) <= x + gapCoverageLength x /\
      primeGap i = H) atTop) :
    Tendsto (fun k : Nat => (lastAscentPrime (ordinaryDensity k) : Real) /
      (primeAt (ordinaryGapCutoffIndex H k) : Real)) atTop (nhds 1) := by
  have hV := tendsto_ordinaryGapCutoffPrime H hH
  have hSmall : Tendsto (fun k : Nat =>
      (2 : Real) / Real.sqrt (primeAt (ordinaryGapCutoffIndex H k))) atTop (nhds 0) :=
    tendsto_const_nhds.div_atTop (Real.tendsto_sqrt_atTop.comp hV)
  have hZero : Tendsto (fun k : Nat =>
      (lastAscentPrime (ordinaryDensity k) : Real) /
        (primeAt (ordinaryGapCutoffIndex H k) : Real) - 1) atTop (nhds 0) := by
    apply tendsto_zero_iff_norm_tendsto_zero.mpr
    apply squeeze_zero' (Filter.Eventually.of_forall (fun _ => norm_nonneg _)) _ hSmall
    filter_upwards [eventually_last_ascent_gap_cutoff_sandwich H hH hMin hCoverage,
      hV.eventually (eventually_ge_atTop (16 : Real)),
      (Real.tendsto_log_atTop.comp hV).eventually (eventually_ge_atTop 1)] with k hSand hV16 hl
    let V : Real := primeAt (ordinaryGapCutoffIndex H k)
    let P : Real := lastAscentPrime (ordinaryDensity k)
    have hV0 : 0 < V := by dsimp [V]; linarith
    have hRoot : 0 < Real.sqrt V := Real.sqrt_pos.mpr hV0
    have hPV : P <= V := by dsimp [P, V]; exact_mod_cast hSand.2.2
    have hDelta : V - P <= 2 * gapCoverageLength V := by linarith [hSand.2.1]
    have hLen : gapCoverageLength V <= Real.sqrt V :=
      div_le_self (Real.sqrt_nonneg V) (by change 1 <= (Real.log V) ^ (2 : Nat); change 1 <= Real.log V at hl; nlinarith)
    change norm (P / V - 1) <= 2 / Real.sqrt V
    rw [Real.norm_eq_abs, show P / V - 1 = (P - V) / V by field_simp,
      abs_div, abs_of_pos hV0, abs_of_nonpos (sub_nonpos.mpr hPV)]
    calc
      _ = (V - P) / V := by ring
      _ <= (2 * Real.sqrt V) / V :=
        div_le_div_of_nonneg_right (by linarith) hV0.le
      _ = _ := by
        have hs := Real.sq_sqrt hV0.le
        field_simp
        nlinarith
  simpa only [sub_add_cancel, zero_add] using hZero.add_const 1

end PrimeFactorOscillations

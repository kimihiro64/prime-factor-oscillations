/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.GapFrequencyCoverage

/-!
# Local exact-gap coverage before an endpoint

Shifts the forward coverage interval to the short interval ending at a
specified late endpoint, with explicit length comparisons.
-/

set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace PrimeFactorOscillations
open Filter

theorem gapCoverageLength_le_quarter (x : Real) (hx : 16 <= x)
    (hl : 1 <= Real.log x) :
    0 < gapCoverageLength x /\ gapCoverageLength x <= x / 4 := by
  have hs := Real.sqrt_nonneg x
  have hsq := Real.sq_sqrt (show 0 <= x by linarith)
  have hs4 : 4 <= Real.sqrt x := by nlinarith
  have hsx : Real.sqrt x <= x / 4 := by nlinarith
  refine And.intro (div_pos (Real.sqrt_pos.mpr (by linarith))
    (sq_pos_of_pos (by linarith))) ?_
  exact (div_le_self hs (by nlinarith : 1 <= (Real.log x) ^ (2 : Nat))).trans hsx

theorem gapCoverageLength_half_interval (x y : Real) (hx : 16 <= x)
    (hl : 4 <= Real.log x) (hxy : x / 2 <= y) (hyx : y <= x) :
    gapCoverageLength y <= 2 * gapCoverageLength x := by
  have hx0 : 0 < x := by linarith
  have hy0 : 0 < y := by linarith
  have hlog := Real.log_le_log (show 0 < x / 2 by positivity) hxy
  rw [Real.log_div hx0.ne' (by norm_num : Not ((2 : Real) = 0))] at hlog
  have h2 : Real.log 2 <= 1 := by
    have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : Real) < 2)
    norm_num at h
    exact h
  have hly : 0 < Real.log y := by linarith
  have hscale : (Real.log x) ^ (2 : Nat) <= 2 * (Real.log y) ^ (2 : Nat) := by
    nlinarith [sq_nonneg (Real.log x - Real.log y)]
  have hs := Real.sqrt_le_sqrt hyx
  dsimp [gapCoverageLength]
  calc
    _ <= Real.sqrt x / (Real.log y) ^ (2 : Nat) :=
      div_le_div_of_nonneg_right hs (by positivity)
    _ <= Real.sqrt x / ((Real.log x) ^ (2 : Nat) / 2) :=
      div_le_div_of_nonneg_left (Real.sqrt_nonneg x)
        (div_pos (sq_pos_of_pos (by linarith)) (by norm_num)) (by linarith)
    _ = _ := by ring

/-- Shift the forward coverage hypothesis to a short interval immediately
before any sufficiently late endpoint. -/
theorem eventually_exact_gap_before_of_coverage (H : Nat)
    (hCoverage : Filter.Eventually (fun x : Real => exists i : Nat,
      x < (PrimeFactorUnimodality.primeAt i : Real) /\
      (PrimeFactorUnimodality.primeAt i : Real) <= x + gapCoverageLength x /\
      PrimeFactorUnimodality.primeGap i = H) atTop) :
    Filter.Eventually (fun x : Real => exists i : Nat,
      x - 2 * gapCoverageLength x < (PrimeFactorUnimodality.primeAt i : Real) /\
      (PrimeFactorUnimodality.primeAt i : Real) <= x /\
      PrimeFactorUnimodality.primeGap i = H) atTop := by
  choose X0 hX0 using hCoverage.exists_forall_of_atTop
  have hLog : Filter.Eventually (fun x : Real => 4 <= Real.log x) atTop :=
    Real.tendsto_log_atTop.eventually (eventually_ge_atTop 4)
  filter_upwards [hLog, eventually_ge_atTop (max 16 (2 * X0))] with x hl hx
  have hx16 : 16 <= x := (le_max_left _ _).trans hx
  have hx0 : 2 * X0 <= x := (le_max_right _ _).trans hx
  have hlen := gapCoverageLength_le_quarter x hx16 (by linarith)
  let y := x - 2 * gapCoverageLength x
  have hyx : y <= x := by dsimp [y]; linarith [hlen.1]
  have hxy : x / 2 <= y := by dsimp [y]; linarith [hlen.2]
  have hy0 : X0 <= y := by linarith
  choose i hi using hX0 y hy0
  have hly := gapCoverageLength_half_interval x y hx16 hl hxy hyx
  exact Exists.intro i (And.intro hi.1 (And.intro (by dsimp [y] at *; linarith [hi.2.1]) hi.2.2))

end PrimeFactorOscillations

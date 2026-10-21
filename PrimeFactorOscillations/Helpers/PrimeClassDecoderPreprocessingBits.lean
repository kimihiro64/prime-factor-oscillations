/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.PrimeClassDecoderBits

/-!
# Binary size of every polynomial-cutoff preprocessing value

Any fixed polynomial in U_N+1 is eventually at most N. The same bit
budget therefore covers values up to N+1 plus that polynomial, including
the binary-log fuel, root-search powers and fixed rational numerators.
-/

set_option autoImplicit false
set_option Elab.async false

namespace PrimeFactorOscillations.PrimeClassDecoder

open Filter

theorem log_binaryCutoff_succ_div_log_tendsto_zero :
    Tendsto (fun N : Nat => Real.log ((binaryCutoff N : Real) + 1) /
      Real.log (N : Real)) atTop (nhds 0) := by
  have hU : Tendsto (fun N : Nat => (binaryCutoff N : Real) + 1) atTop atTop := by
    apply tendsto_atTop.mpr
    intro a
    filter_upwards [binaryCutoff_real_atTop.eventually (eventually_ge_atTop a)] with N hN
    linarith
  have hsmall := Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero.comp hU
  change Tendsto (fun N : Nat => Real.log ((binaryCutoff N : Real) + 1) /
    ((binaryCutoff N : Real) + 1)) atTop (nhds 0) at hsmall
  have hlogN : Tendsto (fun N : Nat => Real.log (N : Real)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hone : Tendsto (fun _ : Nat => (1 : Real)) atTop (nhds 1) := tendsto_const_nhds
  have hplus := binaryCutoff_div_log_tendsto.add (hone.div_atTop hlogN)
  have heq1 : (fun N : Nat => (binaryCutoff N : Real) / Real.log (N : Real) +
      1 / Real.log (N : Real)) =
      (fun N : Nat => ((binaryCutoff N : Real) + 1) / Real.log (N : Real)) := by
    funext N
    ring
  rw [heq1] at hplus
  have hlim := hsmall.mul hplus
  have heq : Filter.EventuallyEq atTop
      (fun N : Nat => (Real.log ((binaryCutoff N : Real) + 1) /
        ((binaryCutoff N : Real) + 1)) *
          (((binaryCutoff N : Real) + 1) / Real.log (N : Real)))
      (fun N : Nat => Real.log ((binaryCutoff N : Real) + 1) / Real.log (N : Real)) := by
    apply Filter.Eventually.of_forall
    intro N
    have hn : Not ((binaryCutoff N : Real) + 1 = 0) := by positivity
    field_simp [hn]
  exact Filter.Tendsto.congr' heq (by simpa only [zero_mul] using hlim)

theorem log_cutoff_polynomial_div_log_tendsto_zero
    (K E : Nat) (hK : 1 <= K) :
    Tendsto (fun N : Nat => Real.log (((K * (binaryCutoff N + 1) ^ E : Nat) : Real)) /
      Real.log (N : Real)) atTop (nhds 0) := by
  have hKr : (0 : Real) < (K : Real) := by exact_mod_cast (show 0 < K by omega)
  have hlogN : Tendsto (fun N : Nat => Real.log (N : Real)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hconst : Tendsto (fun N : Nat => Real.log (K : Real) / Real.log (N : Real))
      atTop (nhds 0) := tendsto_const_nhds.div_atTop hlogN
  have hlim := hconst.add
    (log_binaryCutoff_succ_div_log_tendsto_zero.const_mul (E : Real))
  have heq : (fun N : Nat => Real.log (K : Real) / Real.log (N : Real) +
      (E : Real) * (Real.log ((binaryCutoff N : Real) + 1) / Real.log (N : Real))) =
      (fun N : Nat => Real.log (((K * (binaryCutoff N + 1) ^ E : Nat) : Real)) /
        Real.log (N : Real)) := by
    funext N
    push_cast
    rw [Real.log_mul (ne_of_gt hKr) (pow_ne_zero E (by positivity)), Real.log_pow]
    ring
  rw [heq] at hlim
  simpa only [mul_zero, add_zero] using hlim

theorem cutoff_polynomial_eventually_le_sample (K E : Nat) (hK : 1 <= K) :
    Filter.Eventually (fun N : Nat => K * (binaryCutoff N + 1) ^ E <= N) atTop := by
  have hlim := log_cutoff_polynomial_div_log_tendsto_zero K E hK
  have hupper := hlim.eventually (eventually_lt_nhds (by norm_num : (0 : Real) < 1))
  have hlogN : Tendsto (fun N : Nat => Real.log (N : Real)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  filter_upwards [hupper, eventually_ge_atTop 1,
    hlogN.eventually (eventually_gt_atTop 0)] with N hN hN1 hlog
  have hNp : (0 : Real) < (N : Real) := by exact_mod_cast (show 0 < N by omega)
  have hP : (0 : Real) < (((K * (binaryCutoff N + 1) ^ E : Nat) : Real)) := by
    exact_mod_cast (Nat.mul_pos (show 0 < K by omega)
      (Nat.pow_pos (by omega : 0 < binaryCutoff N + 1)))
  have hscaled := mul_lt_mul_of_pos_right hN hlog
  have hcancel :
      (Real.log (((K * (binaryCutoff N + 1) ^ E : Nat) : Real)) / Real.log (N : Real)) *
        Real.log (N : Real) =
      Real.log (((K * (binaryCutoff N + 1) ^ E : Nat) : Real)) := by
    field_simp [ne_of_gt hlog]
  rw [hcancel, one_mul] at hscaled
  have hexp := Real.exp_lt_exp.mpr hscaled
  rw [Real.exp_log hP, Real.exp_log hNp] at hexp
  exact_mod_cast le_of_lt hexp

theorem decoderMagnitudeBudget_ge_four_mul
    (N R M : Nat) (hM : 1 <= M) :
    4 * (N : Real) <= decoderIntegerMagnitudeBudget N R M := by
  have hA : (1 : Real) <= 2 * (R : Real) + 1 := by
    have hR : (0 : Real) <= (R : Real) := Nat.cast_nonneg R
    linarith
  have hApow : (1 : Real) <= (2 * (R : Real) + 1) ^ M := by
    calc
      (1 : Real) = (1 : Real) ^ M := by simp
      _ <= (2 * (R : Real) + 1) ^ M := by gcongr
  have hfour : (4 : Real) <= (4 : Real) ^ M := by
    calc
      (4 : Real) = (4 : Real) ^ 1 := by simp
      _ <= (4 : Real) ^ M := by gcongr; norm_num
  unfold decoderIntegerMagnitudeBudget
  calc
    4 * (N : Real) = (N : Real) * 1 * 4 := by ring
    _ <= (N : Real) * (2 * (R : Real) + 1) ^ M * (4 : Real) ^ M := by gcongr

theorem preprocessing_polynomial_bits_eventual
    (h c : Real) (K E : Nat) (hh : 0 < h) (hc : 0 < c) (hK : 1 <= K) :
    Filter.Eventually (fun N : Nat => forall z : Int,
      abs (z : Real) <= (N : Real) + 1 + (((K * (binaryCutoff N + 1) ^ E : Nat) : Real)) ->
      (integerBitWidth z : Real) <= decoderBitConstant h c * Real.log (N : Real)) atTop := by
  filter_upwards [decoder_budget_bits_eventual_bound h c hh hc,
    cutoff_polynomial_eventually_le_sample K E hK, eventually_ge_atTop 1,
    (decoderRank_real_atTop c hc).eventually (eventually_ge_atTop 1)] with N hb hp hN hM
  intro z hz
  have hpR : (((K * (binaryCutoff N + 1) ^ E : Nat) : Real)) <= (N : Real) := by
    exact_mod_cast hp
  have hNr : (1 : Real) <= (N : Real) := by exact_mod_cast hN
  have hMN : 1 <= decoderRank c N := by exact_mod_cast hM
  apply hb
  have hbudget := decoderMagnitudeBudget_ge_four_mul N (decoderRadius h N) (decoderRank c N) hMN
  linarith

end PrimeFactorOscillations.PrimeClassDecoder

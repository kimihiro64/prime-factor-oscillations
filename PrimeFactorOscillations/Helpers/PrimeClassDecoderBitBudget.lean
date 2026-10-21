/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.PrimeClassDecoderErrorExponents
import PrimeFactorOscillations.Helpers.PrimeClassDecoderHornerBounds

/-!
# Logarithmic size of the literal decoder magnitude budget

The rank divided by log N tends to zero. The entire retained Horner
budget has logarithm at most (2+c*h)*log N eventually. The parameter
domain is every positive h,c, independently of class summability.
-/

set_option autoImplicit false
set_option Elab.async false

namespace PrimeFactorOscillations.PrimeClassDecoder

open Filter

noncomputable def decoderIntegerMagnitudeBudget (N R M : Nat) : Real :=
  (N : Real) * (2 * (R : Real) + 1) ^ M * (4 : Real) ^ M

theorem decoderIntegerMagnitudeBudget_one_le (N R M : Nat) (hN : 1 <= N) :
    1 <= decoderIntegerMagnitudeBudget N R M := by
  have hNr : (1 : Real) <= (N : Real) := by exact_mod_cast hN
  have hA : (1 : Real) <= 2 * (R : Real) + 1 := by
    have hR : (0 : Real) <= (R : Real) := Nat.cast_nonneg R
    linarith
  have hpow : (1 : Real) <= (2 * (R : Real) + 1) ^ M := by
    calc
      (1 : Real) = (1 : Real) ^ M := by simp
      _ <= (2 * (R : Real) + 1) ^ M := by gcongr
  have hfour : (1 : Real) <= (4 : Real) ^ M := by
    calc
      (1 : Real) = (1 : Real) ^ M := by simp
      _ <= (4 : Real) ^ M := by gcongr; norm_num
  unfold decoderIntegerMagnitudeBudget
  calc
    (1 : Real) = 1 * 1 * 1 := by ring
    _ <= (N : Real) * (2 * (R : Real) + 1) ^ M * (4 : Real) ^ M := by gcongr

theorem decoderRank_div_log_tendsto_zero (c : Real) (hc : 0 < c) :
    Tendsto (fun N : Nat => (decoderRank c N : Real) / Real.log (N : Real))
      atTop (nhds 0) := by
  have hll : Tendsto (fun N : Nat => Real.log (Real.log (N : Real))) atTop atTop :=
    Real.tendsto_log_atTop.comp (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)
  have hinv : Tendsto (fun N : Nat => (1 : Real) /
      Real.log (Real.log (N : Real))) atTop (nhds 0) :=
    tendsto_const_nhds.div_atTop hll
  have h := (decoderRank_log_scale_tendsto c hc).mul hinv
  have heq : Filter.EventuallyEq atTop
      (fun N : Nat => ((decoderRank c N : Real) *
        Real.log (Real.log (N : Real)) / Real.log (N : Real)) *
          (1 / Real.log (Real.log (N : Real))))
      (fun N : Nat => (decoderRank c N : Real) / Real.log (N : Real)) := by
    filter_upwards [hll.eventually (eventually_gt_atTop 0)] with N hN
    field_simp [ne_of_gt hN]
  exact Filter.Tendsto.congr' heq (by simpa only [mul_zero] using h)

theorem decoderIntegerMagnitudeBudget_log_le
    (N R M : Nat) (hN : 0 < N) (hR : 1 <= R) :
    Real.log (decoderIntegerMagnitudeBudget N R M) <=
      Real.log (N : Real) + (M : Real) * Real.log (2 * (R : Real)) +
        (M : Real) * Real.log 8 := by
  have hNr : (0 : Real) < (N : Real) := by exact_mod_cast hN
  have hRr : (1 : Real) <= (R : Real) := by exact_mod_cast hR
  have htwoR : (0 : Real) < 2 * (R : Real) := by linarith
  have hA : (0 : Real) < 2 * (R : Real) + 1 := by linarith
  have hlogA : Real.log (2 * (R : Real) + 1) <=
      Real.log 2 + Real.log (2 * (R : Real)) := by
    rw [<- Real.log_mul (by norm_num : Not ((2 : Real) = 0)) (ne_of_gt htwoR)]
    exact Real.log_le_log hA (by linarith)
  have hlog8 : Real.log 8 = Real.log 2 + Real.log 4 := by
    rw [<- Real.log_mul (by norm_num : Not ((2 : Real) = 0))
      (by norm_num : Not ((4 : Real) = 0))]
    norm_num
  have hscaled := mul_le_mul_of_nonneg_left hlogA (Nat.cast_nonneg M : (0 : Real) <= M)
  unfold decoderIntegerMagnitudeBudget
  rw [Real.log_mul (mul_ne_zero (ne_of_gt hNr) (pow_ne_zero M (ne_of_gt hA)))
      (pow_ne_zero M (by norm_num)),
    Real.log_mul (ne_of_gt hNr) (pow_ne_zero M (ne_of_gt hA)),
    Real.log_pow, Real.log_pow, hlog8]
  nlinarith

theorem decoder_budget_log_upper_ratio_tendsto
    (h c : Real) (hh : 0 < h) (hc : 0 < c) :
    Tendsto (fun N : Nat => 1 +
      (decoderRank c N : Real) * Real.log (2 * (decoderRadius h N : Real)) /
        Real.log (N : Real) +
      ((decoderRank c N : Real) / Real.log (N : Real)) * Real.log 8)
      atTop (nhds (1 + c * h)) := by
  have hone : Tendsto (fun _ : Nat => (1 : Real)) atTop (nhds 1) := tendsto_const_nhds
  have ht := (hone.add
    (decoder_sampling_growth_exponent_tendsto h c hh hc)).add
      ((decoderRank_div_log_tendsto_zero c hc).mul_const (Real.log 8))
  simpa only [zero_mul, add_zero] using ht

theorem decoder_budget_log_eventual_bound
    (h c : Real) (hh : 0 < h) (hc : 0 < c) :
    Filter.Eventually (fun N : Nat =>
      And (1 <= decoderIntegerMagnitudeBudget N (decoderRadius h N) (decoderRank c N))
        (Real.log (decoderIntegerMagnitudeBudget N (decoderRadius h N) (decoderRank c N)) <=
          (2 + c * h) * Real.log (N : Real))) atTop := by
  have hlimit := decoder_budget_log_upper_ratio_tendsto h c hh hc
  have hupper := hlimit.eventually (eventually_lt_nhds (by linarith :
    1 + c * h < 2 + c * h))
  have hlogN : Tendsto (fun N : Nat => Real.log (N : Real)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  filter_upwards [hupper, eventually_ge_atTop 1,
    (decoderRadius_real_atTop h hh).eventually (eventually_ge_atTop 1),
    hlogN.eventually (eventually_gt_atTop 0)] with N hupper hN hR hlog
  have hRN : 1 <= decoderRadius h N := by exact_mod_cast hR
  apply And.intro (decoderIntegerMagnitudeBudget_one_le N _ _ hN)
  have hbasic := decoderIntegerMagnitudeBudget_log_le N (decoderRadius h N)
    (decoderRank c N) (by omega) hRN
  have hscaled := mul_lt_mul_of_pos_right hupper hlog
  have hcancel :
      (1 + (decoderRank c N : Real) * Real.log (2 * (decoderRadius h N : Real)) /
        Real.log (N : Real) +
        ((decoderRank c N : Real) / Real.log (N : Real)) * Real.log 8) *
        Real.log (N : Real) =
      Real.log (N : Real) + (decoderRank c N : Real) *
        Real.log (2 * (decoderRadius h N : Real)) +
        (decoderRank c N : Real) * Real.log 8 := by
    field_simp [ne_of_gt hlog]
  rw [hcancel] at hscaled
  exact hbasic.trans (le_of_lt hscaled)

end PrimeFactorOscillations.PrimeClassDecoder

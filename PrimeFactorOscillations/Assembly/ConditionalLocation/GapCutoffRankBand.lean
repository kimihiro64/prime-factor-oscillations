/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Assembly.ConditionalLocation.ActualGapCutoff
import PrimeFactorOscillations.Helpers.PrimePrefixCutoffBracket

/-!
# Common rank bands at gap cutoffs

Ordinary prime existence and the exact cutoff supply positive compact
rank bands before comparison with any reference root.
-/

set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace PrimeFactorOscillations
open Filter
open PrimeFactorUnimodality

theorem tendsto_ordinaryGapCutoffPrefix (H : Nat) (hH : 2 <= H) :
    Tendsto (fun k : Nat => primeAt (ordinaryGapCutoffIndex H k) - 1) atTop atTop := by
  apply tendsto_atTop.2
  intro N
  filter_upwards [(tendsto_ordinaryGapCutoffPrime H hH).eventually
    (eventually_ge_atTop ((N : Real) + 1))] with k hk
  have h : N + 1 <= primeAt (ordinaryGapCutoffIndex H k) := by exact_mod_cast hk
  omega

/-- A coarse common rank band is derived from the actual cutoff definition;
no spatial comparison with a reference root is assumed. -/
theorem eventually_gap_cutoff_loglog_bounds (H : Nat) (hH : 2 <= H)
    (b : Real) (hb : 0 < b) (hm : ((H : Real) + 1) * (2 * b) < 1) :
    Filter.Eventually (fun k : Nat =>
      b * k <= Real.log (Real.log (primeAt (ordinaryGapCutoffIndex H k) - 1 : Nat)) /\
      Real.log (Real.log (primeAt (ordinaryGapCutoffIndex H k) - 1 : Nat)) < k) atTop := by
  choose K Q hQ using both_twin_potential_excluded_above_scale 1 (by norm_num)
  have hLarge := ordinary_gap_cutoff_eventually_large H hH (2 * b) (by positivity) hm
  have hQlarge := (tendsto_ordinaryGapCutoffPrime H hH).eventually
    (eventually_ge_atTop (Q : Real))
  have ht : Filter.Eventually (fun k : Nat => 3 <= b * (k : Real)) atTop :=
    ((tendsto_natCast_atTop_atTop : Tendsto (fun k : Nat => (k : Real)) atTop atTop).const_mul_atTop hb).eventually (eventually_ge_atTop 3)
  filter_upwards [hLarge, hQlarge, ht, eventually_ge_atTop K,
    ordinary_gap_cutoff_eventually_spec H hH] with k hlarge hq ht hk hcut
  let C := ordinaryGapCutoffIndex H k
  have hE := four_ceil_double_exp_le_double_exp_double (b * k) ht
  rw [show 2 * (b * (k : Real)) = 2 * b * k by ring] at hE
  have hceil : 4 * Nat.ceil (Real.exp (Real.exp (b * k))) <= primeAt C := by
    exact_mod_cast hE.trans hlarge
  have hcpos : 0 < Nat.ceil (Real.exp (Real.exp (b * k))) := Nat.ceil_pos.mpr (Real.exp_pos _)
  have hcsub : Nat.ceil (Real.exp (Real.exp (b * k))) <= primeAt C - 1 := by omega
  have hEL : Real.exp (Real.exp (b * k)) <= ((primeAt C - 1 : Nat) : Real) :=
    (Nat.le_ceil _).trans (by exact_mod_cast hcsub)
  have hLog := Real.log_le_log (Real.exp_pos (Real.exp (b * k))) hEL
  rw [Real.log_exp] at hLog
  have hLogLog := Real.log_le_log (Real.exp_pos (b * k)) hLog
  rw [Real.log_exp] at hLogLog
  refine And.intro hLogLog ?_
  by_contra hn
  have hNo := (hQ.2.2 k hk C (by exact_mod_cast hq)
    (by simpa only [one_mul] using le_of_not_gt hn)).1
  apply hNo
  refine And.intro hcut.1.1 (And.intro hcut.1.2.1 ?_)
  have hh : (3 : Rat) <= (H : Rat) + 1 := by exact_mod_cast (show 3 <= H + 1 by omega)
  exact hh.trans_lt hcut.1.2.2

theorem eventually_gap_cutoff_logSum_bounds (H : Nat) (hH : 2 <= H)
    (b : Real) (hb : 0 < b) (hm : ((H : Real) + 1) * (2 * b) < 1) :
    Filter.Eventually (fun k : Nat => forall j : Nat,
      j = ordinaryGapCutoffIndex H k \/ j = ordinaryGapCutoffIndex H k + 1 ->
      b / 2 * k <= primePrefixLogSum (primeAt j - 1) /\
      primePrefixLogSum (primeAt j - 1) <= 3 * k) atTop := by
  have hError := tendsto_primePrefixProfile_logSum_error
  have hAbs := (tendsto_order.1 hError).2 (1 : Real) (by norm_num)
  have hLow := (tendsto_order.1 hError).1 (-1 : Real) (by norm_num)
  have hN := tendsto_ordinaryGapCutoffPrefix H hH
  have hHigh := hN.eventually hAbs
  have hLower := hN.eventually hLow
  have hSize : Filter.Eventually (fun k : Nat =>
      2 * (abs Real.eulerMascheroniConstant + 2) <= b * (k : Real) /\
      abs Real.eulerMascheroniConstant + 2 <= (k : Real)) atTop := by
    exact (((tendsto_natCast_atTop_atTop : Tendsto (fun k : Nat => (k : Real)) atTop atTop).const_mul_atTop hb).eventually
      (eventually_ge_atTop _)).and (tendsto_natCast_atTop_atTop.eventually (eventually_ge_atTop _))
  filter_upwards [eventually_gap_cutoff_loglog_bounds H hH b hb hm,
    hHigh, hLower, hSize, hN.eventually (eventually_ge_atTop 1)]
    with k hll hhigh hlow hsize hN1
  let C := ordinaryGapCutoffIndex H k
  let B := primePrefixLogSum (primeAt C - 1)
  change B - Real.eulerMascheroniConstant - Real.log (Real.log (primeAt C - 1 : Nat)) < 1 at hhigh
  change -1 < B - Real.eulerMascheroniConstant - Real.log (Real.log (primeAt C - 1 : Nat)) at hlow
  have hg := le_abs_self Real.eulerMascheroniConstant
  have hg' := neg_abs_le Real.eulerMascheroniConstant
  have hB : b / 2 * k <= B /\ B <= 2 * k := by constructor <;> linarith [hll.1, hll.2, hsize.1, hsize.2]
  intro j hj
  rcases hj with hj | hj
  . subst j
    exact And.intro hB.1 (hB.2.trans (by nlinarith [hsize.2]))
  . subst j
    have hstep := primePrefixLogSum_prime_step_bounds C
    have hNReal : (1 : Real) <= (primeAt C - 1 : Nat) := by exact_mod_cast hN1
    have hInv : 1 / ((primeAt C - 1 : Nat) : Real) <= 1 :=
      (div_le_one (by linarith)).mpr hNReal
    constructor <;> dsimp [B] at * <;> linarith [hstep.1, hstep.2, hsize.2]

end PrimeFactorOscillations

/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.PrimeProfileAscentEligibility
import PrimeFactorOscillations.Helpers.PrimeProfileReferenceCrossing
import PrimeFactorOscillations.Proof.Upper.GapScaleCutoff

/-!
# RH reference envelope for every ordinary ascent

The local reference crossing bounds all ascent endpoints at sufficiently large
rank. Finite endpoints are absorbed explicitly; the terminal-descent theorem
excludes the late range and the uniform RH comparison controls the middle range.
No small-prime-gap supply hypothesis is used.
-/

set_option autoImplicit false
set_option Elab.async false

namespace PrimeFactorOscillations

open Filter

theorem exists_ordinary_ascent_theta_envelope_of_RH (hRH : RiemannHypothesis) :
    exists (A : Real) (K : Nat), 0 < A /\ 2 <= K /\
      forall k : Nat, K <= k -> exists u : Real,
        Set.Ioo (((k - 1 : Nat) : Real) / 3 - A)
          (((k - 1 : Nat) : Real) / 3 + A) u /\
        Nat.factorialConvolution primeProfileRealCoefficient (k - 2) u /
          Nat.factorialConvolution primeProfileRealCoefficient (k - 1) u = 3 /\
        forall i : Nat, ordinaryDensity k i < ordinaryDensity k (i + 1) ->
          Chebyshev.theta ((PrimeFactorUnimodality.primeAt i - 1 : Nat) : Real) <
            Real.exp (Real.exp (u - Real.eulerMascheroniConstant)) := by
  choose A r0 hA hr0 hroot using
    exists_primeProfile_reference_local_crossing (3 : Real) (by norm_num)
  choose rS hrS hsecant using
    exists_primeProfile_reference_secant_bounds (1 : Real) 6 (by norm_num) (by norm_num)
  choose Qc hQc helig using ordinary_ascent_reference_gap_bound_of_RH
    hRH (1 : Real) 6 (by norm_num) (by norm_num)
  choose Kd Qd hKd hQd hdesc using
    both_densities_eventually_descend_above_gap_scale 2 ((1 : Real) / 2) (by norm_num)
  have hdelta : Filter.Eventually (fun N : Nat =>
      Real.log (Real.log (Chebyshev.theta (N : Real))) -
        Real.log (Real.log (N : Real)) < 1) atTop :=
    tendsto_primeProfile_loglogTheta_sub_loglog.eventually
      (gt_mem_nhds (by norm_num : (0 : Real) < 1))
  choose N0 hN0 using hdelta.exists_forall_of_atTop
  let Q := max Qc (max Qd (N0 + 3))
  let g := Real.eulerMascheroniConstant
  let T := Chebyshev.theta (Q : Real)
  choose n0 hn0 using exists_nat_gt (max (3 * (A + g + T + 1) + 1) (2 * (g + 2)))
  let K := max Kd (max (r0 + 1) (max (rS + 1) (n0 + 2)))
  have hKKd : Kd <= K := le_max_left _ _
  have hKr0 : r0 + 1 <= K := (le_max_left _ _).trans (le_max_right _ _)
  have hKrS : rS + 1 <= K :=
    (le_max_left _ _).trans ((le_max_right _ _).trans (le_max_right _ _))
  have hKn : n0 + 2 <= K :=
    (le_max_right _ _).trans ((le_max_right _ _).trans (le_max_right _ _))
  refine Exists.intro A (Exists.intro K (And.intro hA
    (And.intro (hKd.trans hKKd) ?_)))
  intro k hk
  have hk2 : 2 <= k := hKd.trans (hKKd.trans hk)
  have hr0' : r0 <= k - 1 := by omega
  have hrS' : rS <= k - 1 := by omega
  have hcast : ((k - 1 : Nat) : Real) = (k : Real) - 1 := by
    rw [Nat.cast_sub (by omega), Nat.cast_one]
  have hnR : (n0 : Real) < k := by exact_mod_cast (show n0 < k by omega)
  have hlarge := hn0.trans hnR
  have hkfinite : 3 * (A + g + T + 1) + 1 < (k : Real) :=
    (le_max_left _ _).trans_lt hlarge
  have hklate : 2 * (g + 2) < (k : Real) :=
    (le_max_right _ _).trans_lt hlarge
  have hrR : (0 : Real) < (k - 1 : Nat) := by exact_mod_cast (show 0 < k - 1 by omega)
  have hroot' := hroot (k - 1) hr0'
  choose u huI hueq hunique using hroot'.2
  have huBand := hroot'.1 u (And.intro huI.1.le huI.2.le)
  have hu : 0 < u := huBand.1
  have huHigh : ((k - 1 : Nat) : Real) / u <= 6 := by
    simpa only [show (2 : Real) * 3 = 6 by norm_num] using huBand.2.2.1
  have huLarge : g + T + 1 < u := by rw [hcast] at huI; linarith [huI.1]
  have hprev : k - 1 - 1 = k - 2 := by omega
  rw [hprev] at hueq
  refine Exists.intro u (And.intro huI (And.intro hueq ?_))
  intro i hascent
  let p := PrimeFactorUnimodality.primeAt i
  let L := g + Real.log (Real.log (Chebyshev.theta ((p - 1 : Nat) : Real)))
  by_cases hpQ : p < Q
  case pos =>
    have htheta : Chebyshev.theta ((p - 1 : Nat) : Real) <= T := by
      apply Chebyshev.theta_mono
      exact_mod_cast (show p - 1 <= Q by omega)
    have hfirst : T < Real.exp (u - g) := by
      have hexp := Real.add_one_le_exp (u - g)
      linarith
    have hsecond : Real.exp (u - g) < Real.exp (Real.exp (u - g)) := by
      have hexp := Real.add_one_le_exp (Real.exp (u - g))
      linarith
    exact htheta.trans_lt (hfirst.trans hsecond)
  case neg =>
    have hpQ' : Q <= p := le_of_not_gt hpQ
    have hpQc : Qc <= p := (le_max_left _ _).trans hpQ'
    have hpQd : Qd <= p :=
      (le_max_left _ _).trans ((le_max_right _ _).trans hpQ')
    have hpN : N0 + 3 <= p :=
      (le_max_right _ _).trans ((le_max_right _ _).trans hpQ')
    have hp3 : 3 <= p := hQc.trans hpQc
    have hgap := primeAt_gap_ge_two i (show 2 < p by omega)
    have htail : Real.log (Real.log ((p - 1 : Nat) : Real)) < (1 : Real) / 2 * k := by
      by_contra hnot
      have hd := (hdesc k (hKKd.trans hk) i hpQd hgap (le_of_not_gt hnot)).2
      exact (hascent.trans hd).false
    have hdel := hN0 (p - 1) (by omega)
    have hLupper : L < ((k - 1 : Nat) : Real) := by
      dsimp [L, g] at *
      rw [hcast]
      linarith
    by_contra hnot
    have htheta : Real.exp (Real.exp (u - g)) <=
        Chebyshev.theta ((p - 1 : Nat) : Real) := le_of_not_gt hnot
    have hlog := Real.log_le_log (Real.exp_pos _) htheta
    rw [Real.log_exp] at hlog
    have hloglog := Real.log_le_log (Real.exp_pos _) hlog
    rw [Real.log_exp] at hloglog
    have huL : u <= L := by dsimp [L]; linarith
    have hLpos : 0 < L := hu.trans_le huL
    have hLlow : 1 <= ((k - 1 : Nat) : Real) / L := by
      have hc : ((k - 1 : Nat) : Real) / L * L = ((k - 1 : Nat) : Real) := by field_simp
      by_contra hnot
      have hm := mul_lt_mul_of_pos_right (lt_of_not_ge hnot) hLpos
      nlinarith
    have hLhigh : ((k - 1 : Nat) : Real) / L <= 6 := by
      exact (div_le_div_of_nonneg_left hrR.le hu huL).trans huHigh
    have hel := helig i hpQc k hLlow hLhigh hascent
    change (PrimeFactorUnimodality.primeGap i : Real) + 1 <
      Nat.factorialConvolution primeProfileRealCoefficient (k - 2) L /
        Nat.factorialConvolution primeProfileRealCoefficient (k - 1) L at hel
    have hgapR : (2 : Real) <= PrimeFactorUnimodality.primeGap i := by
      exact_mod_cast primeGap_ge_two i (show 2 < p by omega)
    have hsegment (w : Real) (hw : Set.Icc (min L u) (max L u) w) :
        0 < w /\ 1 <= ((k - 1 : Nat) : Real) / w /\
          ((k - 1 : Nat) : Real) / w <= 6 := by
      rw [min_eq_right huL, max_eq_left huL] at hw
      have hwpos : 0 < w := hu.trans_le hw.1
      refine And.intro hwpos (And.intro ?_ ?_)
      . exact hLlow.trans (div_le_div_of_nonneg_left hrR.le hwpos hw.2)
      . exact (div_le_div_of_nonneg_left hrR.le hu hw.1).trans huHigh
    choose q hqlo hqhi hqeq using hsecant (k - 1) hrS' L u hsegment
    rw [hprev, hueq] at hqeq
    have hqpos : 0 <= q := le_of_lt (lt_of_lt_of_le (by positivity) hqlo)
    have hsign : q * (u - L) <= 0 :=
      mul_nonpos_of_nonneg_of_nonpos hqpos (sub_nonpos.mpr huL)
    linarith

end PrimeFactorOscillations

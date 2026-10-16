/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/

import PrimeFactorOscillations.Mathlib.Probability.Distributions.FiniteBernoulliAsymptotics
import PrimeFactorOscillations.Mathlib.Probability.Distributions.FiniteBernoulliRegularLaws

/-!
# Asymptotic budgets for outer peak suppression

Asymptotic budgets for outer peak suppression for the peak-height comparison of regular prime Bernoulli laws.
-/

set_option autoImplicit false
set_option Elab.async false

open Filter Topology

namespace Real

theorem eventually_primePeak_benchmark_budgets (P : Nat)
    (nu gamma rho E : Real) (hnu : 0 < nu) (hgamma : 0 < gamma)
    (_hrho : 0 < rho) (hrg : rho < gamma) (hg1 : gamma < 1) :
    Filter.Eventually (fun k : Nat => 2 <= k /\ P <= k ^ 2 /\
      forall n r : Nat, 2 <= n -> r <= 2 * k ->
        (k : Real) ^ gamma <= log (n : Real) ->
        log (n : Real) <= (k : Real) ^ gamma + log 4 ->
          k ^ 2 <= n /\
          nu * rho * log (k : Real) <=
            nu * (log (log (n : Real)) - log (log (((k ^ 2 : Nat) : Real)))) -
              2 * E - (r : Real) * (2 * nu / (((k ^ 2 : Nat) : Real))) /\
          nu * log (log (n : Real)) + E <= nu * (log (k : Real) + log 2) + E)
      atTop := by
  let A := nu * log 2 + 2 * E + 4 * nu
  have hdelta : 0 < nu * (gamma - rho) := mul_pos hnu (sub_pos.mpr hrg)
  have ha := eventually_loglog_allowance A nu (nu * (gamma - rho)) hdelta
  have ho := _root_.isLittleO_log_rpow_rpow_atTop (1 : Real) hgamma
  have hn := tendsto_natCast_atTop_atTop (R := Real)
  have hd := hn.eventually (ho.bound (by norm_num : (0 : Real) < 1 / 2))
  have h4 := hn.eventually (eventually_ge_atTop (log (4 : Real)))
  filter_upwards [ha, hd, h4, eventually_ge_atTop (max P 2)] with k hkallow hkdom hk4 hk
  have hk2 : 2 <= k := (le_max_right _ _).trans hk
  have hkP : P <= k := (le_max_left _ _).trans hk
  have hk1 : 1 <= k := by omega
  have hkR : 1 <= (k : Real) := by exact_mod_cast hk1
  have hkp : 0 < (k : Real) := zero_lt_one.trans_le hkR
  have hlogk : 0 < log (k : Real) := log_pos (by exact_mod_cast (show 1 < k by omega))
  have hkpow : k <= k ^ 2 := by nlinarith only [hk1]
  have hkpowR : (k : Real) <= (k : Real) ^ 2 := by exact_mod_cast hkpow
  have hrpow : 0 < (k : Real) ^ gamma := rpow_pos_of_pos hkp gamma
  simp only [rpow_one, Real.norm_eq_abs, abs_of_nonneg hlogk.le,
    abs_of_pos hrpow] at hkdom
  have hdom : 2 * log (k : Real) <= (k : Real) ^ gamma := by linarith only [hkdom]
  refine And.intro hk2 (And.intro (hkP.trans hkpow) ?_)
  intro n r hn2 hr hlo hhi
  have hnp : 0 < (n : Real) := by exact_mod_cast (show 0 < n by omega)
  have hlogn : 0 < log (n : Real) := log_pos (by exact_mod_cast (show 1 < n by omega))
  have hkn : k ^ 2 <= n := by
    by_contra hnot
    have hlt : (n : Real) < (k : Real) ^ 2 := by
      exact_mod_cast (show n < k ^ 2 by omega)
    have hh := log_lt_log hnp hlt
    rw [log_pow] at hh
    norm_num at hh
    linarith only [hh, hdom, hlo]
  have hLlo : gamma * log (k : Real) <= log (log (n : Real)) := by
    have hh := log_le_log hrpow hlo
    rw [log_rpow hkp] at hh
    nlinarith only [hh]
  have hlogpow : log (log (((k ^ 2 : Nat) : Real))) = log 2 + log (log (k : Real)) := by
    rw [Nat.cast_pow, log_pow]
    exact log_mul (by norm_num) (ne_of_gt hlogk)
  have hrR : (r : Real) <= 2 * (k : Real) := by exact_mod_cast hr
  have hr2 : (r : Real) <= 2 * (k : Real) ^ 2 := by linarith only [hrR, hkpowR]
  have hcost : (r : Real) * (2 * nu / (((k ^ 2 : Nat) : Real))) <= 4 * nu := by
    rw [Nat.cast_pow]
    have hc : 0 <= 2 * nu / (k : Real) ^ 2 :=
      div_nonneg (mul_nonneg (by norm_num) hnu.le) (sq_nonneg _)
    calc
      _ <= (2 * (k : Real) ^ 2) * (2 * nu / (k : Real) ^ 2) :=
        mul_le_mul_of_nonneg_right hr2 hc
      _ = _ := by field_simp [ne_of_gt hkp]; norm_num
  have hlower :
      nu * rho * log (k : Real) <=
        nu * (log (log (n : Real)) - log (log (((k ^ 2 : Nat) : Real)))) -
          2 * E - (r : Real) * (2 * nu / (((k ^ 2 : Nat) : Real))) := by
    rw [hlogpow]
    have hLL := mul_le_mul_of_nonneg_left hLlo hnu.le
    dsimp [A] at hkallow
    linarith only [hLL, hkallow, hcost]
  have hpowup : (k : Real) ^ gamma <= (k : Real) := by
    rw [rpow_def_of_pos hkp gamma]
    have hh : log (k : Real) * gamma <= log (k : Real) := by
      have hh := mul_le_mul_of_nonneg_left hg1.le hlogk.le
      simpa only [mul_one] using hh
    exact (exp_le_exp.mpr hh).trans_eq (exp_log hkp)
  have hlognup : log (n : Real) <= 2 * (k : Real) := by
    linarith only [hhi, hpowup, hk4]
  have hLup : log (log (n : Real)) <= log (k : Real) + log 2 := by
    have hh := log_le_log hlogn hlognup
    rw [log_mul (by norm_num) (ne_of_gt hkp)] at hh
    linarith only [hh]
  exact And.intro hkn (And.intro hlower
    (add_le_add (mul_le_mul_of_nonneg_left hLup hnu.le) (le_refl E)))

end Real
namespace Real

theorem eventually_log_linear_allowance (A C epsilon : Real) (he : 0 < epsilon) :
    Filter.Eventually (fun k : Nat =>
      A + C * log (k : Real) <= epsilon * (k : Real)) atTop := by
  have ho := (_root_.isLittleO_log_rpow_rpow_atTop (1 : Real)
    (by norm_num : (0 : Real) < 1)).const_mul_left C
  have hn := (tendsto_natCast_atTop_atTop (R := Real)).eventually (ho.bound (half_pos he))
  choose K hK using exists_nat_gt (A / (epsilon / 2))
  filter_upwards [hn, eventually_ge_atTop K] with k hk hkg
  have hk0 : (0 : Real) <= k := Nat.cast_nonneg k
  simp only [rpow_one, Real.norm_eq_abs, abs_of_nonneg hk0] at hk
  have hl : C * log (k : Real) <= (epsilon / 2) * k := (le_abs_self _).trans hk
  have hkr : (K : Real) <= k := by exact_mod_cast hkg
  have hconst := mul_lt_mul_of_pos_right (hK.trans_le hkr) (half_pos he)
  have hc : (A / (epsilon / 2)) * (epsilon / 2) = A := by
    field_simp [ne_of_gt (half_pos he)]
  rw [hc] at hconst
  linarith only [hl, hconst]

theorem eventually_rpow_linear_allowance (gamma epsilon : Real)
    (hg : gamma < 1) (he : 0 < epsilon) :
    Filter.Eventually (fun k : Nat =>
      (k : Real) ^ gamma <= epsilon * (k : Real)) atTop := by
  have ht := (tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop (R := Real))).eventually
    (eventually_ge_atTop (-log epsilon / (1 - gamma)))
  filter_upwards [ht, eventually_ge_atTop 1] with k hk hk1
  have hkp : 0 < (k : Real) := by exact_mod_cast (show 0 < k by omega)
  have hden : 0 < 1 - gamma := sub_pos.mpr hg
  have hh := mul_le_mul_of_nonneg_right hk hden.le
  have hid : (-log epsilon / (1 - gamma)) * (1 - gamma) = -log epsilon := by
    field_simp [ne_of_gt hden]
  rw [hid] at hh
  change -log epsilon <= log (k : Real) * (1 - gamma) at hh
  have hlog : log (k : Real) * gamma <= log epsilon + log (k : Real) := by
    nlinarith only [hh]
  rw [rpow_def_of_pos hkp gamma]
  have hb := exp_le_exp.mpr hlog
  rwa [exp_add, exp_log he, exp_log hkp] at hb

theorem eventually_sublinear_peak_cost (A C D gamma epsilon : Real)
    (hg : gamma < 1) (he : 0 < epsilon) :
    Filter.Eventually (fun k : Nat =>
      A + C * log (k : Real) + D * log (log (k : Real)) +
        (k : Real) ^ gamma < epsilon * (k : Real)) atTop := by
  have hll := eventually_loglog_allowance A D 1 (by norm_num)
  have hl := eventually_log_linear_allowance 0 (C + 1) (epsilon / 3)
    (by positivity)
  have hp := eventually_rpow_linear_allowance gamma (epsilon / 3) hg (by positivity)
  filter_upwards [hll, hl, hp, eventually_ge_atTop 1] with k hkll hkl hkp hk1
  have hkpos : 0 < (k : Real) := by exact_mod_cast (show 0 < k by omega)
  simp only [one_mul] at hkll
  simp only [zero_add] at hkl
  have hpos := mul_pos he hkpos
  linarith only [hkll, hkl, hkp, hpos]

theorem eventually_peak_left_power_separation
    (nu a b A E gamma : Real) (s : Nat)
    (hnu : 0 < nu) (ha : 0 < a) (hab : a < b) (hA : 0 < A) (hg : gamma < 1) :
    Filter.Eventually (fun k : Nat => s <= k /\
      (nu * a * log (k : Real)) ^ k <
        A * exp (-((k : Real) ^ gamma +
          nu * (log (k : Real) + log 2) + E)) *
          (nu * b * log (k : Real)) ^ (k - s)) atTop := by
  have hb : 0 < b := ha.trans hab
  let delta := log b - log a
  have hd : 0 < delta := sub_pos.mpr (log_lt_log ha hab)
  let C0 := (s : Real) * (log nu + log b) + nu * log 2 + E - log A
  have hcost := eventually_sublinear_peak_cost C0 nu (s : Real) gamma delta hg hd
  filter_upwards [hcost, eventually_ge_atTop (max 2 s)] with k hkcost hk
  have hk2 : 2 <= k := (le_max_left _ _).trans hk
  have hsk : s <= k := (le_max_right _ _).trans hk
  have hlogk : 0 < log (k : Real) :=
    log_pos (by exact_mod_cast (show 1 < k by omega))
  let L := nu * a * log (k : Real)
  let B := nu * b * log (k : Real)
  let T := (k : Real) ^ gamma + nu * (log (k : Real) + log 2) + E
  have hL : 0 < L := mul_pos (mul_pos hnu ha) hlogk
  have hB : 0 < B := mul_pos (mul_pos hnu hb) hlogk
  have hLl : log L = log nu + log a + log (log (k : Real)) := by
    dsimp [L]
    rw [log_mul (ne_of_gt (mul_pos hnu ha)) (ne_of_gt hlogk),
      log_mul (ne_of_gt hnu) (ne_of_gt ha)]
  have hBl : log B = log nu + log b + log (log (k : Real)) := by
    dsimp [B]
    rw [log_mul (ne_of_gt (mul_pos hnu hb)) (ne_of_gt hlogk),
      log_mul (ne_of_gt hnu) (ne_of_gt hb)]
  have hdiff : ((k - s : Nat) : Real) = (k : Real) - (s : Real) :=
    Nat.cast_sub hsk
  have hlogleft : log (L ^ k) = (k : Real) *
      (log nu + log a + log (log (k : Real))) := by rw [log_pow, hLl]
  have hlogright : log (A * exp (-T) * B ^ (k - s)) =
      log A - T + ((k : Real) - (s : Real)) *
        (log nu + log b + log (log (k : Real))) := by
    rw [log_mul (ne_of_gt (mul_pos hA (exp_pos _))) (ne_of_gt (pow_pos hB _)),
      log_mul (ne_of_gt hA) (ne_of_gt (exp_pos _)), log_exp, log_pow, hBl, hdiff]
    ring
  have hcompare : log (L ^ k) < log (A * exp (-T) * B ^ (k - s)) := by
    rw [hlogleft, hlogright]
    dsimp [C0, delta] at hkcost
    dsimp [T]
    nlinarith only [hkcost]
  have hexp := exp_lt_exp.mpr hcompare
  rw [exp_log (pow_pos hL _),
    exp_log (mul_pos (mul_pos hA (exp_pos _)) (pow_pos hB _))] at hexp
  exact And.intro hsk hexp

end Real
namespace Real

theorem eventually_peak_right_power_separation
    (A C nu E gamma beta : Real)
    (hA : 0 < A) (hC : 0 < C) (hg : gamma < 1) (hb : 1 < beta) :
    Filter.Eventually (fun k : Nat =>
      C * exp (-((k : Real) ^ beta)) <
        A * exp (-((k : Real) ^ gamma +
          nu * (log (k : Real) + log 2) + E)) / (k : Real) ^ k) atTop := by
  have hcost := eventually_sublinear_peak_cost
    (nu * log 2 + E + log C - log A) nu 0 gamma (1 / 4) hg (by norm_num)
  have ho := _root_.isLittleO_log_rpow_rpow_atTop (1 : Real) (sub_pos.mpr hb)
  have hlog := (tendsto_natCast_atTop_atTop (R := Real)).eventually
    (ho.bound (by norm_num : (0 : Real) < 1 / 4))
  filter_upwards [hcost, hlog, eventually_ge_atTop 2] with k hkcost hklog hk2
  have hkp : 0 < (k : Real) := by exact_mod_cast (show 0 < k by omega)
  have hlogk : 0 <= log (k : Real) :=
    log_nonneg (by exact_mod_cast (show 1 <= k by omega))
  have hrpow : 0 < (k : Real) ^ (beta - 1) := rpow_pos_of_pos hkp _
  simp only [zero_mul, add_zero] at hkcost
  simp only [rpow_one, Real.norm_eq_abs, abs_of_nonneg hlogk,
    abs_of_pos hrpow] at hklog
  have hmult : (k : Real) * (k : Real) ^ (beta - 1) = (k : Real) ^ beta := by
    rw [rpow_def_of_pos hkp (beta - 1), rpow_def_of_pos hkp beta]
    calc
      _ = exp (log (k : Real)) * exp (log (k : Real) * (beta - 1)) := by
        rw [exp_log hkp]
      _ = exp (log (k : Real) + log (k : Real) * (beta - 1)) := (exp_add _ _).symm
      _ = _ := by congr 1; ring
  have hlogterm : (k : Real) * log (k : Real) <= (1 / 4) * (k : Real) ^ beta := by
    have hh := mul_le_mul_of_nonneg_left hklog hkp.le
    nlinarith only [hh, hmult]
  have hpowup : (k : Real) <= (k : Real) ^ beta := by
    have hh : log (k : Real) <= log (k : Real) * beta := by
      have hh := mul_le_mul_of_nonneg_left hb.le hlogk
      simpa only [mul_one] using hh
    have he := exp_le_exp.mpr hh
    rwa [exp_log hkp, <- rpow_def_of_pos hkp beta] at he
  let T := (k : Real) ^ gamma + nu * (log (k : Real) + log 2) + E
  have hll : log (C * exp (-((k : Real) ^ beta))) =
      log C - (k : Real) ^ beta := by
    rw [log_mul (ne_of_gt hC) (ne_of_gt (exp_pos _)), log_exp]
    ring
  have hlr : log (A * exp (-T) / (k : Real) ^ k) =
      log A - T - (k : Real) * log (k : Real) := by
    rw [log_div (ne_of_gt (mul_pos hA (exp_pos _))) (ne_of_gt (pow_pos hkp _)),
      log_mul (ne_of_gt hA) (ne_of_gt (exp_pos _)), log_exp, log_pow]
    ring
  have hcompare : log (C * exp (-((k : Real) ^ beta))) <
      log (A * exp (-T) / (k : Real) ^ k) := by
    rw [hll, hlr]
    dsimp [T]
    have hp := rpow_pos_of_pos hkp beta
    nlinarith only [hkcost, hlogterm, hpowup, hp]
  have he := exp_lt_exp.mpr hcompare
  rw [exp_log (mul_pos hC (exp_pos _)),
    exp_log (div_pos (mul_pos hA (exp_pos _)) (pow_pos hkp _))] at he
  exact he

theorem factorial_le_fixed_base_power (k r : Nat) (hr : r <= k) :
    (r.factorial : Real) <= (k : Real) ^ r := by
  induction r with
  | zero => simp
  | succ r ih =>
      have hi := ih (by omega)
      have hcast : ((r + 1 : Nat) : Real) <= (k : Real) := by exact_mod_cast hr
      rw [Nat.factorial_succ, Nat.cast_mul, pow_succ]
      calc
        _ <= (k : Real) * (k : Real) ^ r :=
          mul_le_mul hcast hi (Nat.cast_nonneg _) (Nat.cast_nonneg _)
        _ = _ := mul_comm _ _

end Real
namespace Real

theorem normalized_reciprocal_error_bound (x nu t b C : Real)
    (hx : 1 <= x) (hnu : 0 < nu) (hC : 0 <= C)
    (herr : abs (t - x / nu - b) <= C / x) :
    abs ((nu / x) * t - 1) <= nu * (abs b + C) / x := by
  have hxp : 0 < x := zero_lt_one.trans_le hx
  have hcoef : 0 <= nu / x := (div_pos hnu hxp).le
  have hid : (nu / x) * t - 1 =
      (nu / x) * (t - x / nu - b) + (nu / x) * b := by
    field_simp [ne_of_gt hxp, ne_of_gt hnu]
    ring
  have hCx : C / x <= C := by
    have hh := div_le_div_of_nonneg_left hC (by norm_num : (0 : Real) < 1) hx
    simpa only [div_one] using hh
  rw [hid]
  calc
    _ <= abs ((nu / x) * (t - x / nu - b)) + abs ((nu / x) * b) := abs_add_le _ _
    _ = (nu / x) * abs (t - x / nu - b) + (nu / x) * abs b := by
      rw [abs_mul, abs_mul, abs_of_nonneg hcoef]
    _ <= (nu / x) * (C / x) + (nu / x) * abs b :=
      add_le_add (mul_le_mul_of_nonneg_left herr hcoef) (le_refl _)
    _ <= (nu / x) * C + (nu / x) * abs b :=
      add_le_add (mul_le_mul_of_nonneg_left hCx hcoef) (le_refl _)
    _ = _ := by ring

end Real
namespace Real

theorem rpow_nat_power_balance (z : Real) (hz : 0 < z) (s1 s2 m1 m2 : Nat) :
    rpow z ((s1 : Real) - (s2 : Real) + (m2 : Real) - (m1 : Real)) *
        z ^ s2 * z ^ m1 = z ^ s1 * z ^ m2 := by
  have hpow (j : Nat) : z ^ j = exp (log z * (j : Real)) := by
    have hh := exp_log (pow_pos hz j)
    rw [log_pow] at hh
    rw [<- hh]
    congr 1
    ring
  have hr : rpow z ((s1 : Real) - (s2 : Real) + (m2 : Real) - (m1 : Real)) =
      exp (log z * ((s1 : Real) - (s2 : Real) + (m2 : Real) - (m1 : Real))) :=
    rpow_def_of_pos hz ((s1 : Real) - (s2 : Real) + (m2 : Real) - (m1 : Real))
  rw [hr, hpow s2, hpow m1, hpow s1, hpow m2,
    <- exp_add, <- exp_add, <- exp_add]
  congr 1
  ring

end Real
namespace Real

theorem regular_localLaw_peak_bounds (x nu eta b C : Real)
    (hx : 1 <= x) (hnu : 0 < nu) (heta0 : 0 < eta) (heta1 : eta < 1) (hC : 0 <= C)
    (herr : abs (1 / eta - x / nu - b) <= C / x)
    (hscale : 2 * (nu * (abs b + C)) <= x)
    (hoddsScale : 2 * nu * (C + abs (b - 1)) <= x) :
    (nu / 2) / x <= eta /\ eta <= 2 * nu / x /\
      (nu / 2) / x <= eta / (1 - eta) /\ eta / (1 - eta) <= 2 * nu / x /\
        abs (eta / (1 - eta) - nu / x) <= 2 * nu ^ 2 * (C + abs (b - 1)) / x ^ 2 := by
  have hxp : 0 < x := zero_lt_one.trans_le hx
  have hCx : C / x <= C := by
    simpa only [div_one] using
      div_le_div_of_nonneg_left hC (by norm_num : (0 : Real) < 1) hx
  have he : 1 / eta - x / nu = (1 / eta - x / nu - b) + b := by ring
  have herror : abs (1 / eta - x / nu) <= C + abs b := by
    rw [he]
    exact ((abs_add_le _ _).trans (add_le_add herr (le_refl _))).trans
      (add_le_add hCx (le_refl _))
  have hscale' : 2 * nu * (C + abs b) <= x := by nlinarith only [hscale]
  have ha := reciprocal_approximation_explicit x nu eta (C + abs b) hxp hnu heta0
    (add_nonneg hC (abs_nonneg _)) herror hscale'
  have ho := regular_localLaw_odds_bounds x nu eta b C hx hnu heta0 heta1 hC herr hoddsScale
  have hlo : (nu / 2) / x <= eta := by simpa only [div_div] using ha.1
  have hol : (nu / 2) / x <= eta / (1 - eta) := by simpa only [div_div] using ho.1
  exact And.intro hlo (And.intro ha.2.1 (And.intro hol (And.intro ho.2.1 ho.2.2)))

end Real


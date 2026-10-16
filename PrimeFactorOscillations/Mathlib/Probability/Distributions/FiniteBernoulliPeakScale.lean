/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/

import PrimeFactorOscillations.Mathlib.Probability.Distributions.FiniteBernoulliLocalization
import PrimeFactorOscillations.Mathlib.Probability.Distributions.FiniteBernoulliPeakBounds

/-!
# Scale calibration and comparison of two attained maxima

Scale calibration and comparison of two attained maxima for the peak-height comparison of regular prime Bernoulli laws.
-/

set_option autoImplicit false
set_option Elab.async false

open Filter Topology

namespace Real

theorem eventually_log_nat_shift_bound (m : Nat -> Nat) (J : Real) (_hJ : 0 <= J)
    (hshift : Filter.Eventually (fun k : Nat => abs ((k : Real) - (m k : Real)) <= J) atTop) :
    Filter.Eventually (fun k : Nat => 2 <= k /\ 2 <= m k /\
      abs (log (m k : Real) - log (k : Real)) <= log 2) atTop := by
  have hb := (tendsto_natCast_atTop_atTop (R := Real)).eventually
    (eventually_ge_atTop (2 * J + 4))
  filter_upwards [hb, hshift, eventually_ge_atTop 2] with k hk hs hk2
  change 2 * J + 4 <= (k : Real) at hk
  have hm2R : (2 : Real) <= (m k : Real) := by
    linarith only [hk, (abs_le.mp hs).2]
  have hm2 : 2 <= m k := by exact_mod_cast hm2R
  have hkp : 0 < (k : Real) := by exact_mod_cast (show 0 < k by omega)
  have hmp : 0 < (m k : Real) := by exact_mod_cast (show 0 < m k by omega)
  have hmup : (m k : Real) <= 2 * (k : Real) := by
    linarith only [hk, (abs_le.mp hs).1]
  have hkup : (k : Real) <= 2 * (m k : Real) := by
    linarith only [hk, (abs_le.mp hs).2]
  have hu := log_le_log hmp hmup
  have hl := log_le_log hkp hkup
  rw [log_mul (by norm_num : Not ((2 : Real) = 0)) (ne_of_gt hkp)] at hu
  rw [log_mul (by norm_num : Not ((2 : Real) = 0)) (ne_of_gt hmp)] at hl
  exact And.intro hk2 (And.intro hm2 (abs_le.mpr
    (And.intro (by linarith only [hl]) (by linarith only [hu]))))

theorem logLog_nat_predecessor_bounds (p : Nat) (hp : 3 <= p) :
    log (log ((p - 1 : Nat) : Real)) <= log (log (p : Real)) /\
      log (log (p : Real)) <= log (log ((p - 1 : Nat) : Real)) + log 2 := by
  have hn2 : 2 <= p - 1 := by omega
  have hnp : 0 < ((p - 1 : Nat) : Real) := by exact_mod_cast (show 0 < p - 1 by omega)
  have hpp : 0 < (p : Real) := by exact_mod_cast (show 0 < p by omega)
  have hlogn : 0 < log ((p - 1 : Nat) : Real) :=
    log_pos (by exact_mod_cast (show 1 < p - 1 by omega))
  have hlogp : 0 < log (p : Real) := log_pos (by exact_mod_cast (show 1 < p by omega))
  have hnle : ((p - 1 : Nat) : Real) <= (p : Real) := by
    exact_mod_cast Nat.sub_le p 1
  have hfirst := log_le_log hlogn (log_le_log hnp hnle)
  have hpe : p - 1 + 1 = p := by omega
  have hsq : p <= (p - 1) ^ 2 := by nlinarith only [hn2, hpe]
  have hsqR : (p : Real) <= (((p - 1 : Nat) : Real)) ^ 2 := by exact_mod_cast hsq
  have hlog := log_le_log hpp hsqR
  rw [log_pow] at hlog
  norm_num at hlog
  have hh := log_le_log hlogp hlog
  rw [log_mul (by norm_num : Not ((2 : Real) = 0)) (ne_of_gt hlogn)] at hh
  exact And.intro hfirst (by linarith only [hh])

theorem tendsto_logLog_predecessor_of_peak_localization
    (m p : Nat -> Nat) (J : Real) (hJ : 0 <= J)
    (hshift : Filter.Eventually (fun k : Nat => abs ((k : Real) - (m k : Real)) <= J) atTop)
    (hp : Filter.Eventually (fun k : Nat => 3 <= p k) atTop)
    (hlocal : forall alpha beta : Real, 0 < alpha -> alpha < 1 -> 1 < beta ->
      Filter.Eventually (fun k : Nat =>
        alpha * log (m k : Real) < log (log (p k : Real)) /\
          log (p k : Real) < (m k : Real) ^ beta) atTop) :
    Tendsto (fun k : Nat =>
      log (log ((p k - 1 : Nat) : Real)) / log (k : Real)) atTop (nhds 1) := by
  have hs := eventually_log_nat_shift_bound m J hJ hshift
  apply Metric.tendsto_nhds.2
  intro e he
  let delta := min (e / 4) (1 / 4)
  have hd : 0 < delta := lt_min (by linarith only [he]) (by norm_num)
  have hdq : delta <= 1 / 4 := min_le_right _ _
  have hde : delta <= e / 4 := min_le_left _ _
  have hda : 0 < 1 - delta := by linarith only [hdq]
  have hdb : 0 < 1 + delta := by linarith only [hd]
  have hl := hlocal (1 - delta) (1 + delta) hda
    (by linarith only [hd]) (by linarith only [hd])
  have hb := eventually_loglog_allowance (2 * log 2) 0 delta hd
  filter_upwards [hs, hp, hl, hb] with k hk hpk hkl hkb
  have hk2 := hk.1
  have hm2 := hk.2.1
  have hlogk : 0 < log (k : Real) := log_pos (by exact_mod_cast (show 1 < k by omega))
  have hmp : 0 < (m k : Real) := by exact_mod_cast (show 0 < m k by omega)
  have hlogp : 0 < log (p k : Real) :=
    log_pos (by exact_mod_cast (show 1 < p k by omega))
  have hpred := logLog_nat_predecessor_bounds (p k) hpk
  have hlog2 : 0 <= log (2 : Real) := (log_pos (by norm_num : (1 : Real) < 2)).le
  have hlowlog : log (k : Real) - log 2 <= log (m k : Real) := by
    linarith only [(abs_le.mp hk.2.2).1]
  have hhighlog : log (m k : Real) <= log (k : Real) + log 2 := by
    linarith only [(abs_le.mp hk.2.2).2]
  have hlowmul := mul_le_mul_of_nonneg_left hlowlog hda.le
  have hhighmul := mul_le_mul_of_nonneg_left hhighlog hdb.le
  have hupper := log_lt_log hlogp hkl.2
  rw [log_rpow hmp] at hupper
  simp only [zero_mul, add_zero] at hkb
  have hdcost := mul_nonneg hd.le hlog2
  have hdcostup : delta * log 2 <= log 2 := by
    have hh := mul_le_mul_of_nonneg_right
      (show delta <= 1 by linarith only [hdq]) hlog2
    simpa only [one_mul] using hh
  have hlo : (1 - 2 * delta) * log (k : Real) <=
      log (log ((p k - 1 : Nat) : Real)) := by
    nlinarith only [hpred.2, hkl.1, hlowmul, hkb, hdcost]
  have hhi : log (log ((p k - 1 : Nat) : Real)) <=
      (1 + 2 * delta) * log (k : Real) := by
    nlinarith only [hpred.1, hupper, hhighmul, hkb, hdcostup]
  have habs : abs (log (log ((p k - 1 : Nat) : Real)) - log (k : Real)) <=
      2 * delta * log (k : Real) := by
    apply abs_le.mpr
    exact And.intro (by linarith only [hlo]) (by linarith only [hhi])
  have hdiv := div_le_div_of_nonneg_right habs hlogk.le
  have hcancel : (2 * delta * log (k : Real)) / log (k : Real) = 2 * delta := by
    field_simp [ne_of_gt hlogk]
  rw [hcancel] at hdiv
  change abs (log (log ((p k - 1 : Nat) : Real)) / log (k : Real) - 1) < e
  have hid : log (log ((p k - 1 : Nat) : Real)) / log (k : Real) - 1 =
      (log (log ((p k - 1 : Nat) : Real)) - log (k : Real)) / log (k : Real) := by
    field_simp [ne_of_gt hlogk]
  rw [hid, abs_div, abs_of_pos hlogk]
  exact hdiv.trans_lt (by linarith only [hde, he])

end Real
namespace Real

theorem primeTilt_sequence_atTop_and_cutoff
    (nu alpha beta : Real) (hnu : 0 < nu) (halpha : 0 < alpha) (hbeta : 0 < beta)
    (n : Nat -> Nat)
    (hband : Filter.Eventually (fun k : Nat => k ^ 2 <= n k /\
      alpha * log (k : Real) <= log (log (n k : Real)) /\
        log (log (n k : Real)) <= beta * log (k : Real)) atTop) :
    let z := fun k : Nat => (k : Real) / (nu * log (log (n k : Real)))
    Tendsto z atTop atTop /\
      Filter.Eventually (fun k : Nat => 0 < z k /\ Nat.floor (z k) <= n k) atTop := by
  let z := fun k : Nat => (k : Real) / (nu * log (log (n k : Real)))
  constructor
  case left =>
    apply Filter.tendsto_atTop.2
    intro Z
    let U := max Z 1
    have hU : 0 < U := zero_lt_one.trans_le (le_max_right _ _)
    have hb := eventually_log_linear_allowance 0 (U * (nu * beta)) 1 (by norm_num)
    filter_upwards [hb, hband, eventually_ge_atTop 2] with k hk hkn hk2
    have hkp : 0 < (k : Real) := by exact_mod_cast (show 0 < k by omega)
    have hlogk : 0 < log (k : Real) := log_pos (by exact_mod_cast (show 1 < k by omega))
    let D := nu * log (log (n k : Real))
    have hD : 0 < D := mul_pos hnu ((mul_pos halpha hlogk).trans_le hkn.2.1)
    have hlarge : U * D <= (k : Real) := by
      have hh := mul_le_mul_of_nonneg_left hkn.2.2 (mul_pos hU hnu).le
      simp only [zero_add, one_mul] at hk
      dsimp [D]
      nlinarith only [hh, hk]
    have hh := div_le_div_of_nonneg_right hlarge hD.le
    have hid : (U * D) / D = U := by field_simp [ne_of_gt hD]
    rw [hid] at hh
    exact (le_max_left Z 1).trans hh
  case right =>
    have hb := eventually_loglog_allowance 1 0 (nu * alpha) (mul_pos hnu halpha)
    filter_upwards [hb, hband, eventually_ge_atTop 2] with k hk hkn hk2
    have hkp : 0 < (k : Real) := by exact_mod_cast (show 0 < k by omega)
    let D := nu * log (log (n k : Real))
    have hD : 1 <= D := by
      have hh := mul_le_mul_of_nonneg_left hkn.2.1 hnu.le
      simp only [zero_mul, add_zero] at hk
      dsimp [D]
      nlinarith only [hh, hk]
    have hDp : 0 < D := zero_lt_one.trans_le hD
    have hz : 0 < z k := div_pos hkp hDp
    have hzk : z k <= (k : Real) := by
      have hh := div_le_div_of_nonneg_left hkp.le (by norm_num : (0 : Real) < 1) hD
      simpa only [div_one] using hh
    have hfloor : Nat.floor (z k) <= k := by
      exact_mod_cast (Nat.floor_le hz.le).trans hzk
    have hkk : k <= k ^ 2 := by nlinarith only [hk2]
    exact And.intro hz (hfloor.trans (hkk.trans hkn.1))

end Real

namespace Real

theorem eventually_prime_cutoff_band_of_log_ratio
    (n : Nat -> Nat) (hn2 : Filter.Eventually (fun k : Nat => 2 <= n k) atTop)
    (hratio : Tendsto (fun k : Nat =>
      log (log (n k : Real)) / log (k : Real)) atTop (nhds 1)) :
    Filter.Eventually (fun k : Nat => k ^ 2 <= n k /\
      (1 / 2 : Real) * log (k : Real) <= log (log (n k : Real)) /\
        log (log (n k : Real)) <= 2 * log (k : Real)) atTop := by
  have hb := (Metric.tendsto_nhds.1 hratio) (1 / 4) (by norm_num)
  have ho := _root_.isLittleO_log_rpow_rpow_atTop (1 : Real)
    (by norm_num : (0 : Real) < 1 / 2)
  have hd := (tendsto_natCast_atTop_atTop (R := Real)).eventually
    (ho.bound (by norm_num : (0 : Real) < 1 / 2))
  filter_upwards [hb, hd, hn2, eventually_ge_atTop 2] with k hk hdom hnk hk2
  have hkp : 0 < (k : Real) := by exact_mod_cast (show 0 < k by omega)
  have hnp : 0 < (n k : Real) := by exact_mod_cast (show 0 < n k by omega)
  have hlk : 0 < log (k : Real) := log_pos (by exact_mod_cast (show 1 < k by omega))
  have hln : 0 < log (n k : Real) := log_pos (by exact_mod_cast (show 1 < n k by omega))
  change abs (log (log (n k : Real)) / log (k : Real) - 1) < 1 / 4 at hk
  have hlow : (1 / 2 : Real) * log (k : Real) <= log (log (n k : Real)) := by
    have hh := mul_lt_mul_of_pos_right (show (3 / 4 : Real) <
      log (log (n k : Real)) / log (k : Real) by linarith only [(abs_lt.mp hk).1]) hlk
    have he : (log (log (n k : Real)) / log (k : Real)) * log (k : Real) =
        log (log (n k : Real)) := by field_simp [ne_of_gt hlk]
    rw [he] at hh
    linarith only [hh, hlk]
  have hhigh : log (log (n k : Real)) <= 2 * log (k : Real) := by
    have hh := mul_lt_mul_of_pos_right (show
      log (log (n k : Real)) / log (k : Real) < (5 / 4 : Real) by
        linarith only [(abs_lt.mp hk).2]) hlk
    have he : (log (log (n k : Real)) / log (k : Real)) * log (k : Real) =
        log (log (n k : Real)) := by field_simp [ne_of_gt hlk]
    rw [he] at hh
    linarith only [hh, hlk]
  have hpw : 0 < (k : Real) ^ (1 / 2 : Real) := rpow_pos_of_pos hkp _
  simp only [rpow_one, Real.norm_eq_abs, abs_of_pos hlk, abs_of_pos hpw] at hdom
  have hlogdom : 2 * log (k : Real) <= (k : Real) ^ (1 / 2 : Real) := by
    linarith only [hdom]
  have hexp := exp_le_exp.mpr hlow
  rw [exp_log hln] at hexp
  have he : (k : Real) ^ (1 / 2 : Real) = exp ((1 / 2 : Real) * log (k : Real)) := by
    rw [rpow_def_of_pos hkp (1 / 2 : Real)]
    congr 1
    ring
  rw [<- he] at hexp
  have hlogn : 2 * log (k : Real) <= log (n k : Real) := hlogdom.trans hexp
  have hkn : k ^ 2 <= n k := by
    by_contra hnot
    have hlt : (n k : Real) < (k : Real) ^ 2 := by exact_mod_cast (show n k < k ^ 2 by omega)
    have hh := log_lt_log hnp hlt
    rw [log_pow] at hh
    norm_num at hh
    linarith only [hh, hlogn]
  exact And.intro hkn (And.intro hlow hhigh)

theorem primeTilt_sequence_standard_scale
    (nu : Real) (hnu : 0 < nu) (n : Nat -> Nat)
    (hn2 : Filter.Eventually (fun k : Nat => 2 <= n k) atTop)
    (hratio : Tendsto (fun k : Nat =>
      log (log (n k : Real)) / log (k : Real)) atTop (nhds 1)) :
    let z := fun k : Nat => (k : Real) / (nu * log (log (n k : Real)))
    let w := fun k : Nat => (k : Real) / (nu * log (k : Real))
    Tendsto (fun k : Nat => z k / w k) atTop (nhds 1) /\
      Tendsto (fun k : Nat => log (z k) / log (k : Real)) atTop (nhds 1) := by
  let z := fun k : Nat => (k : Real) / (nu * log (log (n k : Real)))
  let w := fun k : Nat => (k : Real) / (nu * log (k : Real))
  have hb := eventually_prime_cutoff_band_of_log_ratio n hn2 hratio
  constructor
  case left =>
    have hc : Tendsto (fun _ : Nat => (1 : Real)) atTop (nhds 1) := tendsto_const_nhds
    have hh := hc.div hratio (by norm_num : Not ((1 : Real) = 0))
    have hh' : Tendsto (fun k : Nat =>
        1 / (log (log (n k : Real)) / log (k : Real))) atTop (nhds 1) := by
      change Tendsto (fun k : Nat =>
        (1 : Real) / (log (log (n k : Real)) / log (k : Real)))
          atTop (nhds ((1 : Real) / 1)) at hh
      simpa only [div_one] using hh
    apply hh'.congr'
    filter_upwards [hb, eventually_ge_atTop 2] with k hk hk2
    have hkp : 0 < (k : Real) := by exact_mod_cast (show 0 < k by omega)
    have hlk : 0 < log (k : Real) := log_pos (by exact_mod_cast (show 1 < k by omega))
    have hL : 0 < log (log (n k : Real)) :=
      (mul_pos (by norm_num : (0 : Real) < 1 / 2) hlk).trans_le hk.2.1
    field_simp [ne_of_gt hnu, ne_of_gt hkp, ne_of_gt hlk, ne_of_gt hL]
  case right =>
    apply Metric.tendsto_nhds.2
    intro e he
    let A := abs (log nu) + log 2
    have hcost := eventually_loglog_allowance A 1 (e / 2) (half_pos he)
    have hlog := (tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop (R := Real))).eventually
      (eventually_ge_atTop 1)
    filter_upwards [hb, hcost, hlog, eventually_ge_atTop 2] with k hk hkc hklog hk2
    have hkp : 0 < (k : Real) := by exact_mod_cast (show 0 < k by omega)
    have hlk : 0 < log (k : Real) := log_pos (by exact_mod_cast (show 1 < k by omega))
    let L := log (log (n k : Real))
    have hL : 0 < L :=
      (mul_pos (by norm_num : (0 : Real) < 1 / 2) hlk).trans_le hk.2.1
    have hloglo : log (k : Real) <= 2 * L := by dsimp [L]; linarith only [hk.2.1]
    have hlo := log_le_log hlk hloglo
    rw [log_mul (by norm_num : Not ((2 : Real) = 0)) (ne_of_gt hL)] at hlo
    have hhi := log_le_log hL hk.2.2
    rw [log_mul (by norm_num : Not ((2 : Real) = 0)) (ne_of_gt hlk)] at hhi
    have hLL : 0 <= log (log (k : Real)) := log_nonneg hklog
    have hlogL : abs (log L) <= log (log (k : Real)) + log 2 := by
      apply abs_le.mpr
      exact And.intro (by linarith only [hlo, hLL]) (by linarith only [hhi])
    have habs : abs (log nu + log L) <= A + log (log (k : Real)) := by
      have hh := (abs_add_le (log nu) (log L)).trans (add_le_add (le_refl _) hlogL)
      dsimp [A]
      linarith only [hh]
    simp only [one_mul] at hkc
    have hbound := habs.trans hkc
    have hd := div_le_div_of_nonneg_right hbound hlk.le
    have hcancel : ((e / 2) * log (k : Real)) / log (k : Real) = e / 2 := by
      field_simp [ne_of_gt hlk]
    rw [hcancel] at hd
    have hlogz : log (z k) = log (k : Real) - log nu - log L := by
      change log ((k : Real) / (nu * L)) = _
      rw [log_div (ne_of_gt hkp) (ne_of_gt (mul_pos hnu hL)),
        log_mul (ne_of_gt hnu) (ne_of_gt hL)]
      ring
    change abs (log (z k) / log (k : Real) - 1) < e
    have hid : log (z k) / log (k : Real) - 1 =
        -(log nu + log L) / log (k : Real) := by
      rw [hlogz]
      field_simp [ne_of_gt hlk] <;> ring
    rw [hid, abs_div, abs_neg, abs_of_pos hlk]
    exact hd.trans_lt (half_lt_self he)

theorem tendsto_rpow_ratio_one
    (f g : Nat -> Real) (a : Real)
    (hpos : Filter.Eventually (fun k : Nat => 0 < f k /\ 0 < g k) atTop)
    (hratio : Tendsto (fun k : Nat => f k / g k) atTop (nhds 1)) :
    Tendsto (fun k : Nat => rpow (f k) a / rpow (g k) a) atTop (nhds 1) := by
  have hl := (continuousAt_log (by norm_num : Not ((1 : Real) = 0))).tendsto.comp hratio
  have hc : Tendsto (fun _ : Nat => a) atTop (nhds a) := tendsto_const_nhds
  have he := continuous_exp.continuousAt.tendsto.comp (hc.mul hl)
  have he' : Tendsto (fun k : Nat => exp (a * log (f k / g k))) atTop (nhds 1) := by
    simpa only [log_one, mul_zero, exp_zero, Function.comp_def] using he
  apply he'.congr'
  filter_upwards [hpos] with k hk
  have hf : rpow (f k) a = exp (log (f k) * a) := rpow_def_of_pos hk.1 a
  have hg : rpow (g k) a = exp (log (g k) * a) := rpow_def_of_pos hk.2 a
  rw [hf, hg, <- exp_sub, log_div (ne_of_gt hk.1) (ne_of_gt hk.2)]
  congr 1
  ring

theorem primeTilt_sequence_normalizer_ratio
    (nu E theta : Real) (hnu : 0 < nu) (n : Nat -> Nat)
    (hn2 : Filter.Eventually (fun k : Nat => 2 <= n k) atTop)
    (hratio : Tendsto (fun k : Nat =>
      log (log (n k : Real)) / log (k : Real)) atTop (nhds 1)) :
    let z := fun k : Nat => (k : Real) / (nu * log (log (n k : Real)))
    let w := fun k : Nat => (k : Real) / (nu * log (k : Real))
    Tendsto (fun k : Nat =>
      (rpow (z k) E * rpow (log (z k)) theta) /
        (rpow (w k) E * rpow (log (k : Real)) theta)) atTop (nhds 1) := by
  let z := fun k : Nat => (k : Real) / (nu * log (log (n k : Real)))
  let w := fun k : Nat => (k : Real) / (nu * log (k : Real))
  have hb := eventually_prime_cutoff_band_of_log_ratio n hn2 hratio
  have ht := primeTilt_sequence_atTop_and_cutoff nu (1 / 2) 2 hnu (by norm_num)
    (by norm_num) n hb
  have hs := primeTilt_sequence_standard_scale nu hnu n hn2 hratio
  have hzw : Filter.Eventually (fun k : Nat => 0 < z k /\ 0 < w k) atTop := by
    filter_upwards [ht.2, eventually_ge_atTop 2] with k hk hk2
    have hkp : 0 < (k : Real) := by exact_mod_cast (show 0 < k by omega)
    have hlk : 0 < log (k : Real) := log_pos (by exact_mod_cast (show 1 < k by omega))
    exact And.intro hk.1 (div_pos hkp (mul_pos hnu hlk))
  have hlogs : Filter.Eventually (fun k : Nat => 0 < log (z k) /\ 0 < log (k : Real)) atTop := by
    filter_upwards [ht.1.eventually (eventually_gt_atTop (1 : Real)), eventually_ge_atTop 2]
      with k hk hk2
    exact And.intro (log_pos hk) (log_pos (by exact_mod_cast (show 1 < k by omega)))
  have h1 := tendsto_rpow_ratio_one z w E hzw hs.1
  have h2 := tendsto_rpow_ratio_one (fun k => log (z k)) (fun k => log (k : Real))
    theta hlogs hs.2
  have hm := h1.mul h2
  have hm' : Tendsto (fun k : Nat =>
      (rpow (z k) E / rpow (w k) E) *
        (rpow (log (z k)) theta / rpow (log (k : Real)) theta)) atTop (nhds 1) := by
    simpa only [mul_one] using hm
  apply hm'.congr'
  exact Filter.Eventually.of_forall (fun k => div_mul_div_comm _ _ _ _)

end Real

namespace Real

theorem tendsto_ratio_nat_shift_of_adjacent
    (a : Nat -> Nat -> Real) (r : Nat -> Nat)
    (hpos : forall j : Nat, Filter.Eventually
      (fun k : Nat => 0 < a k (r k + j)) atTop)
    (hadj : forall j : Nat, Tendsto
      (fun k : Nat => a k (r k + j) / a k (r k + j + 1)) atTop (nhds 1)) :
    forall d : Nat, Tendsto
      (fun k : Nat => a k (r k) / a k (r k + d)) atTop (nhds 1) := by
  intro d
  induction d with
  | zero =>
      have hc : Tendsto (fun _ : Nat => (1 : Real)) atTop (nhds 1) :=
        tendsto_const_nhds
      apply hc.congr'
      filter_upwards [hpos 0] with k hk
      simp only [Nat.add_zero] at hk
      simp only [Nat.add_zero, div_self (ne_of_gt hk)]
  | succ d ih =>
      have hm := ih.mul (hadj d)
      have hm' : Tendsto (fun k : Nat =>
          (a k (r k) / a k (r k + d)) *
            (a k (r k + d) / a k (r k + d + 1))) atTop (nhds 1) := by
        simpa only [mul_one] using hm
      apply hm'.congr'
      filter_upwards [hpos d, hpos (d + 1)] with k hb hc
      have hidx : r k + (d + 1) = r k + d + 1 := by omega
      rw [hidx] at hc
      rw [hidx]
      field_simp [ne_of_gt hb, ne_of_gt hc]

end Real
namespace Real

theorem tendsto_two_maximum_ratio
    (u1 u2 v1 v2 F : Nat -> Real) (B : Real)
    (hpos : Filter.Eventually (fun k : Nat =>
      0 <= u1 k /\ 0 < v1 k /\ 0 < v2 k /\ 0 < F k) atTop)
    (hmax : Filter.Eventually (fun k : Nat => u2 k <= u1 k /\ v1 k <= v2 k) atTop)
    (h1 : Tendsto (fun k : Nat => (u1 k / v1 k) / F k) atTop (nhds B))
    (h2 : Tendsto (fun k : Nat => (u2 k / v2 k) / F k) atTop (nhds B)) :
    Tendsto (fun k : Nat => (u1 k / v2 k) / F k) atTop (nhds B) := by
  apply Metric.tendsto_nhds.2
  intro e he
  have hl := (Metric.tendsto_nhds.1 h1) e he
  have hr := (Metric.tendsto_nhds.1 h2) e he
  filter_upwards [hpos, hmax, hl, hr] with k hk hm hkl hkr
  have hlo : (u2 k / v2 k) / F k <= (u1 k / v2 k) / F k :=
    div_le_div_of_nonneg_right
      (div_le_div_of_nonneg_right hm.1 hk.2.2.1.le) hk.2.2.2.le
  have hhi : (u1 k / v2 k) / F k <= (u1 k / v1 k) / F k :=
    div_le_div_of_nonneg_right
      (div_le_div_of_nonneg_left hk.1 hk.2.1 hm.2) hk.2.2.2.le
  change abs ((u1 k / v1 k) / F k - B) < e at hkl
  change abs ((u2 k / v2 k) / F k - B) < e at hkr
  change abs ((u1 k / v2 k) / F k - B) < e
  exact abs_lt.mpr (And.intro
    (by linarith only [(abs_lt.mp hkr).1, hlo])
    (by linarith only [(abs_lt.mp hkl).2, hhi]))

end Real


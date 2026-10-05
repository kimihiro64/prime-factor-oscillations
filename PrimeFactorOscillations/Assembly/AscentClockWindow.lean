/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.PrimeProfileThetaClock
import PrimeFactorOscillations.Proof.Upper.GapScaleCutoff

/-!
# The actual prime-cutoff window for late ordinary ascents

For every fixed positive lower-scale parameter, all late actual ascents
lie below the canonical terminal cutoff and in a single compact clock band.
An arbitrary finite prime threshold is absorbed without changing endpoints.
-/

set_option autoImplicit false
set_option Elab.async false

namespace PrimeFactorOscillations

open Filter

theorem ordinary_ascent_eventually_in_clock_window (a : Real) (ha : 0 < a) (Qreq : Nat) :
    exists K : Nat, 2 <= K /\ forall k : Nat, K <= k -> forall i : Nat,
      Real.exp (Real.exp (a * (k : Real))) <= (PrimeFactorUnimodality.primeAt i : Real) ->
      ordinaryDensity k i < ordinaryDensity k (i + 1) ->
      Qreq <= PrimeFactorUnimodality.primeAt i /\
      PrimeFactorUnimodality.primeAt i <
        Nat.ceil (Real.exp (Real.exp ((k : Real) / 2))) + 1 /\
      let L := Real.eulerMascheroniConstant + Real.log (Real.log
        (Chebyshev.theta ((PrimeFactorUnimodality.primeAt i - 1 : Nat) : Real)))
      0 < L /\ 1 <= ((k - 1 : Nat) : Real) / L /\
        ((k - 1 : Nat) : Real) / L <= max 1 (4 / a) := by
  choose Kd Qd hKd hQd hdesc using
    both_densities_eventually_descend_above_gap_scale 2 ((1 : Real) / 2) (by norm_num)
  have hdelta : Filter.Eventually (fun N : Nat =>
      -1 < Real.log (Real.log (Chebyshev.theta (N : Real))) -
        Real.log (Real.log (N : Real)) /\
      Real.log (Real.log (Chebyshev.theta (N : Real))) -
        Real.log (Real.log (N : Real)) < 1) atTop := by
    filter_upwards [tendsto_primeProfile_loglogTheta_sub_loglog.eventually
      (lt_mem_nhds (by norm_num : (-1 : Real) < 0)),
      tendsto_primeProfile_loglogTheta_sub_loglog.eventually
      (gt_mem_nhds (by norm_num : (0 : Real) < 1))] with N hlow hupp
    exact And.intro hlow hupp
  choose N0 hN0 using hdelta.exists_forall_of_atTop
  let Q := max Qreq (max Qd (N0 + 3))
  let g := Real.eulerMascheroniConstant
  let M := abs g + (Q : Real) + 10
  have hM : 0 < M := by dsimp [M]; positivity
  choose n0 hn0 using exists_nat_gt (max (4 * M / a) (4 * M))
  refine Exists.intro (max Kd (n0 + 3)) (And.intro (hKd.trans (le_max_left _ _)) ?_)
  intro k hk i hcut hascent
  have hkD : Kd <= k := (le_max_left _ _).trans hk
  have hkn : n0 + 3 <= k := (le_max_right _ _).trans hk
  have hk2 : 2 <= k := hKd.trans hkD
  have hkR : (0 : Real) < k := by exact_mod_cast (show 0 < k by omega)
  have hnR : (n0 : Real) < k := by exact_mod_cast (show n0 < k by omega)
  have hlarge := hn0.trans hnR
  have hkBig : 4 * M < (k : Real) := (le_max_right _ _).trans_lt hlarge
  have hka : 4 * M < a * (k : Real) := by
    have h := mul_lt_mul_of_pos_right ((le_max_left _ _).trans_lt hlarge) ha
    have heq : (4 * M / a) * a = 4 * M := by field_simp
    rw [heq] at h
    nlinarith only [h]
  have hak2 : 2 <= a * (k : Real) := by dsimp [M] at hka; nlinarith [abs_nonneg g, (show (0 : Real) <= Q from Nat.cast_nonneg Q)]
  have hakQ : (Q : Real) <= a * (k : Real) := by
    dsimp [M] at hka
    nlinarith [abs_nonneg g, (show (0 : Real) <= Q from Nat.cast_nonneg Q)]
  let p := PrimeFactorUnimodality.primeAt i
  let L := g + Real.log (Real.log (Chebyshev.theta ((p - 1 : Nat) : Real)))
  have hpQ : Q <= p := by
    have h1 := Real.add_one_le_exp (a * (k : Real))
    have h2 := Real.add_one_le_exp (Real.exp (a * (k : Real)))
    have hQR : (Q : Real) <= p := by
      change Real.exp (Real.exp (a * (k : Real))) <= (p : Real) at hcut
      linarith only [h1, h2, hakQ, hcut]
    exact_mod_cast hQR
  have hpReq : Qreq <= p := (le_max_left _ _).trans hpQ
  have hpQd : Qd <= p := (le_max_left _ _).trans ((le_max_right _ _).trans hpQ)
  have hpN : N0 + 3 <= p := (le_max_right _ _).trans ((le_max_right _ _).trans hpQ)
  have hp3 : 3 <= p := by omega
  have hcast : ((p - 1 : Nat) : Real) = (p : Real) - 1 := by
    rw [Nat.cast_sub (by omega), Nat.cast_one]
  have hrcast : ((k - 1 : Nat) : Real) = (k : Real) - 1 := by
    rw [Nat.cast_sub (by omega), Nat.cast_one]
  have htail : Real.log (Real.log ((p - 1 : Nat) : Real)) < (1 : Real) / 2 * k := by
    by_contra hnot
    have hd := (hdesc k hkD i hpQd (primeAt_gap_ge_two i (show 2 < p by omega))
      (le_of_not_gt hnot)).2
    exact (hascent.trans hd).false
  have hpUpper : p < Nat.ceil (Real.exp (Real.exp ((k : Real) / 2))) + 1 := by
    by_contra hnot
    have hpge : Nat.ceil (Real.exp (Real.exp ((k : Real) / 2))) <= p - 1 := by omega
    have hNexp : Real.exp (Real.exp ((k : Real) / 2)) <= ((p - 1 : Nat) : Real) :=
      (Nat.le_ceil _).trans (by exact_mod_cast hpge)
    have hlog := Real.log_le_log (Real.exp_pos _) hNexp
    rw [Real.log_exp] at hlog
    have hloglog := Real.log_le_log (Real.exp_pos _) hlog
    rw [Real.log_exp] at hloglog
    linarith only [htail, hloglog]
  let q := Real.exp (a * (k : Real) / 2)
  have hq2 : 2 <= q := by
    have h := Real.add_one_le_exp (a * (k : Real) / 2)
    dsimp [q]
    linarith only [h, hak2]
  have hq0 : 0 <= q := by dsimp [q]; positivity
  have heq : Real.exp (a * (k : Real)) = q ^ 2 := by
    dsimp [q]
    rw [pow_two, <- Real.exp_add]
    congr 1
    ring
  have hqSquare : q + 1 <= q ^ 2 := by nlinarith only [hq2, sq_nonneg (q - 1)]
  have hExpQ : 1 <= Real.exp q := by linarith [Real.add_one_le_exp q]
  have hExpOne : (2 : Real) <= Real.exp 1 := by linarith [Real.add_one_le_exp (1 : Real)]
  have hplus : Real.exp q + 1 <= Real.exp (q + 1) := by
    rw [Real.exp_add]
    nlinarith [mul_le_mul_of_nonneg_left hExpOne (Real.exp_pos q).le]
  have hsep : Real.exp q + 1 <= Real.exp (Real.exp (a * (k : Real))) := by
    exact hplus.trans (Real.exp_le_exp.mpr (by rw [heq]; exact hqSquare))
  have hNlower : Real.exp q <= ((p - 1 : Nat) : Real) := by
    rw [hcast]
    change Real.exp (Real.exp (a * (k : Real))) <= (p : Real) at hcut
    linarith only [hsep, hcut]
  have hlog := Real.log_le_log (Real.exp_pos _) hNlower
  rw [Real.log_exp] at hlog
  have hloglog := Real.log_le_log (Real.exp_pos (a * (k : Real) / 2)) hlog
  rw [Real.log_exp] at hloglog
  have hdel := hN0 (p - 1) (by omega)
  have hOffset : 1 - g <= a * (k : Real) / 4 := by
    dsimp [M] at hka
    nlinarith [neg_abs_le g, (show (0 : Real) <= Q from Nat.cast_nonneg Q)]
  have hLlower : a * (k : Real) / 4 <= L := by
    dsimp [L]
    linarith only [hdel.1, hloglog, hOffset]
  have hLpos : 0 < L := (div_pos (mul_pos ha hkR) (by norm_num)).trans_le hLlower
  have hkLinear : 2 * (g + 2) < (k : Real) := by
    dsimp [M] at hkBig
    nlinarith [le_abs_self g, (show (0 : Real) <= Q from Nat.cast_nonneg Q)]
  have hLupper : L < ((k - 1 : Nat) : Real) := by
    dsimp [L]
    rw [hrcast]
    linarith only [hdel.2, htail, hkLinear]
  have hLow : 1 <= ((k - 1 : Nat) : Real) / L := by
    have hc : ((k - 1 : Nat) : Real) / L * L = ((k - 1 : Nat) : Real) := by field_simp
    by_contra hnot
    have hm := mul_lt_mul_of_pos_right (lt_of_not_ge hnot) hLpos
    nlinarith only [hc, hm, hLupper]
  have hrle : ((k - 1 : Nat) : Real) <= k := by exact_mod_cast Nat.sub_le k 1
  have hHigh : ((k - 1 : Nat) : Real) / L <= 4 / a := by
    calc
      ((k - 1 : Nat) : Real) / L <= (k : Real) / L :=
        div_le_div_of_nonneg_right hrle hLpos.le
      _ <= (k : Real) / (a * (k : Real) / 4) :=
        div_le_div_of_nonneg_left hkR.le (by positivity) hLlower
      _ = 4 / a := by field_simp
  exact And.intro hpReq (And.intro hpUpper
    (And.intro hLpos (And.intro hLow (hHigh.trans (le_max_right _ _)))))

end PrimeFactorOscillations

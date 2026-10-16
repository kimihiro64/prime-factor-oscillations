/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/

import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import PrimeFactorOscillations.Mathlib.Probability.Distributions.FiniteBernoulliTiltComparison

/-! # Regular local laws and uniform tilted-probability comparison

Explicit reciprocal inversion turns the local law's second-order error into
odds bounds with a common reciprocal slope. The exact probability-tilt identity
then supplies a total coordinate-change bound uniform in cutoff and tilt.
All cutoffs, interior probability conditions and denominator signs are explicit.
-/

set_option autoImplicit false
set_option Elab.async false

namespace Real

/-- Explicit inversion of a bounded perturbation of a positive linear reciprocal. -/
theorem reciprocal_approximation_explicit (x nu a B : Real)
    (hx : 0 < x) (hnu : 0 < nu) (ha : 0 < a) (hB : 0 <= B)
    (herror : abs (1 / a - x / nu) <= B) (hscale : 2 * nu * B <= x) :
    nu / (2 * x) <= a /\ a <= 2 * nu / x /\
      abs (a - nu / x) <= 2 * nu ^ 2 * B / x ^ 2 := by
  have hid : (1 / a - x / nu) * nu = nu / a - x := by field_simp
  have hlo := mul_le_mul_of_nonneg_right (abs_le.mp herror).1 hnu.le
  have hhi := mul_le_mul_of_nonneg_right (abs_le.mp herror).2 hnu.le
  rw [hid] at hlo hhi
  have hl : x <= 2 * (nu / a) := by linarith only [hlo, hscale]
  have hu : nu / a <= 2 * x := by linarith only [hhi, hscale, hx]
  have hlam : x * a <= 2 * nu := by
    calc
      x * a <= (2 * (nu / a)) * a := mul_le_mul_of_nonneg_right hl ha.le
      _ = 2 * nu := by field_simp
  have huam : nu <= (2 * x) * a := by
    calc
      nu = (nu / a) * a := by field_simp
      _ <= (2 * x) * a := mul_le_mul_of_nonneg_right hu ha.le
  have halow : nu / (2 * x) <= a := by
    have hh := mul_le_mul_of_nonneg_right huam
      (div_nonneg (show (0 : Real) <= 1 by norm_num)
        (mul_pos (show (0 : Real) < 2 by norm_num) hx).le)
    have hc : ((2 * x) * a) * (1 / (2 * x)) = a := by field_simp
    simpa only [hc, mul_one_div] using hh
  have haup : a <= 2 * nu / x := by
    have hh := mul_le_mul_of_nonneg_right hlam
      (div_nonneg (show (0 : Real) <= 1 by norm_num) hx.le)
    have hc : (x * a) * (1 / x) = a := by field_simp
    simpa only [hc, mul_one_div] using hh
  have heq : a - nu / x = (a * nu / x) * (x / nu - 1 / a) := by field_simp
  have habs : abs (a - nu / x) = (a * nu / x) * abs (1 / a - x / nu) := by
    rw [heq, abs_mul, abs_of_pos (div_pos (mul_pos ha hnu) hx), abs_sub_comm]
  have hfinal : abs (a - nu / x) <= 2 * nu ^ 2 * B / x ^ 2 := by
    rw [habs]
    calc
      _ <= (a * nu / x) * B :=
        mul_le_mul_of_nonneg_left herror (div_pos (mul_pos ha hnu) hx).le
      _ = a * (nu * B / x) := by ring
      _ <= (2 * nu / x) * (nu * B / x) :=
        mul_le_mul_of_nonneg_right haup (div_nonneg (mul_nonneg hnu.le hB) hx.le)
      _ = 2 * nu ^ 2 * B / x ^ 2 := by field_simp
  exact And.intro halow (And.intro haup hfinal)

/-- The reciprocal regularity hypothesis on a local probability gives
explicit first-order odds bounds beyond its stated linear cutoff. -/
theorem regular_localLaw_odds_bounds (x nu eta b C : Real)
    (hx1 : 1 <= x) (hnu : 0 < nu)
    (heta0 : 0 < eta) (heta1 : eta < 1) (hC : 0 <= C)
    (herror : abs (1 / eta - x / nu - b) <= C / x)
    (hscale : 2 * nu * (C + abs (b - 1)) <= x) :
    nu / (2 * x) <= eta / (1 - eta) /\
      eta / (1 - eta) <= 2 * nu / x /\
      abs (eta / (1 - eta) - nu / x) <=
        2 * nu ^ 2 * (C + abs (b - 1)) / x ^ 2 := by
  have hx : 0 < x := lt_of_lt_of_le zero_lt_one hx1
  have ha : 0 < eta / (1 - eta) := div_pos heta0 (sub_pos.mpr heta1)
  have hB : 0 <= C + abs (b - 1) := add_nonneg hC (abs_nonneg _)
  have heq : 1 / (eta / (1 - eta)) - x / nu =
      (1 / eta - x / nu - b) + (b - 1) := by
    field_simp
    ring
  have hsmall : C / x <= C := by
    have hi := one_div_le_one_div_of_le zero_lt_one hx1
    have hh := mul_le_mul_of_nonneg_left hi hC
    simpa only [div_one, mul_one, mul_one_div] using hh
  have herr : abs (1 / (eta / (1 - eta)) - x / nu) <= C + abs (b - 1) := by
    rw [heq]
    calc
      _ <= abs (1 / eta - x / nu - b) + abs (b - 1) := abs_add_le _ _
      _ <= C / x + abs (b - 1) := add_le_add herror (le_refl _)
      _ <= C + abs (b - 1) := add_le_add hsmall (le_refl _)
  exact reciprocal_approximation_explicit x nu (eta / (1 - eta))
    (C + abs (b - 1)) hx hnu ha hB herr hscale

/-- Two regular laws with the same reciprocal slope have a uniform
reciprocal-square odds difference. -/
theorem regular_localLaws_odds_difference (x nu eta1 eta2 b1 b2 C1 C2 : Real)
    (hx1 : 1 <= x) (hnu : 0 < nu)
    (h10 : 0 < eta1) (h11 : eta1 < 1) (h20 : 0 < eta2) (h21 : eta2 < 1)
    (hC1 : 0 <= C1) (hC2 : 0 <= C2)
    (herr1 : abs (1 / eta1 - x / nu - b1) <= C1 / x)
    (herr2 : abs (1 / eta2 - x / nu - b2) <= C2 / x)
    (hscale : 2 * nu * ((C1 + abs (b1 - 1)) + (C2 + abs (b2 - 1))) <= x) :
    (nu / 2) / x <= eta1 / (1 - eta1) /\
      (nu / 2) / x <= eta2 / (1 - eta2) /\
      abs (eta1 / (1 - eta1) - eta2 / (1 - eta2)) <=
        (2 * nu ^ 2 * ((C1 + abs (b1 - 1)) + (C2 + abs (b2 - 1)))) / x ^ 2 := by
  have hx : 0 < x := lt_of_lt_of_le zero_lt_one hx1
  have hB1 : 0 <= C1 + abs (b1 - 1) := add_nonneg hC1 (abs_nonneg _)
  have hB2 : 0 <= C2 + abs (b2 - 1) := add_nonneg hC2 (abs_nonneg _)
  have hs1 : 2 * nu * (C1 + abs (b1 - 1)) <= x := by
    have hh := mul_nonneg (mul_pos (show (0 : Real) < 2 by norm_num) hnu).le hB2
    nlinarith only [hscale, hh]
  have hs2 : 2 * nu * (C2 + abs (b2 - 1)) <= x := by
    have hh := mul_nonneg (mul_pos (show (0 : Real) < 2 by norm_num) hnu).le hB1
    nlinarith only [hscale, hh]
  have ha := regular_localLaw_odds_bounds x nu eta1 b1 C1 hx1 hnu h10 h11 hC1 herr1 hs1
  have hb := regular_localLaw_odds_bounds x nu eta2 b2 C2 hx1 hnu h20 h21 hC2 herr2 hs2
  have hid : (nu / 2) / x = nu / (2 * x) := by ring
  refine And.intro (by rw [hid]; exact ha.1)
    (And.intro (by rw [hid]; exact hb.1) ?_)
  calc
    _ <= abs (eta1 / (1 - eta1) - nu / x) +
        abs (nu / x - eta2 / (1 - eta2)) := abs_sub_le _ _ _
    _ = abs (eta1 / (1 - eta1) - nu / x) +
        abs (eta2 / (1 - eta2) - nu / x) := by rw [abs_sub_comm (nu / x)]
    _ <= 2 * nu ^ 2 * (C1 + abs (b1 - 1)) / x ^ 2 +
        2 * nu ^ 2 * (C2 + abs (b2 - 1)) / x ^ 2 :=
      add_le_add ha.2.2 hb.2.2
    _ = _ := by ring

/-- The probability tilt used in coefficient extraction equals the odds tilt. -/
theorem localLaw_tilt_eq_odds_tilt (eta z : Real)
    (heta0 : 0 < eta) (heta1 : eta < 1) (hz : 0 < z) :
    eta * z / (1 + (z - 1) * eta) =
      z * (eta / (1 - eta)) / (1 + z * (eta / (1 - eta))) := by
  have hm : 0 < 1 - eta := sub_pos.mpr heta1
  have hdf : 0 < 1 - eta + eta * z := add_pos hm (mul_pos heta0 hz)
  have heq1 : 1 + (z - 1) * eta = 1 - eta + eta * z := by ring
  have heq2 : 1 + z * (eta / (1 - eta)) =
      (1 - eta + eta * z) / (1 - eta) := by field_simp
  rw [heq1, heq2]
  field_simp [ne_of_gt hm, ne_of_gt hdf]

/-- Positive odds give a strictly interior probability. -/
theorem oddsProbability_mem_open (x : Real) (hx : 0 < x) :
    0 < x / (1 + x) /\ x / (1 + x) < 1 := by
  have hd : 0 < 1 + x := by linarith
  exact And.intro (div_pos hx hd) ((div_lt_one hd).mpr (by linarith))

/-- Converting nonnegative odds to a probability and back is exact. -/
theorem oddsProbability_odds (x : Real) (hx : 0 <= x) :
    (x / (1 + x)) / (1 - x / (1 + x)) = x := by
  have hd : Not (1 + x = 0) := ne_of_gt (by linarith)
  have he : 1 - x / (1 + x) = 1 / (1 + x) := by field_simp; ring
  rw [he]
  field_simp



theorem abs_log_one_add_sub_self_le_two_sq (u : Real) (hu : abs u <= 1 / 2) :
    abs (log (1 + u) - u) <= 2 * u ^ 2 := by
  have hlo : -(1 / 2) <= u := (abs_le.mp hu).1
  have hd : 0 < 1 + u := by linarith only [hlo]
  have hdhalf : 1 / 2 <= 1 + u := by linarith only [hlo]
  have hup := log_le_sub_one_of_pos hd
  have hinv := log_le_sub_one_of_pos (inv_pos.mpr hd)
  rw [log_inv] at hinv
  have hid : 1 / (1 + u) - 1 = -u / (1 + u) := by
    field_simp [ne_of_gt hd]
    ring
  have hinv2 : -log (1 + u) <= -u / (1 + u) := by
    calc
      _ <= 1 / (1 + u) - 1 := by simpa only [one_div] using hinv
      _ = _ := hid
  rw [neg_div] at hinv2
  have hnonpos : log (1 + u) - u <= 0 := by linarith only [hup]
  rw [abs_of_nonpos hnonpos]
  calc
    _ <= u - u / (1 + u) := by linarith only [hinv2]
    _ = u ^ 2 / (1 + u) := by field_simp [ne_of_gt hd]; ring
    _ <= u ^ 2 / (1 / 2) :=
      div_le_div_of_nonneg_left (sq_nonneg u) (by norm_num) hdhalf
    _ = _ := by ring

theorem reciprocalRegularity_log_explicit (x nu eta b C : Real)
    (hx : 1 <= x) (hnu : 0 < nu) (heta : 0 < eta) (hC : 0 <= C)
    (herr : abs (1 / eta - x / nu - b) <= C / x)
    (hscale : 2 * (nu * (abs b + C)) <= x) :
    abs (log eta - (log nu - log x - nu * b / x)) <=
      (2 * (nu * (abs b + C)) ^ 2 + nu * C) / x ^ 2 := by
  have hx0 : 0 < x := zero_lt_one.trans_le hx
  have hxne := ne_of_gt hx0
  have hnune := ne_of_gt hnu
  have hetane := ne_of_gt heta
  let u := nu / (x * eta) - 1
  let T := nu * (abs b + C)
  have hT : 0 <= T := mul_nonneg hnu.le (add_nonneg (abs_nonneg _) hC)
  have huid : u - nu * b / x = (nu / x) * (1 / eta - x / nu - b) := by
    dsimp [u]
    field_simp [hxne, hnune, hetane]
  have huerr : abs (u - nu * b / x) <= nu * C / x ^ 2 := by
    rw [huid, abs_mul, abs_of_pos (div_pos hnu hx0)]
    calc
      _ <= (nu / x) * (C / x) := mul_le_mul_of_nonneg_left herr (div_pos hnu hx0).le
      _ = _ := by ring
  have hxx : x <= x ^ 2 := by nlinarith only [hx]
  have hsmall : nu * C / x ^ 2 <= nu * C / x :=
    div_le_div_of_nonneg_left (mul_nonneg hnu.le hC) hx0 hxx
  have huT : abs u <= T / x := by
    calc
      _ <= abs (u - nu * b / x) + abs (nu * b / x) := by
        have hh := abs_add_le (u - nu * b / x) (nu * b / x)
        simpa only [sub_add_cancel] using hh
      _ <= nu * C / x ^ 2 + abs (nu * b / x) := add_le_add huerr (le_refl _)
      _ <= nu * C / x + abs (nu * b / x) := add_le_add hsmall (le_refl _)
      _ = T / x := by
        rw [abs_div, abs_mul, abs_of_pos hnu, abs_of_pos hx0]
        dsimp [T]
        ring
  have hhalf : T / x <= 1 / 2 := by
    have hh := div_le_div_of_nonneg_right hscale hx0.le
    rw [div_self hxne] at hh
    have hid : 2 * T / x = 2 * (T / x) := by ring
    rw [hid] at hh
    linarith only [hh]
  have hquad := abs_log_one_add_sub_self_le_two_sq u (huT.trans hhalf)
  have hprod := mul_le_mul huT huT (abs_nonneg u) (div_nonneg hT hx0.le)
  have huSq : u ^ 2 <= (T / x) ^ 2 := by
    simpa only [<- pow_two, sq_abs] using hprod
  have hlog : log (1 + u) = log nu - log x - log eta := by
    have hid : 1 + u = nu / (x * eta) := by dsimp [u]; ring
    rw [hid, log_div hnune (mul_ne_zero hxne hetane), log_mul hxne hetane]
    ring
  have hid : log eta - (log nu - log x - nu * b / x) =
      -((log (1 + u) - u) + (u - nu * b / x)) := by
    rw [hlog]
    ring
  rw [hid, abs_neg]
  calc
    _ <= abs (log (1 + u) - u) + abs (u - nu * b / x) := abs_add_le _ _
    _ <= 2 * u ^ 2 + nu * C / x ^ 2 := add_le_add hquad huerr
    _ <= 2 * (T / x) ^ 2 + nu * C / x ^ 2 :=
      add_le_add (mul_le_mul_of_nonneg_left huSq (by norm_num)) (le_refl _)
    _ = _ := by dsimp [T]; ring

theorem reciprocalRegularity_renormalized_log_ratio_bound
    (x nu eta1 eta2 b1 b2 C1 C2 : Real)
    (hx : 2 <= x) (hnu : 0 < nu) (h1 : 0 < eta1) (h2 : 0 < eta2)
    (hC1 : 0 <= C1) (hC2 : 0 <= C2)
    (herr1 : abs (1 / eta1 - x / nu - b1) <= C1 / x)
    (herr2 : abs (1 / eta2 - x / nu - b2) <= C2 / x)
    (hscale1 : 2 * (nu * (abs b1 + C1)) <= x)
    (hscale2 : 2 * (nu * (abs b2 + C2)) <= x) :
    abs (log eta1 - log eta2 + (nu * (b2 - b1)) * log (1 - 1 / x)) <=
      ((2 * (nu * (abs b1 + C1)) ^ 2 + nu * C1) +
        (2 * (nu * (abs b2 + C2)) ^ 2 + nu * C2) +
          2 * abs (nu * (b2 - b1))) / x ^ 2 := by
  have hx1 : 1 <= x := by linarith only [hx]
  have hx0 : 0 < x := by linarith only [hx]
  have ha := reciprocalRegularity_log_explicit x nu eta1 b1 C1 hx1 hnu h1 hC1
    herr1 hscale1
  have hb := reciprocalRegularity_log_explicit x nu eta2 b2 C2 hx1 hnu h2 hC2
    herr2 hscale2
  have hhalf : abs (-(1 / x)) <= 1 / 2 := by
    rw [abs_neg, abs_of_pos (div_pos (by norm_num) hx0)]
    exact one_div_le_one_div_of_le (by norm_num) hx
  have hc := abs_log_one_add_sub_self_le_two_sq (-(1 / x)) hhalf
  have hct : abs (log (1 - 1 / x) + 1 / x) <= 2 / x ^ 2 := by
    have harg : 1 + -(1 / x) = 1 - 1 / x := by ring
    rw [harg, sub_neg_eq_add, neg_sq, one_div_pow] at hc
    convert hc using 1
    ring
  let theta := nu * (b2 - b1)
  have hid : log eta1 - log eta2 + theta * log (1 - 1 / x) =
      (log eta1 - (log nu - log x - nu * b1 / x)) -
        (log eta2 - (log nu - log x - nu * b2 / x)) +
          theta * (log (1 - 1 / x) + 1 / x) := by dsimp [theta]; ring
  change abs (log eta1 - log eta2 + theta * log (1 - 1 / x)) <= _
  rw [hid]
  calc
    _ <= abs ((log eta1 - (log nu - log x - nu * b1 / x)) -
        (log eta2 - (log nu - log x - nu * b2 / x))) +
          abs (theta * (log (1 - 1 / x) + 1 / x)) := abs_add_le _ _
    _ <= (abs (log eta1 - (log nu - log x - nu * b1 / x)) +
        abs (log eta2 - (log nu - log x - nu * b2 / x))) +
          abs theta * abs (log (1 - 1 / x) + 1 / x) := by
      rw [abs_mul]
      exact add_le_add (abs_sub _ _) (le_refl _)
    _ <= ((2 * (nu * (abs b1 + C1)) ^ 2 + nu * C1) / x ^ 2 +
        (2 * (nu * (abs b2 + C2)) ^ 2 + nu * C2) / x ^ 2) +
          abs theta * (2 / x ^ 2) :=
      add_le_add (add_le_add ha hb) (mul_le_mul_of_nonneg_left hct (abs_nonneg theta))
    _ = _ := by dsimp [theta]; ring

end Real

namespace Finset

/-- The original reciprocal regularity assumptions give total probability
change bounded uniformly in every finite cutoff and every tilt at least one. -/
theorem sum_abs_regularLocalLaw_tilt_sub_le (S : Finset Nat) (N : Nat)
    (hSN : forall p, Membership.mem S p -> Membership.mem (range N) p)
    (eta1 eta2 : Nat -> Real) (nu b1 b2 C1 C2 z : Real)
    (hnu : 0 < nu) (hC1 : 0 <= C1) (hC2 : 0 <= C2) (hz1 : 1 <= z)
    (hindex : forall p, Membership.mem S p -> 1 <= p)
    (h1 : forall p, Membership.mem S p -> 0 < eta1 p /\ eta1 p < 1)
    (h2 : forall p, Membership.mem S p -> 0 < eta2 p /\ eta2 p < 1)
    (herr1 : forall p, Membership.mem S p ->
      abs (1 / eta1 p - (p : Real) / nu - b1) <= C1 / (p : Real))
    (herr2 : forall p, Membership.mem S p ->
      abs (1 / eta2 p - (p : Real) / nu - b2) <= C2 / (p : Real))
    (hscale : forall p, Membership.mem S p ->
      2 * nu * ((C1 + abs (b1 - 1)) + (C2 + abs (b2 - 1))) <= (p : Real)) :
    S.sum (fun p => abs (eta1 p * z / (1 + (z - 1) * eta1 p) -
      eta2 p * z / (1 + (z - 1) * eta2 p))) <=
      (2 * nu ^ 2 * ((C1 + abs (b1 - 1)) + (C2 + abs (b2 - 1)))) *
        (1 / (nu / 2) ^ 2 + 1 / (nu / 2)) := by
  let a := fun p => eta1 p / (1 - eta1 p)
  let b := fun p => eta2 p / (1 - eta2 p)
  let B := (C1 + abs (b1 - 1)) + (C2 + abs (b2 - 1))
  let K := 2 * nu ^ 2 * B
  have hc : 0 < nu / 2 := div_pos hnu (by norm_num)
  have hB : 0 <= B :=
    add_nonneg (add_nonneg hC1 (abs_nonneg _)) (add_nonneg hC2 (abs_nonneg _))
  have hK : 0 <= K := mul_nonneg
    (mul_nonneg (show (0 : Real) <= 2 by norm_num) (sq_nonneg nu)) hB
  have hpair (p : Nat) (hp : Membership.mem S p) :
      (nu / 2) / (p : Real) <= a p /\
        (nu / 2) / (p : Real) <= b p /\
        abs (a p - b p) <= K / (p : Real) ^ 2 := by
    have hx : (1 : Real) <= (p : Real) := by exact_mod_cast hindex p hp
    exact Real.regular_localLaws_odds_difference (p : Real) nu
      (eta1 p) (eta2 p) b1 b2 C1 C2 hx hnu
      (h1 p hp).1 (h1 p hp).2 (h2 p hp).1 (h2 p hp).2 hC1 hC2
      (herr1 p hp) (herr2 p hp) (hscale p hp)
  have hh := sum_abs_tiltOdds_sub_le S N hSN a b (nu / 2) K z hc hK hz1 hindex
    (fun p hp => (hpair p hp).1)
    (fun p hp => (hpair p hp).2.1)
    (fun p hp => (hpair p hp).2.2)
  have hz : 0 < z := lt_of_lt_of_le zero_lt_one hz1
  have heq :
      S.sum (fun p => abs (eta1 p * z / (1 + (z - 1) * eta1 p) -
        eta2 p * z / (1 + (z - 1) * eta2 p))) =
      S.sum (fun p => abs (z * a p / (1 + z * a p) -
        z * b p / (1 + z * b p))) := by
    apply sum_congr rfl
    intro p hp
    rw [Real.localLaw_tilt_eq_odds_tilt (eta1 p) z (h1 p hp).1 (h1 p hp).2 hz,
      Real.localLaw_tilt_eq_odds_tilt (eta2 p) z (h2 p hp).1 (h2 p hp).2 hz]
  rw [heq]
  exact hh

end Finset

/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.AscentEndpoints
import PrimeFactorOscillations.Helpers.PrimeCountingLocation

/-!
# Asymptotic of the actual theta endpoint count

The strict condition theta(p-1)<T is retained in finite prime-set injections.
A positive lower-cutoff margin and an explicit small-prime bound give a
prime-count sandwich, which the actual PNT normalizes to T/log(T).
-/

set_option autoImplicit false
set_option Elab.async false

namespace PrimeFactorOscillations

open Filter Asymptotics

theorem tendsto_primeCounting_scaled_mainTerm (a : Real) (ha : 0 < a) :
    Tendsto (fun T : Real => (Nat.primeCounting (Nat.floor (a * T)) : Real) /
      (T / Real.log T)) atTop (nhds a) := by
  have hgrow : Tendsto (fun T : Real => a * T) atTop atTop :=
    (tendsto_id : Tendsto (fun T : Real => T) atTop atTop).const_mul_atTop ha
  have hne : Filter.Eventually (fun T : Real =>
      Not ((a * T / Real.log (a * T)) = 0)) atTop := by
    filter_upwards [hgrow.eventually_gt_atTop 1] with T hT
    exact div_ne_zero (zero_lt_one.trans hT).ne' (Real.log_pos hT).ne'
  have heq := primeCounting_isEquivalent_div_log.comp_tendsto hgrow
  have hr := (Asymptotics.isEquivalent_iff_tendsto_one hne).mp heq
  have hratio : Tendsto (fun T : Real =>
      (Nat.primeCounting (Nat.floor (a * T)) : Real) / (a * T / Real.log (a * T)))
      atTop (nhds (1 : Real)) := by
    apply hr.congr'
    filter_upwards [] with T
    simp only [Pi.div_apply, Function.comp_apply]
  have hinv : Tendsto (fun T : Real => 1 / Real.log (a * T))
      atTop (nhds (0 : Real)) := by
    simpa only [one_div, Function.comp_def] using
      tendsto_inv_atTop_zero.comp (Real.tendsto_log_atTop.comp hgrow)
  have hconst : Tendsto (fun _ : Real => Real.log a) atTop (nhds (Real.log a)) :=
    tendsto_const_nhds
  have hone : Tendsto (fun _ : Real => (1 : Real)) atTop (nhds (1 : Real)) :=
    tendsto_const_nhds
  have hraw : Tendsto (fun T : Real => 1 - Real.log a * (1 / Real.log (a * T)))
      atTop (nhds (1 : Real)) := by
    simpa only [mul_zero, sub_zero] using hone.sub (hconst.mul hinv)
  have hlogRatio : Tendsto (fun T : Real => Real.log T / Real.log (a * T))
      atTop (nhds (1 : Real)) := by
    apply hraw.congr'
    filter_upwards [eventually_gt_atTop (0 : Real), hgrow.eventually_gt_atTop 1] with T hT haT
    have hlog : 0 < Real.log (a * T) := Real.log_pos haT
    have hlogeq := Real.log_mul ha.ne' hT.ne'
    field_simp
    linarith only [hlogeq]
  have hca : Tendsto (fun _ : Real => a) atTop (nhds a) := tendsto_const_nhds
  have hmain : Tendsto (fun T : Real =>
      ((Nat.primeCounting (Nat.floor (a * T)) : Real) / (a * T / Real.log (a * T))) *
        (a * (Real.log T / Real.log (a * T)))) atTop (nhds a) := by
    simpa only [mul_one, one_mul] using hratio.mul (hca.mul hlogRatio)
  apply hmain.congr'
  filter_upwards [eventually_gt_atTop (1 : Real), hgrow.eventually_gt_atTop 1] with T hT haT
  have hTpos : 0 < T := zero_lt_one.trans hT
  have hlogT : 0 < Real.log T := Real.log_pos hT
  have hlogAT : 0 < Real.log (a * T) := Real.log_pos haT
  field_simp

theorem eventually_primeThetaEndpointCount_sandwich (delta : Real)
    (hd : 0 < delta) (hd1 : delta < 1) :
    Filter.Eventually (fun T : Real =>
      Nat.primeCounting (Nat.floor (T / (1 + 2 * delta))) <= primeThetaEndpointCount T /\
      primeThetaEndpointCount T <= Nat.primeCounting (Nat.floor (T / (1 - delta))))
      atTop := by
  classical
  have hu := tendsto_thetaPrefix_div_endpoint.eventually
    (gt_mem_nhds (show (1 : Real) < 1 + delta by linarith))
  have hb : Filter.Eventually (fun p : Nat =>
      2 <= p /\ (1 - delta) * (p : Real) <= Chebyshev.theta ((p - 1 : Nat) : Real) /\
        Chebyshev.theta ((p - 1 : Nat) : Real) <= (1 + delta) * (p : Real)) atTop := by
    filter_upwards [eventually_thetaPrefix_and_primeCounting_bounds delta hd, hu] with p hp hupper
    have hpR : (0 : Real) < p := by exact_mod_cast (show 0 < p by omega)
    have h := mul_lt_mul_of_pos_right hupper hpR
    have heq : Chebyshev.theta ((p - 1 : Nat) : Real) / (p : Real) * p =
        Chebyshev.theta ((p - 1 : Nat) : Real) := by field_simp
    rw [heq] at h
    exact And.intro hp.1 (And.intro hp.2.1 h.le)
  choose P0 hP0 using hb.exists_forall_of_atTop
  have hdL : 0 < 1 + 2 * delta := by linarith
  have hdU : 0 < 1 - delta := by linarith
  filter_upwards [eventually_gt_atTop
    (max (1 : Real) (max (Chebyshev.theta (P0 : Real)) (P0 : Real)))] with T hT
  have hT1 : 1 < T := (le_max_left _ _).trans_lt hT
  have hTpos : 0 < T := zero_lt_one.trans hT1
  have hTtheta : Chebyshev.theta (P0 : Real) < T :=
    ((le_max_left _ _).trans (le_max_right _ _)).trans_lt hT
  have hTP0 : (P0 : Real) < T :=
    ((le_max_right _ _).trans (le_max_right _ _)).trans_lt hT
  let : Fintype (primeThetaEndpoints T) := (finite_primeThetaEndpoints T).fintype
  have hlowCover (p : Nat)
      (hp : Membership.mem (Nat.primesLE (Nat.floor (T / (1 + 2 * delta)))) p) :
      primeThetaEndpoints T p := by
    have hprime := (Nat.mem_primesLE.mp hp).2
    refine And.intro hprime ?_
    by_cases hlarge : P0 <= p
    case pos =>
      have hpFloor : (p : Real) <= (Nat.floor (T / (1 + 2 * delta)) : Real) := by
        exact_mod_cast (Nat.mem_primesLE.mp hp).1
      have hpR : (p : Real) <= T / (1 + 2 * delta) :=
        hpFloor.trans (Nat.floor_le (div_nonneg hTpos.le hdL.le))
      have hYpos : 0 < T / (1 + 2 * delta) := div_pos hTpos hdL
      have hcancel : T / (1 + 2 * delta) * (1 + 2 * delta) = T := by field_simp
      have hslack : (1 + delta) * (T / (1 + 2 * delta)) < T := by
        nlinarith [mul_pos hd hYpos]
      exact (hP0 p hlarge).2.2.trans_lt
        ((mul_le_mul_of_nonneg_left hpR (by linarith)).trans_lt hslack)
    case neg =>
      have htheta : Chebyshev.theta ((p - 1 : Nat) : Real) <= Chebyshev.theta (P0 : Real) := by
        apply Chebyshev.theta_mono
        exact_mod_cast (show p - 1 <= P0 by omega)
      exact htheta.trans_lt hTtheta
  have huppCover (p : Nat) (hp : primeThetaEndpoints T p) :
      Membership.mem (Nat.primesLE (Nat.floor (T / (1 - delta)))) p := by
    have hproduct : (1 - delta) * (p : Real) < T := by
      by_cases hlarge : P0 <= p
      case pos =>
        exact (hP0 p hlarge).2.1.trans_lt hp.2
      case neg =>
        have hpP0 : (p : Real) < P0 := by exact_mod_cast (lt_of_not_ge hlarge)
        have hc : (1 - delta) * (p : Real) <= p := by
          nlinarith [mul_nonneg hd.le (Nat.cast_nonneg p)]
        exact hc.trans_lt (hpP0.trans hTP0)
    have hpR : (p : Real) <= T / (1 - delta) := by
      have h := div_le_div_of_nonneg_right hproduct.le hdU.le
      have heq : (1 - delta) * (p : Real) / (1 - delta) = p := by field_simp
      rwa [heq] at h
    exact Nat.mem_primesLE.mpr (And.intro (Nat.le_floor hpR) hp.1)
  constructor
  . let into : {p : Nat // Membership.mem
        (Nat.primesLE (Nat.floor (T / (1 + 2 * delta)))) p} -> primeThetaEndpoints T :=
      fun p => Subtype.mk p.val (hlowCover p.val p.property)
    have hinj : Function.Injective into := by
      intro p q heq
      apply Subtype.ext
      exact congrArg (fun z : primeThetaEndpoints T => z.val) heq
    have hc := Nat.card_le_card_of_injective into hinj
    change Nat.primeCounting (Nat.floor (T / (1 + 2 * delta))) <= Nat.card (primeThetaEndpoints T)
    simpa only [Nat.card_eq_fintype_card, Fintype.card_coe,
      Nat.primesLE_card_eq_primeCounting] using hc
  . let into : primeThetaEndpoints T -> {p : Nat // Membership.mem
        (Nat.primesLE (Nat.floor (T / (1 - delta)))) p} :=
      fun p => Subtype.mk p.val (huppCover p.val p.property)
    have hinj : Function.Injective into := by
      intro p q heq
      apply Subtype.ext
      exact congrArg (fun z : {p : Nat // Membership.mem
        (Nat.primesLE (Nat.floor (T / (1 - delta)))) p} => z.val) heq
    have hc := Nat.card_le_card_of_injective into hinj
    change Nat.card (primeThetaEndpoints T) <= Nat.primeCounting (Nat.floor (T / (1 - delta)))
    simpa only [Nat.card_eq_fintype_card, Fintype.card_coe,
      Nat.primesLE_card_eq_primeCounting] using hc

theorem tendsto_primeThetaEndpointCount_div_mainTerm :
    Tendsto (fun T : Real => (primeThetaEndpointCount T : Real) / (T / Real.log T))
      atTop (nhds (1 : Real)) := by
  apply Metric.tendsto_nhds.mpr
  intro epsilon he
  let delta := min (epsilon / 8) ((1 : Real) / 4)
  have hd : 0 < delta := lt_min (by positivity) (by norm_num)
  have hdE : delta <= epsilon / 8 := min_le_left _ _
  have hdQ : delta <= (1 : Real) / 4 := min_le_right _ _
  have hd1 : delta < 1 := by linarith
  let aL := 1 / (1 + 2 * delta)
  let aU := 1 / (1 - delta)
  have hdL : 0 < 1 + 2 * delta := by linarith
  have hdU : 0 < 1 - delta := by linarith
  have haL : 0 < aL := by dsimp [aL]; positivity
  have haU : 0 < aU := by dsimp [aU]; positivity
  have haLbound : 1 - 2 * delta <= aL := by
    apply le_of_mul_le_mul_right _ hdL
    have hc : aL * (1 + 2 * delta) = 1 := by dsimp [aL]; field_simp
    rw [hc]
    nlinarith [sq_nonneg delta]
  have haUbound : aU <= 1 + 2 * delta := by
    apply le_of_mul_le_mul_right _ hdU
    have hc : aU * (1 - delta) = 1 := by dsimp [aU]; field_simp
    rw [hc]
    nlinarith [mul_nonneg hd.le (show 0 <= 1 - 2 * delta by linarith)]
  have hL := (tendsto_primeCounting_scaled_mainTerm aL haL).eventually
    (lt_mem_nhds (show aL - epsilon / 2 < aL by linarith))
  have hU := (tendsto_primeCounting_scaled_mainTerm aU haU).eventually
    (gt_mem_nhds (show aU < aU + epsilon / 2 by linarith))
  filter_upwards [eventually_primeThetaEndpointCount_sandwich delta hd hd1,
    eventually_gt_atTop (1 : Real), hL, hU] with T hcount hT hL hU
  have hmain : 0 < T / Real.log T := div_pos (zero_lt_one.trans hT) (Real.log_pos hT)
  have hlo : (Nat.primeCounting (Nat.floor (T / (1 + 2 * delta))) : Real) <=
      primeThetaEndpointCount T := by exact_mod_cast hcount.1
  have hup : (primeThetaEndpointCount T : Real) <=
      Nat.primeCounting (Nat.floor (T / (1 - delta))) := by exact_mod_cast hcount.2
  have hcutL : aL * T = T / (1 + 2 * delta) := by dsimp [aL]; ring
  have hcutU : aU * T = T / (1 - delta) := by dsimp [aU]; ring
  rw [hcutL] at hL
  rw [hcutU] at hU
  have hlower := hL.trans_le (div_le_div_of_nonneg_right hlo hmain.le)
  have hupper := (div_le_div_of_nonneg_right hup hmain.le).trans_lt hU
  rw [Real.dist_eq]
  apply abs_lt.mpr
  constructor <;> linarith

end PrimeFactorOscillations

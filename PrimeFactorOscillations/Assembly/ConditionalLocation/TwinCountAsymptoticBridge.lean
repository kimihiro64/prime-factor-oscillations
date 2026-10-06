/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import Mathlib.Topology.Algebra.Order.Field
import PrimeFactorOscillations.Assembly.ConditionalLocation.HardyLittlewoodLocation

/-!
# Twin Count Asymptotic Bridge

Maintained implementation of the conditional last-ascent location argument.
The arithmetic coverage assumptions remain explicit; no conjecture is an axiom.
-/

set_option autoImplicit false
set_option Elab.async false

namespace PrimeFactorOscillations

open Filter
noncomputable section

/-- Count lower twin members at most x; the upper member may exceed x. -/
def twinCount (x : Real) : Nat :=
  ((Finset.range (Nat.floor x + 1)).filter
    (fun p => Nat.Prime p /\ Nat.Prime (p + 2))).card

/-- The global Hardy-Littlewood-shaped counting asymptotic, leaving its
positive constant explicit. This is a hypothesis, not an asserted conjecture. -/
def TwinCountAsymptotic (C : Real) : Prop :=
  Tendsto (fun x : Real => (twinCount x : Real) * (Real.log x) ^ 2 / x)
    atTop (nhds C)

private theorem log_mul_div_log_tendsto (lam : Real) (hlam : 0 < lam) :
    Tendsto (fun x : Real => Real.log (lam * x) / Real.log x) atTop (nhds 1) := by
  have hsmall : Tendsto (fun x : Real => Real.log lam / Real.log x) atTop (nhds 0) := by
    simpa only [div_eq_mul_inv, mul_zero, Function.comp_apply] using
      (tendsto_inv_atTop_zero.comp Real.tendsto_log_atTop).const_mul (Real.log lam)
  have hsum : Tendsto (fun x : Real => Real.log lam / Real.log x + 1) atTop (nhds 1) := by
    simpa only [zero_add] using hsmall.add (tendsto_const_nhds (x := (1 : Real)))
  apply hsum.congr'
  exact (eventually_gt_atTop (1 : Real)).mono (fun x hx => by
    have hx0 : 0 < x := lt_trans (by norm_num) hx
    change Real.log lam / Real.log x + 1 = Real.log (lam * x) / Real.log x
    rw [Real.log_mul (ne_of_gt hlam) (ne_of_gt hx0)]
    field_simp [ne_of_gt (Real.log_pos hx)])

private theorem scaled_count_normalized_tendsto (F : Real -> Real) (C lam : Real)
    (hlam : 0 < lam)
    (hF : Tendsto (fun x : Real => F x * (Real.log x) ^ 2 / x) atTop (nhds C)) :
    Tendsto (fun x : Real => F (lam * x) * (Real.log x) ^ 2 / x)
      atTop (nhds (C * lam)) := by
  have hscale : Tendsto (fun x : Real => lam * x) atTop atTop :=
    (tendsto_const_mul_atTop_of_pos hlam).mpr tendsto_id
  have hlog := log_mul_div_log_tendsto lam hlam
  have hraw : Tendsto (fun x : Real =>
      ((F (lam * x) * (Real.log (lam * x)) ^ 2 / (lam * x)) * lam) /
        (Real.log (lam * x) / Real.log x) ^ 2) atTop (nhds (C * lam)) := by
    have ht := ((hF.comp hscale).mul_const lam).div (hlog.pow 2) (by norm_num)
    convert ht using 1
    next => funext x; rfl
    next => norm_num
  apply hraw.congr'
  exact (eventually_gt_atTop (max (1 : Real) (1 / lam))).mono (fun x hx => by
    have hx1 : 1 < x := (le_max_left _ _).trans_lt hx
    have hx0 : 0 < x := lt_trans (by norm_num) hx1
    have hlamx : 1 < lam * x := by
      have h := mul_lt_mul_of_pos_left ((le_max_right _ _).trans_lt hx) hlam
      have hc : lam * (1 / lam) = 1 := by field_simp
      rwa [hc] at h
    change ((F (lam * x) * (Real.log (lam * x)) ^ 2 / (lam * x)) * lam) /
      (Real.log (lam * x) / Real.log x) ^ 2 =
        F (lam * x) * (Real.log x) ^ 2 / x
    field_simp [ne_of_gt hlam, ne_of_gt hx0, ne_of_gt (Real.log_pos hx1),
      ne_of_gt (Real.log_pos hlamx)]
    <;> ring)

private theorem exists_twin_of_count_lt (a b : Real) (hb : 0 <= b)
    (hcount : twinCount a < twinCount b) :
    exists p : Nat, Nat.Prime p /\ Nat.Prime (p + 2) /\ a < p /\ (p : Real) <= b := by
  classical
  by_contra hnone
  have hsubset :
      ((Finset.range (Nat.floor b + 1)).filter
        (fun p => Nat.Prime p /\ Nat.Prime (p + 2))) <=
      ((Finset.range (Nat.floor a + 1)).filter
        (fun p => Nat.Prime p /\ Nat.Prime (p + 2))) := by
    intro p hp
    have h := Finset.mem_filter.mp hp
    have hpFloor : p <= Nat.floor b := Nat.le_of_lt_succ (Finset.mem_range.mp h.1)
    have hpb : (p : Real) <= b :=
      (show (p : Real) <= Nat.floor b by exact_mod_cast hpFloor).trans (Nat.floor_le hb)
    have hpa : (p : Real) <= a := by
      by_contra hn
      exact hnone (Exists.intro p
        (And.intro h.2.1 (And.intro h.2.2 (And.intro (lt_of_not_ge hn) hpb))))
    exact Finset.mem_filter.mpr (And.intro
      (Finset.mem_range.mpr (Nat.lt_succ_of_le (Nat.le_floor hpa))) h.2)
  exact (not_lt_of_ge (Finset.card_le_card hsubset)) hcount

/-- A positive global twin-count asymptotic implies fixed proportional
coverage by subtracting counts at x and (1-eps)*x. -/
theorem multiplicativeTwinCoverage_of_twinCountAsymptotic
    (C : Real) (hC : 0 < C) (hasymptotic : TwinCountAsymptotic C) :
    MultiplicativeTwinCoverage := by
  intro eps heps heps1
  let lam := 1 - eps
  have hlam : 0 < lam := sub_pos.mpr heps1
  have hscaled := scaled_count_normalized_tendsto (fun x => (twinCount x : Real))
    C lam hlam hasymptotic
  have hdiff := hasymptotic.sub hscaled
  have hlim : 0 < C - C * lam := by
    dsimp only [lam]
    nlinarith only [mul_pos hC heps]
  have hevent : Filter.Eventually (fun x : Real =>
      0 < (twinCount x : Real) * (Real.log x) ^ 2 / x -
        (twinCount (lam * x) : Real) * (Real.log x) ^ 2 / x) atTop :=
    (tendsto_order.mp hdiff).1 0 hlim
  choose X hX using eventually_atTop.mp hevent
  refine Exists.intro (max X 2) ?_
  intro x hx
  have hx0 : 0 < x := lt_of_lt_of_le (by norm_num) ((le_max_right _ _).trans hx)
  have hpositive := hX x ((le_max_left _ _).trans hx)
  have hcount : twinCount (lam * x) < twinCount x := by
    by_contra hn
    have hle : (twinCount x : Real) <= twinCount (lam * x) := by
      exact_mod_cast (Nat.le_of_not_gt hn)
    have hmul := mul_le_mul_of_nonneg_right hle (sq_nonneg (Real.log x))
    have hdiv := div_le_div_of_nonneg_right hmul hx0.le
    linarith only [hpositive, hdiv]
  exact exists_twin_of_count_lt (lam * x) x hx0.le hcount

/-- The Hardy-Littlewood-shaped global twin asymptotic gives the full
relative last-ascent limits for both actual canonical density formulas. -/
theorem both_last_ascent_ratio_tendsto_one_of_twinCountAsymptotic
    (C : Real) (hC : 0 < C) (hasymptotic : TwinCountAsymptotic C) :
    Tendsto (fun k : Nat => (lastAscentPrime (ordinaryDensity k) : Real) /
        (PrimeFactorUnimodality.primeAt (ordinaryTwinCutoffIndex k) : Real))
      atTop (nhds 1) /\
    Tendsto (fun k : Nat => (lastAscentPrime (genericOddDensity k) : Real) /
        (PrimeFactorUnimodality.primeAt (genericTwinCutoffIndex k) : Real))
      atTop (nhds 1) :=
  both_last_ascent_ratio_tendsto_one
    (multiplicativeTwinCoverage_of_twinCountAsymptotic C hC hasymptotic)

end
end PrimeFactorOscillations

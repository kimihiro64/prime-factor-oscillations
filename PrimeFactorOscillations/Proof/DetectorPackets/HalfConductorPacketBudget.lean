/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/

import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import OAI.NumberTheory.DirichletL.Detector.CentralDyadicWeight
import OAI.NumberTheory.DirichletL.Hecke.ZeroSupremum

/-!
# HalfConductorPacketBudget

Maintained extraction of completed detector/packet proof components.
All original theorem hypotheses and retained proof bodies are preserved.
This module alone asserts no improved zero-free boundary.
-/

set_option autoImplicit false
set_option Elab.async false

/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/

/-!
# A half-conductor split for the complete central exponent

The balanced source density at Delta=0 suffices below row exponent 1/2,
uniformly in both amplitude parameters. All losses in the mixed dyadic
consumer remain explicit. The signed tail above this cutoff and the
principal transport below beta=7/8 are separate analytic estimates.
No improved global zero-free boundary is asserted here.

The final rational witness rules out extending only the old absolute
row-density envelope to boundary 3/4; it is not a counterexample to the
arithmetic packet or to a signed estimate.
-/

set_option maxHeartbeats 1000000

noncomputable section
namespace OAI.SevenEighths.HalfConductorPacketBudget

open ProbeCentralExponent ProbeHighRowFamily

private def coeffA (y : Real) : Real :=
  181/576 + (239/864)*y + (17/108)*y^2 + (4/27)*y^3

private def coeffB (y : Real) : Real :=
  -38869/86400 - (34691/129600)*y + (671/4050)*y^2

private def coeffC (y : Real) : Real :=
  8843/51840 + (4063/25920)*y

private theorem quadratic_nonneg (A B C t : Real)
    (hA : 0 < A) (hdisc : 0 < 4*A*C-B^2) :
    0 <= A*t^2+B*t+C := by
  by_contra hn
  have hneg : A*t^2+B*t+C < 0 := lt_of_not_ge hn
  have hp := mul_neg_of_pos_of_neg hA hneg
  nlinarith only [hp, hdisc, sq_nonneg (2*A*t+B)]

theorem balanced_half_exact (delta y : Real)
    (hd0 : 0 <= delta) (hd1 : delta <= 5/6)
    (hy0 : 0 <= y) (hy1 : y <= 1/2) :
    sourceExponent ((1+delta)/2) (1/2)
      (Endpoint.balancedRowCount delta y) (delta*(1/2-y)) <= 3/50 := by
  have hJ : 0 < Endpoint.balanceDenominator delta y := by
    have hh := Endpoint.balanceDenominator_bounds hd0 hd1 hy0 hy1
    linarith
  have hA : 0 < coeffA y := by unfold coeffA; positivity
  have hdisc : 0 < 4*coeffA y*coeffC y-(coeffB y)^2 := by
    unfold coeffA coeffB coeffC
    ring_nf
    positivity
  have hQ := quadratic_nonneg (coeffA y) (coeffB y) (coeffC y) delta hA hdisc
  have hid :
      (3/50-sourceExponent ((1+delta)/2) (1/2)
        (Endpoint.balancedRowCount delta y) (delta*(1/2-y))) *
        Endpoint.balanceDenominator delta y =
      coeffA y*delta^2+coeffB y*delta+coeffC y := by
    unfold sourceExponent Endpoint.balancedRowCount Endpoint.balancedCutoff
    field_simp [ne_of_gt hJ]
    unfold Endpoint.balanceDenominator Endpoint.denominator Endpoint.primeWeight
      coeffA coeffB coeffC
    ring
  by_contra hn
  have he : 3/50-sourceExponent ((1+delta)/2) (1/2)
      (Endpoint.balancedRowCount delta y) (delta*(1/2-y)) < 0 := by linarith
  have hh := mul_neg_of_neg_of_pos he hJ
  rw [hid] at hh
  linarith

theorem balanced_half_range (delta x v R loss : Real)
    (hd0 : 0 <= delta) (hd1 : delta <= 5/6)
    (hx0 : 0 <= x) (hx1 : x <= 1/2)
    (hv0 : 0 <= v) (hv1 : v <= 1/2) (hloss : 0 <= loss)
    (hR : R <= Endpoint.balancedRowCount delta (1/2-x)+loss) :
    sourceExponent ((1+delta)/2) v R (delta*x) <= 3/50+loss/2 := by
  let y : Real := 1/2-x
  let B : Real := Endpoint.balancedRowCount delta y
  have hy0 : 0 <= y := by dsimp [y]; linarith
  have hy1 : y <= 1/2 := by dsimp [y]; linarith
  have hJ : 0 < Endpoint.balanceDenominator delta y := by
    have hh := Endpoint.balanceDenominator_bounds hd0 hd1 hy0 hy1
    linarith
  have hP : 0 <= Endpoint.primeWeight y :=
    le_trans (by norm_num) (Endpoint.primeWeight_bounds hy0 hy1).1
  have hcut : 1 <= Endpoint.balancedCutoff delta y := by
    unfold Endpoint.balancedCutoff
    have hh := div_nonneg (mul_nonneg hd0 hP) (by positivity : 0 <= 2*Endpoint.balanceDenominator delta y)
    linarith
  have hB : 1-delta <= B := by
    dsimp [B, Endpoint.balancedRowCount]
    nlinarith [mul_nonneg (show 0 <= 5/6-delta by linarith) (show 0 <= Endpoint.balancedCutoff delta y-1 by linarith)]
  have hs : 0 <= B+(1+delta)/2-21/25 := by linarith
  have hv := mul_nonpos_of_nonpos_of_nonneg (show v-1/2 <= 0 by linarith) hs
  have hr := mul_le_mul_of_nonneg_left hR hv0
  have hl := mul_le_mul_of_nonneg_right hv1 hloss
  have hb := balanced_half_exact delta y hd0 hd1 hy0 hy1
  have hq : delta*(1/2-y)=delta*x := by dsimp [y]; ring
  rw [hq] at hb
  change sourceExponent ((1+delta)/2) (1/2) B (delta*x) <= 3/50 at hb
  change R <= B+loss at hR
  change v*R <= v*(B+loss) at hr
  unfold sourceExponent at hb
  unfold sourceExponent
  nlinarith only [hb, hr, hv, hl]

theorem mixed_half_budget (beta delta x v d R countLoss mu realError overhead saving : Real)
    (hbeta : 3/4 <= beta)
    (hd0 : 0 <= delta) (hd1 : delta <= 5/6)
    (hx0 : 0 <= x) (hx1 : x <= 1/2)
    (hv0 : 0 <= v) (hv1 : v <= 1/2)
    (hR0 : 0 <= R) (hR2 : R <= 2) (hcount : 0 <= countLoss)
    (hmu : 0 <= mu) (hd : d-v <= mu)
    (hR : R <= Endpoint.balancedRowCount delta (1/2-x)+countLoss)
    (hbudget : countLoss/2+2*mu+realError+overhead+saving <= 1/400) :
    mixedSourceExponent ((1+delta)/2) v d R (delta*x)+realError+overhead <=
      beta-11/16-saving := by
  have hc := balanced_half_range delta x v R countLoss
    hd0 hd1 hx0 hx1 hv0 hv1 hcount hR
  have hm := mul_le_mul_of_nonneg_right hd hR0
  have hm2 := mul_le_mul_of_nonneg_left hR2 hmu
  unfold mixedSourceExponent
  linarith

theorem actual_mixed_half_budget
    (N : Nat) (beta delta x v d R countLoss mu e eps heightLoss mesh overhead saving : Real)
    (hbeta : 3/4 <= beta)
    (hd0 : 0 <= delta) (hd1 : delta <= 5/6)
    (hx0 : 0 <= x) (hx1 : x <= 1/2)
    (hv0 : 0 <= v) (hv1 : v <= 1/2)
    (hR0 : 0 <= R) (hR2 : R <= 2) (hcount : 0 <= countLoss)
    (hmu : 0 <= mu) (hd : d-v <= mu) (he : 0 <= e) (heps : 0 <= eps)
    (hR : R <= Endpoint.balancedRowCount delta (1/2-x)+countLoss)
    (hbudget : countLoss/2+2*mu+26*e+(N+8)*eps+heightLoss+mesh/6+
      overhead+saving <= 1/400) :
    mixedSourceExponent ((1+delta)/2) v d R (delta*x)+
      realLoss N v e eps heightLoss mesh+overhead <= beta-11/16-saving := by
  have hl := realLoss_bound N v e eps heightLoss mesh (by linarith) he heps
  apply mixed_half_budget beta delta x v d R countLoss mu
    (realLoss N v e eps heightLoss mesh) overhead saving
    hbeta hd0 hd1 hx0 hx1 hv0 hv1 hR0 hR2 hcount hmu hd hR
  linarith

theorem floor_half_range (v q : Real) (hv : v <= 1/2) (hq : q <= 1/100) :
    sourceExponent (51/100) v 1 q <= -133/4800 := by
  unfold sourceExponent
  nlinarith

theorem source_label_le_beta (a : Real)
    (hbeta : 51/100 <= HeckeZeroSupremum.beta)
    (hwitness : 51/100 < a ->
      exists (chi : HeckeFamily.Character) (s : Complex),
        HeckeFamily.LFunction chi s = 0 /\
        Not (chi.residue = 1 /\ s = 1) /\ a <= s.re) :
    a <= HeckeZeroSupremum.beta := by
  by_cases ha : a <= 51/100
  . exact ha.trans hbeta
  . have hap : 51/100 < a := lt_of_not_ge ha
    choose chi s hzero hexc hle using hwitness hap
    have hpole : Not (s = 1) \/ Not (chi.residue = 1) := by
      by_cases ht : s = 1
      . exact Or.inr (fun hc => hexc (And.intro hc ht))
      . exact Or.inl ht
    have hz := HeckeZeroSupremum.zero_re_le_beta chi
      (show 0 < s.re by linarith) hpole hzero
    exact hle.trans hz

theorem source_label_balanced (a : Real)
    (hbeta : 51/100 <= HeckeZeroSupremum.beta)
    (hupper : HeckeZeroSupremum.beta <= 7/8)
    (hwitness : 51/100 < a ->
      exists (chi : HeckeFamily.Character) (s : Complex),
        HeckeFamily.LFunction chi s = 0 /\
        Not (chi.residue = 1 /\ s = 1) /\ a <= s.re) :
    2*a-1 <= 3/4 := by
  have hh := source_label_le_beta a hbeta hwitness
  linarith

theorem original_cutoff_gap (beta : Real) :
    sourceExponent (3/4) (13/16) (1/2) (1/4) -
      (beta-11/16) = 79/96-beta := by
  unfold sourceExponent
  ring

theorem original_cutoff_envelope_fails (beta : Real) (hb : beta < 79/96) :
    beta-11/16 < sourceExponent (3/4) (13/16) (1/2) (1/4) := by
  have hh := original_cutoff_gap beta
  linarith

end OAI.SevenEighths.HalfConductorPacketBudget


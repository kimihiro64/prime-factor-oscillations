/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import Mathlib.Topology.Instances.Real.Lemmas
import PrimeFactorOscillations.Helpers.DampedWaveRecurrence

/-!
# Continuous periodic waves satisfy the full envelope regularity hypotheses

The compact-interval argument shifts both arguments by the same period.
No global uniform-continuity assumption is added to the periodic theorem.
-/

set_option autoImplicit false
set_option Elab.async false

namespace PrimeFactorOscillations.PrimeClassDeletion

theorem periodic_real_exists_abs_bound (T : Real) (f : Real -> Real)
    (hT : 0 < T) (hp : Function.Periodic f T) (hc : Continuous f) :
    exists A : Real, forall v : Real, abs (f v) <= A := by
  choose A hA using (hp.isBounded_of_continuous hT.ne' hc).exists_norm_le
  refine Exists.intro A ?_
  intro v
  simpa only [Real.norm_eq_abs] using hA (f v) (Set.mem_range_self v)

theorem periodic_real_uniformContinuous (T : Real) (f : Real -> Real)
    (hT : 0 < T) (hp : Function.Periodic f T) (hc : Continuous f) :
    UniformContinuous f := by
  have hcompact : UniformContinuousOn f (Set.Icc (-1 : Real) (T + 1)) :=
    isCompact_Icc.uniformContinuousOn_of_continuous hc.continuousOn
  apply Metric.uniformContinuous_iff.mpr
  intro e he
  choose d hd using Metric.uniformContinuousOn_iff.mp hcompact e he
  refine Exists.intro (min d 1) (And.intro (lt_min hd.1 (by norm_num)) ?_)
  intro a b hab
  let F : Real -> Real -> Real := fun x z => f (x + z)
  have hpF : Function.Periodic F T := by
    intro x
    funext z
    dsimp [F]
    rw [show x + T + z = (x + z) + T by ring, hp (x + z)]
  choose y hy using hpF.exists_mem_Ico hT a 0
  have hya : f a = f y := by
    simpa only [F, add_zero] using congrFun hy.2 0
  have hyb : f b = f (y + (b - a)) := by
    have h := congrFun hy.2 (b - a)
    dsimp [F] at h
    rw [show a + (b - a) = b by ring] at h
    exact h
  have hy0 : 0 <= y := hy.1.1
  have hyT : y <= T := by linarith only [hy.1.2]
  have hab1 : abs (a - b) < 1 :=
    (show dist a b < 1 from hab.trans_le (min_le_right d 1))
  have habs := abs_lt.mp hab1
  have hym : Membership.mem (Set.Icc (-1 : Real) (T + 1)) y := by
    exact And.intro (by linarith only [hy0]) (by linarith only [hyT])
  have hzm : Membership.mem (Set.Icc (-1 : Real) (T + 1)) (y + (b - a)) := by
    exact And.intro (by linarith only [hy0, habs.2]) (by linarith only [hyT, habs.1])
  have hdist : dist y (y + (b - a)) = dist a b := by
    rw [Real.dist_eq, Real.dist_eq]
    congr 1
    ring
  rw [hya, hyb]
  apply hd.2 y hym (y + (b - a)) hzm
  rw [hdist]
  exact hab.trans_le (min_le_left d 1)

theorem dampedWaveEnvelope_periodic_continuous (b T : Real) (f : Real -> Real)
    (hb : 0 <= b) (hT : 0 < T) (hp : Function.Periodic f T) (hc : Continuous f) :
    And (Continuous (dampedWaveEnvelope b f)) (Function.Periodic (dampedWaveEnvelope b f) T) := by
  choose A hA using periodic_real_exists_abs_bound T f hT hp hc
  exact And.intro
    (dampedWaveEnvelope_uniformContinuous b A f hb hA
      (periodic_real_uniformContinuous T f hT hp hc)).continuous
    (dampedWaveEnvelope_periodic b T f hp)

end PrimeFactorOscillations.PrimeClassDeletion

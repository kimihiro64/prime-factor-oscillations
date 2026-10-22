/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.DampedWaveEnvelope

/-!
# Periodic and uniformly almost-periodic positivity of the deletion envelope

Almost periods are quantified uniformly over the whole real line. The
recurrence length is independent of the observation point.
-/

set_option autoImplicit false
set_option Elab.async false

namespace PrimeFactorOscillations.PrimeClassDeletion

def IsUniformAlmostPeriodicWave (f : Real -> Real) : Prop :=
  forall e : Real, 0 < e -> exists L : Real, And (0 < L)
    (forall a : Real, exists t : Real, And (a <= t) (And (t <= a + L)
      (forall v : Real, abs (f (v + t) - f v) <= e)))

theorem dampedWaveEnvelope_almost_period (b A e t : Real) (f : Real -> Real)
    (hb : 0 <= b) (hf : forall v : Real, abs (f v) <= A) (he : 0 <= e)
    (ht : forall v : Real, abs (f (v + t) - f v) <= e) (v : Real) :
    abs (dampedWaveEnvelope b f (v + t) - dampedWaveEnvelope b f v) <= e := by
  apply dampedWaveEnvelope_abs_sub_le b A A e f f hb hf hf he
  intro u _
  rw [show v + t - u = (v - u) + t by ring]
  exact ht (v - u)

theorem dampedWaveEnvelope_uniformAlmostPeriodic (b A : Real) (f : Real -> Real)
    (hb : 0 <= b) (hf : forall v : Real, abs (f v) <= A)
    (hp : IsUniformAlmostPeriodicWave f) :
    IsUniformAlmostPeriodicWave (dampedWaveEnvelope b f) := by
  intro e he
  choose L hL using hp e he
  refine Exists.intro L (And.intro hL.1 ?_)
  intro a
  choose t ht using hL.2 a
  exact Exists.intro t (And.intro ht.1 (And.intro ht.2.1
    (dampedWaveEnvelope_almost_period b A e t f hb hf he.le ht.2.2)))

theorem dampedWaveEnvelope_periodic_lower (b A T v0 : Real) (f : Real -> Real)
    (hb : 0 <= b) (hf : forall v : Real, abs (f v) <= A)
    (hT : 0 < T) (hp : Function.Periodic f T) (hpos : 0 < f v0) (v : Real) :
    f v0 * Real.exp (-(b * T)) <= dampedWaveEnvelope b f v := by
  choose y hy using hp.exists_mem_Ioc hT v0 (v - T)
  have hyv : y <= v := by linarith only [hy.1.2]
  have hyl : v - y <= T := by linarith only [hy.1.1]
  have hu : 0 <= v - y := sub_nonneg.mpr hyv
  have hrow := dampedWave_term_le_envelope b A f hb hf v (v - y) hu
  rw [show v - (v - y) = y by ring, <- hy.2] at hrow
  have hweight : Real.exp (-(b * T)) <= Real.exp (-(b * (v - y))) := by
    apply Real.exp_le_exp.mpr
    exact neg_le_neg (mul_le_mul_of_nonneg_left hyl hb)
  have hproduct := mul_le_mul_of_nonneg_right hweight hpos.le
  calc
    f v0 * Real.exp (-(b * T)) = Real.exp (-(b * T)) * f v0 := mul_comm _ _
    _ <= Real.exp (-(b * (v - y))) * f v0 := hproduct
    _ <= dampedWaveEnvelope b f v := hrow

theorem dampedWaveEnvelope_uniformAlmostPeriodic_lower (b A v0 : Real)
    (f : Real -> Real) (hb : 0 <= b) (hf : forall v : Real, abs (f v) <= A)
    (hp : IsUniformAlmostPeriodicWave f) (hpos : 0 < f v0) :
    exists c : Real, And (0 < c) (forall v : Real, c <= dampedWaveEnvelope b f v) := by
  let a := f v0 / 2
  have ha : 0 < a := by dsimp [a]; linarith only [hpos]
  choose L hL using hp a ha
  refine Exists.intro (a * Real.exp (-(b * L)))
    (And.intro (mul_pos ha (Real.exp_pos _)) ?_)
  intro v
  choose t ht using hL.2 (v - v0 - L)
  let u := v - v0 - t
  have hu : 0 <= u := by dsimp [u]; linarith only [ht.2.1]
  have huL : u <= L := by dsimp [u]; linarith only [ht.1]
  have hfpos : a <= f (v - u) := by
    have h := (abs_le.mp (ht.2.2 v0)).1
    rw [show v - u = v0 + t by dsimp [u]; ring]
    dsimp [a] at h
    dsimp [a]
    linarith only [h]
  have hweight : Real.exp (-(b * L)) <= Real.exp (-(b * u)) := by
    apply Real.exp_le_exp.mpr
    exact neg_le_neg (mul_le_mul_of_nonneg_left huL hb)
  calc
    a * Real.exp (-(b * L)) = Real.exp (-(b * L)) * a := mul_comm _ _
    _ <= Real.exp (-(b * u)) * a := mul_le_mul_of_nonneg_right hweight ha.le
    _ <= Real.exp (-(b * u)) * f (v - u) :=
      mul_le_mul_of_nonneg_left hfpos (Real.exp_pos _).le
    _ <= dampedWaveEnvelope b f v := dampedWave_term_le_envelope b A f hb hf v u hu

end PrimeFactorOscillations.PrimeClassDeletion

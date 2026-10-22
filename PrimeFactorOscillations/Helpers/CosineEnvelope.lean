/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.DampedWaveEnvelope
import PrimeFactorOscillations.Helpers.DiscountedCosinePhase

/-!
# The complete explicit one-harmonic deletion envelope

The modular phase is a literal floor expression. The full nonnegative
lookback domain is retained; both candidate maximizers are exhibited.
-/

set_option autoImplicit false
set_option Elab.async false

namespace PrimeFactorOscillations.PrimeClassDeletion

theorem cosineWave_abs_le (A frequency phase : Real) (hA : 0 <= A) (v : Real) :
    abs (A * Real.cos (frequency * v + phase)) <= A := by
  rw [abs_mul, abs_of_nonneg hA]
  exact (mul_le_mul_of_nonneg_left (Real.abs_cos_le_one _) hA).trans_eq (mul_one _)

theorem dampedWaveEnvelope_cosine (b A frequency phase v : Real)
    (hb : 0 <= b) (hA : 0 <= A) (hfrequency : 0 < frequency) :
    let a := Real.arctan (b / frequency)
    let w := frequency * v + phase
    let d := cosinePhaseRemainder w a
    dampedWaveEnvelope b (fun t : Real => A * Real.cos (frequency * t + phase)) v =
      A * max (Real.cos w) (Real.cos a * Real.exp (-((b / frequency) * d))) := by
  let k := b / frequency
  let a := Real.arctan k
  let w := frequency * v + phase
  let d := cosinePhaseRemainder w a
  let f : Real -> Real := fun t => A * Real.cos (frequency * t + phase)
  change dampedWaveEnvelope b f v = A *
    max (Real.cos w) (Real.cos a * Real.exp (-(k * d)))
  have hf : forall t : Real, abs (f t) <= A := cosineWave_abs_le A frequency phase hA
  have hk : 0 <= k := div_nonneg hb hfrequency.le
  have hcos : 0 < Real.cos a := Real.cos_arctan_pos k
  have hsin : Real.sin a = k * Real.cos a := by
    have ht := Real.tan_arctan k
    rw [Real.tan_eq_sin_div_cos] at ht
    have hm := congrArg (fun y : Real => y * Real.cos a) ht
    have hc : (Real.sin a / Real.cos a) * Real.cos a = Real.sin a := by
      field_simp
    rw [hc] at hm
    exact hm
  have hd := cosinePhaseRemainder_bounds w a
  have hkw : k * frequency = b := by
    dsimp [k]
    field_simp [ne_of_gt hfrequency]
  have hc0 : Real.cos (a + d) = Real.cos w := by
    have h := cosinePhaseRemainder_cos w a 0
    simpa only [sub_zero] using h.symm
  have hupp (u : Real) (hu : 0 <= u) :
      Real.exp (-(b * u)) * f (v - u) <=
        A * max (Real.cos w) (Real.cos a * Real.exp (-(k * d))) := by
    have h := discountedCosine_phase_upper k a d (frequency * u) hk hcos.le hsin
      hd.1 hd.2.le (mul_nonneg hfrequency.le hu)
    have hphase : Real.cos (a + d - frequency * u) = Real.cos (w - frequency * u) :=
      (cosinePhaseRemainder_cos w a (frequency * u)).symm
    rw [hphase, hc0] at h
    have he : b * u = k * (frequency * u) := by rw [<- hkw]; ring
    have harg : frequency * (v - u) + phase = w - frequency * u := by dsimp [w]; ring
    dsimp [f]
    rw [he, harg]
    calc
      _ = A * (Real.exp (-(k * (frequency * u))) * Real.cos (w - frequency * u)) := by ring
      _ <= _ := mul_le_mul_of_nonneg_left h hA
  have hupper : dampedWaveEnvelope b f v <=
      A * max (Real.cos w) (Real.cos a * Real.exp (-(k * d))) := by
    apply csSup_le (dampedWaveValues_nonempty b f v)
    intro y hy
    cases Set.mem_insert_iff.mp hy with
    | inl hz =>
        rw [hz]
        apply mul_nonneg hA
        exact (mul_nonneg hcos.le (Real.exp_pos _).le).trans (le_max_right _ _)
    | inr hi =>
        choose u hu using hi
        rw [<- hu.2]
        exact hupp u hu.1
  have hfirst : A * Real.cos w <= dampedWaveEnvelope b f v := by
    have h := dampedWave_term_le_envelope b A f hb hf v 0 (le_refl 0)
    simpa only [mul_zero, neg_zero, Real.exp_zero, one_mul, sub_zero] using h
  have hsecond : A * (Real.cos a * Real.exp (-(k * d))) <=
      dampedWaveEnvelope b f v := by
    have h := dampedWave_term_le_envelope b A f hb hf v (d / frequency)
      (div_nonneg hd.1 hfrequency.le)
    have harg : frequency * (v - d / frequency) + phase = w - d := by
      dsimp [w]
      field_simp [ne_of_gt hfrequency]
      ring
    have he : b * (d / frequency) = k * d := by dsimp [k]; ring
    have hphase : Real.cos (w - d) = Real.cos a := by
      have hp := cosinePhaseRemainder_cos w a d
      change Real.cos (w - d) = Real.cos (a + d - d) at hp
      simpa only [add_sub_cancel_right] using hp
    change Real.exp (-(b * (d / frequency))) *
      (A * Real.cos (frequency * (v - d / frequency) + phase)) <= _ at h
    rw [harg, hphase, he] at h
    calc
      _ = Real.exp (-(k * d)) * (A * Real.cos a) := by ring
      _ <= _ := h
  have hlower : A * max (Real.cos w) (Real.cos a * Real.exp (-(k * d))) <=
      dampedWaveEnvelope b f v := by
    cases le_total (Real.cos w) (Real.cos a * Real.exp (-(k * d))) with
    | inl hc => rw [max_eq_right hc]; exact hsecond
    | inr hc => rw [max_eq_left hc]; exact hfirst
  exact le_antisymm hupper hlower

theorem dampedWaveEnvelope_cosine_bounds (b A frequency phase v : Real)
    (hb : 0 <= b) (hA : 0 <= A) (hfrequency : 0 < frequency) :
    And (A * Real.cos (Real.arctan (b / frequency)) *
      Real.exp (-(2 * Real.pi * (b / frequency))) <=
        dampedWaveEnvelope b (fun t : Real => A * Real.cos (frequency * t + phase)) v)
      (dampedWaveEnvelope b (fun t : Real => A * Real.cos (frequency * t + phase)) v <= A) := by
  refine And.intro ?_ (dampedWaveEnvelope_le b A _ hb
    (cosineWave_abs_le A frequency phase hA) v)
  rw [dampedWaveEnvelope_cosine b A frequency phase v hb hA hfrequency]
  let k := b / frequency
  let a := Real.arctan k
  let w := frequency * v + phase
  let d := cosinePhaseRemainder w a
  change A * Real.cos a * Real.exp (-(2 * Real.pi * k)) <=
    A * max (Real.cos w) (Real.cos a * Real.exp (-(k * d)))
  have hk : 0 <= k := div_nonneg hb hfrequency.le
  have hd := cosinePhaseRemainder_bounds w a
  have he : Real.exp (-(2 * Real.pi * k)) <= Real.exp (-(k * d)) := by
    apply Real.exp_le_exp.mpr
    nlinarith only [hd.2, hk]
  have hc : 0 <= A * Real.cos a := mul_nonneg hA (Real.cos_arctan_pos k).le
  calc
    _ <= A * Real.cos a * Real.exp (-(k * d)) := mul_le_mul_of_nonneg_left he hc
    _ = A * (Real.cos a * Real.exp (-(k * d))) := by ring
    _ <= _ := mul_le_mul_of_nonneg_left (le_max_right _ _) hA

end PrimeFactorOscillations.PrimeClassDeletion

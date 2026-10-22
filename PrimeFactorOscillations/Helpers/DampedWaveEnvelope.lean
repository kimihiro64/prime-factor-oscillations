/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import Mathlib.Algebra.Field.Periodic
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# The discounted positive envelope used by the prime-record wave theorem

The value set explicitly contains zero. Positivity of the original wave
is unnecessary for boundedness or uniform continuity.
-/

set_option autoImplicit false
set_option Elab.async false

namespace PrimeFactorOscillations.PrimeClassDeletion

noncomputable def dampedWaveValues (b : Real) (f : Real -> Real) (v : Real) : Set Real :=
  Set.insert 0 ((fun u : Real => Real.exp (-(b * u)) * f (v - u)) '' Set.Ici 0)

noncomputable def dampedWaveEnvelope (b : Real) (f : Real -> Real) (v : Real) : Real :=
  sSup (dampedWaveValues b f v)

theorem dampedWaveValues_nonempty (b : Real) (f : Real -> Real) (v : Real) :
    (dampedWaveValues b f v).Nonempty :=
  Exists.intro 0 (Set.mem_insert_iff.mpr (Or.inl rfl))

theorem dampedWave_weight_bounds (b u : Real) (hb : 0 <= b) (hu : 0 <= u) :
    And (0 <= Real.exp (-(b * u))) (Real.exp (-(b * u)) <= 1) :=
  And.intro (Real.exp_pos _).le
    (Real.exp_le_one_iff.mpr (neg_nonpos.mpr (mul_nonneg hb hu)))

theorem dampedWaveValues_upperBound (b A : Real) (f : Real -> Real)
    (hb : 0 <= b) (hf : forall t : Real, abs (f t) <= A) (v : Real) :
    forall y : Real, Membership.mem (dampedWaveValues b f v) y -> y <= A := by
  have hA : 0 <= A := (abs_nonneg (f 0)).trans (hf 0)
  intro y hy
  cases Set.mem_insert_iff.mp hy with
  | inl hz => simpa only [hz] using hA
  | inr hi =>
      choose u hu using hi
      rw [<- hu.2]
      have hw := dampedWave_weight_bounds b u hb hu.1
      calc
        Real.exp (-(b * u)) * f (v - u) <=
            Real.exp (-(b * u)) * abs (f (v - u)) :=
          mul_le_mul_of_nonneg_left (le_abs_self _) hw.1
        _ <= Real.exp (-(b * u)) * A :=
          mul_le_mul_of_nonneg_left (hf _) hw.1
        _ <= 1 * A := mul_le_mul_of_nonneg_right hw.2 hA
        _ = A := one_mul A

theorem dampedWaveValues_bddAbove (b A : Real) (f : Real -> Real)
    (hb : 0 <= b) (hf : forall t : Real, abs (f t) <= A) (v : Real) :
    BddAbove (dampedWaveValues b f v) :=
  Exists.intro A (dampedWaveValues_upperBound b A f hb hf v)

theorem dampedWaveEnvelope_nonneg (b A : Real) (f : Real -> Real)
    (hb : 0 <= b) (hf : forall t : Real, abs (f t) <= A) (v : Real) :
    0 <= dampedWaveEnvelope b f v :=
  le_csSup (dampedWaveValues_bddAbove b A f hb hf v)
    (Set.mem_insert_iff.mpr (Or.inl rfl))

theorem dampedWaveEnvelope_le (b A : Real) (f : Real -> Real)
    (hb : 0 <= b) (hf : forall t : Real, abs (f t) <= A) (v : Real) :
    dampedWaveEnvelope b f v <= A :=
  csSup_le (dampedWaveValues_nonempty b f v)
    (dampedWaveValues_upperBound b A f hb hf v)

theorem dampedWave_term_le_envelope (b A : Real) (f : Real -> Real)
    (hb : 0 <= b) (hf : forall t : Real, abs (f t) <= A)
    (v u : Real) (hu : 0 <= u) :
    Real.exp (-(b * u)) * f (v - u) <= dampedWaveEnvelope b f v := by
  apply le_csSup (dampedWaveValues_bddAbove b A f hb hf v)
  exact Set.mem_insert_iff.mpr (Or.inr (Exists.intro u (And.intro hu rfl)))

theorem dampedWaveEnvelope_le_add (b B e : Real) (f g : Real -> Real)
    (hb : 0 <= b) (hg : forall t : Real, abs (g t) <= B) (he : 0 <= e)
    (v w : Real) (hfg : forall u : Real, 0 <= u -> f (v - u) <= g (w - u) + e) :
    dampedWaveEnvelope b f v <= dampedWaveEnvelope b g w + e := by
  apply csSup_le (dampedWaveValues_nonempty b f v)
  intro y hy
  cases Set.mem_insert_iff.mp hy with
  | inl hz =>
      rw [hz]
      exact add_nonneg (dampedWaveEnvelope_nonneg b B g hb hg w) he
  | inr hi =>
      choose u hu using hi
      rw [<- hu.2]
      have hw := dampedWave_weight_bounds b u hb hu.1
      have hrow := mul_le_mul_of_nonneg_left (hfg u hu.1) hw.1
      have htop := dampedWave_term_le_envelope b B g hb hg w u hu.1
      have hew := mul_le_mul_of_nonneg_right hw.2 he
      nlinarith only [hrow, htop, hew]

theorem dampedWaveEnvelope_abs_sub_le (b A B e : Real) (f g : Real -> Real)
    (hb : 0 <= b) (hf : forall t : Real, abs (f t) <= A)
    (hg : forall t : Real, abs (g t) <= B) (he : 0 <= e)
    (v w : Real) (hfg : forall u : Real, 0 <= u -> abs (f (v - u) - g (w - u)) <= e) :
    abs (dampedWaveEnvelope b f v - dampedWaveEnvelope b g w) <= e := by
  have hleft := dampedWaveEnvelope_le_add b B e f g hb hg he v w (by
    intro u hu
    have h := (abs_le.mp (hfg u hu)).2
    linarith only [h])
  have hright := dampedWaveEnvelope_le_add b A e g f hb hf he w v (by
    intro u hu
    have h := (abs_le.mp (hfg u hu)).1
    linarith only [h])
  exact abs_le.mpr (And.intro (by linarith only [hright]) (by linarith only [hleft]))

theorem dampedWaveEnvelope_periodic (b T : Real) (f : Real -> Real)
    (hf : Function.Periodic f T) : Function.Periodic (dampedWaveEnvelope b f) T := by
  intro v
  have heq : (fun u : Real => Real.exp (-(b * u)) * f (v + T - u)) =
      (fun u : Real => Real.exp (-(b * u)) * f (v - u)) := by
    funext u
    rw [show v + T - u = (v - u) + T by ring, hf (v - u)]
  unfold dampedWaveEnvelope dampedWaveValues
  rw [heq]

theorem dampedWaveEnvelope_uniformContinuous (b A : Real) (f : Real -> Real)
    (hb : 0 <= b) (hf : forall t : Real, abs (f t) <= A)
    (hc : UniformContinuous f) : UniformContinuous (dampedWaveEnvelope b f) := by
  apply Metric.uniformContinuous_iff.mpr
  intro e he
  choose d hd using Metric.uniformContinuous_iff.mp hc (e / 2) (by linarith only [he])
  refine Exists.intro d (And.intro hd.1 ?_)
  intro v w hvw
  have hfg : forall u : Real, 0 <= u -> abs (f (v - u) - f (w - u)) <= e / 2 := by
    intro u _
    have hdist : dist (v - u) (w - u) = dist v w := by
      rw [Real.dist_eq, Real.dist_eq]
      congr 1
      ring
    have h := hd.2 (by rw [hdist]; exact hvw)
    exact (show abs (f (v - u) - f (w - u)) < e / 2 from h).le
  have h := dampedWaveEnvelope_abs_sub_le b A A (e / 2) f f hb hf hf
    (by linarith only [he]) v w hfg
  rw [Real.dist_eq]
  exact lt_of_le_of_lt h (by linarith only [he])

end PrimeFactorOscillations.PrimeClassDeletion

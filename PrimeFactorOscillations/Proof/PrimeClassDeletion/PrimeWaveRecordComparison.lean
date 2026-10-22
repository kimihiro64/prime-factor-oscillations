/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.DampedWaveEnvelope
import PrimeFactorOscillations.Proof.PrimeClassDeletion.PrimeRecordAllCutoffs

/-!
# Finite wave comparisons for the actual fixed greedy prime regulator

The error hypothesis ranges over every real cutoff between two and x.
The envelope comparison retains the bounded initial tail and logarithmic
overshoot; neither is substituted for a deleted-count asymptotic.
-/

set_option autoImplicit false
set_option Elab.async false

namespace PrimeFactorOscillations.PrimeClassDeletion

open PrimeFactorUnimodality
open PrimeFactorOscillations.PrimeClassSampling

theorem greedyPrimeRegulatorReal_nonneg (x : Real) :
    0 <= greedyPrimeRegulatorReal x :=
  clockRecord_nonneg primeClockError (primeCutoffLength (Nat.floor x))

theorem greedyPrimeRegulatorReal_mono (t x : Real) (ht : 0 <= t) (htx : t <= x) :
    greedyPrimeRegulatorReal t <= greedyPrimeRegulatorReal x := by
  have hx := ht.trans htx
  have hself := (greedyPrimeRegulatorReal_le_iff x (greedyPrimeRegulatorReal x) hx).mp
    (le_refl _)
  apply (greedyPrimeRegulatorReal_le_iff t (greedyPrimeRegulatorReal x) ht).mpr
  exact And.intro hself.1 (fun p hp hpt => hself.2 p hp (hpt.trans htx))

theorem primeThetaErrorReal_le_record_log (t : Real) (ht : 2 <= t) :
    primeClassThetaReal Set.univ t - t <= greedyPrimeRegulatorReal t + Real.log t := by
  have htotal := greedyPrimeClass_theta_partition (Nat.floor t)
  change primeClassThetaReal greedyPrimeClass t +
    primeClassThetaReal greedyDeletedPrimeClass t = primeClassThetaReal Set.univ t at htotal
  have hcap := greedyPrimeClass_thetaReal_le t (by linarith only [ht])
  have hmass := (greedyDeletedPrimeClass_real_record_bounds t ht).2
  linarith only [htotal, hcap, hmass]

theorem dampedWave_scale_identity (b x t : Real) (hx : 0 < x) (ht : 0 < t) :
    x ^ b * Real.exp (-(b * (Real.log x - Real.log t))) = t ^ b := by
  rw [Real.rpow_def_of_pos hx, Real.rpow_def_of_pos ht, <- Real.exp_add]
  congr 1
  ring

theorem dampedWave_model_le (b A : Real) (f : Real -> Real)
    (hb : 0 <= b) (hf : forall v : Real, abs (f v) <= A)
    (x t : Real) (hx : 0 < x) (ht : 0 < t) (htx : t <= x) :
    t ^ b * f (Real.log t) <= x ^ b * dampedWaveEnvelope b f (Real.log x) := by
  have hu : 0 <= Real.log x - Real.log t :=
    sub_nonneg.mpr (Real.log_le_log ht htx)
  have hrow := dampedWave_term_le_envelope b A f hb hf (Real.log x)
    (Real.log x - Real.log t) hu
  have heq : Real.log x - (Real.log x - Real.log t) = Real.log t := by ring
  calc
    t ^ b * f (Real.log t) = x ^ b *
        (Real.exp (-(b * (Real.log x - Real.log t))) *
          f (Real.log x - (Real.log x - Real.log t))) := by
      rw [heq, <- mul_assoc, dampedWave_scale_identity b x t hx ht]
    _ <= x ^ b * dampedWaveEnvelope b f (Real.log x) :=
      mul_le_mul_of_nonneg_left hrow (Real.rpow_pos_of_pos hx b).le

theorem primeWaveRecord_model_upper (b A D x : Real) (f : Real -> Real)
    (hb : 0 <= b) (hf : forall v : Real, abs (f v) <= A)
    (hD : 0 <= D) (hx : 2 <= x)
    (herr : forall t : Real, 2 <= t -> t <= x ->
      abs ((primeClassThetaReal Set.univ t - t) - t ^ b * f (Real.log t)) <= D) :
    greedyPrimeRegulatorReal x <= x ^ b * dampedWaveEnvelope b f (Real.log x) + D := by
  have hx0 : 0 < x := by linarith only [hx]
  apply (greedyPrimeRegulatorReal_le_iff x _ hx0.le).mpr
  refine And.intro
    (add_nonneg (mul_nonneg (Real.rpow_pos_of_pos hx0 b).le
      (dampedWaveEnvelope_nonneg b A f hb hf (Real.log x))) hD) ?_
  intro p hp hpx
  have hp2 : (2 : Real) <= (p : Real) := by exact_mod_cast hp.two_le
  have hp0 : (0 : Real) < (p : Real) := by linarith only [hp2]
  have he := (abs_le.mp (herr (p : Real) hp2 hpx)).2
  have hm := dampedWave_model_le b A f hb hf x (p : Real) hx0 hp0 hpx
  linarith only [he, hm]

theorem primeWaveRecord_model_lower (b A D x : Real) (f : Real -> Real)
    (hb : 0 <= b) (hf : forall v : Real, abs (f v) <= A)
    (hD : 0 <= D) (hx : 2 <= x)
    (herr : forall t : Real, 2 <= t -> t <= x ->
      abs ((primeClassThetaReal Set.univ t - t) - t ^ b * f (Real.log t)) <= D) :
    x ^ b * dampedWaveEnvelope b f (Real.log x) <=
      greedyPrimeRegulatorReal x + D + Real.log x + A * (2 : Real) ^ b := by
  have hx0 : 0 < x := by linarith only [hx]
  have hxb : 0 < x ^ b := Real.rpow_pos_of_pos hx0 b
  have hA : 0 <= A := (abs_nonneg (f 0)).trans (hf 0)
  have hR := greedyPrimeRegulatorReal_nonneg x
  have hlog : 0 <= Real.log x := Real.log_nonneg (by linarith only [hx])
  have htail : 0 <= A * (2 : Real) ^ b :=
    mul_nonneg hA (Real.rpow_pos_of_pos (by norm_num) b).le
  have hsup : dampedWaveEnvelope b f (Real.log x) <=
      (greedyPrimeRegulatorReal x + D + Real.log x + A * (2 : Real) ^ b) / x ^ b := by
    apply csSup_le (dampedWaveValues_nonempty b f (Real.log x))
    intro y hy
    have hrow : y * x ^ b <=
        greedyPrimeRegulatorReal x + D + Real.log x + A * (2 : Real) ^ b := by
      cases Set.mem_insert_iff.mp hy with
      | inl hz => rw [hz, zero_mul]; linarith only [hR, hD, hlog, htail]
      | inr hi =>
          choose u hu using hi
          rw [<- hu.2]
          let t := x * Real.exp (-u)
          have ht0 : 0 < t := mul_pos hx0 (Real.exp_pos _)
          have htx : t <= x := by
            have hw : Real.exp (-u) <= 1 :=
              Real.exp_le_one_iff.mpr (neg_nonpos.mpr hu.1)
            exact (mul_le_mul_of_nonneg_left hw hx0.le).trans_eq (mul_one x)
          have hlt : Real.log t = Real.log x - u := by
            rw [show t = x * Real.exp (-u) from rfl,
              Real.log_mul hx0.ne' (Real.exp_pos _).ne', Real.log_exp]
            ring
          have hscale : x ^ b * Real.exp (-(b * u)) = t ^ b := by
            have h := dampedWave_scale_identity b x t hx0 ht0
            rw [hlt, show Real.log x - (Real.log x - u) = u by ring] at h
            exact h
          have hmodel : (Real.exp (-(b * u)) * f (Real.log x - u)) * x ^ b =
              t ^ b * f (Real.log t) := by
            rw [hlt]
            calc
              _ = (x ^ b * Real.exp (-(b * u))) * f (Real.log x - u) := by ring
              _ = _ := by rw [hscale]
          rw [hmodel]
          by_cases ht : 2 <= t
          case pos =>
            have he := (abs_le.mp (herr t ht htx)).1
            have hE := primeThetaErrorReal_le_record_log t ht
            have hmono := greedyPrimeRegulatorReal_mono t x ht0.le htx
            have hlogs := Real.log_le_log ht0 htx
            linarith only [he, hE, hmono, hlogs, htail]
          case neg =>
            have ht2 : t <= 2 := le_of_lt (lt_of_not_ge ht)
            have hpower := Real.rpow_le_rpow ht0.le ht2 hb
            have hfa : f (Real.log t) <= A := (le_abs_self _).trans (hf _)
            have hm := mul_le_mul_of_nonneg_left hfa (Real.rpow_pos_of_pos ht0 b).le
            have hp := mul_le_mul_of_nonneg_right hpower hA
            linarith only [hm, hp, hR, hD, hlog]
    calc
      y = (y * x ^ b) / x ^ b := by field_simp
      _ <= (greedyPrimeRegulatorReal x + D + Real.log x + A * (2 : Real) ^ b) / x ^ b :=
        div_le_div_of_nonneg_right hrow hxb.le
  have h := mul_le_mul_of_nonneg_right hsup hxb.le
  have hcancel :
      ((greedyPrimeRegulatorReal x + D + Real.log x + A * (2 : Real) ^ b) / x ^ b) *
        x ^ b = greedyPrimeRegulatorReal x + D + Real.log x + A * (2 : Real) ^ b := by
    field_simp
  rw [hcancel] at h
  simpa only [mul_comm] using h

theorem primeWaveRecord_model_error (b A D x : Real) (f : Real -> Real)
    (hb : 0 <= b) (hf : forall v : Real, abs (f v) <= A)
    (hD : 0 <= D) (hx : 2 <= x)
    (herr : forall t : Real, 2 <= t -> t <= x ->
      abs ((primeClassThetaReal Set.univ t - t) - t ^ b * f (Real.log t)) <= D) :
    abs (greedyPrimeRegulatorReal x - x ^ b * dampedWaveEnvelope b f (Real.log x)) <=
      D + Real.log x + A * (2 : Real) ^ b := by
  have hlow := primeWaveRecord_model_lower b A D x f hb hf hD hx herr
  have hupp := primeWaveRecord_model_upper b A D x f hb hf hD hx herr
  have hlog : 0 <= Real.log x := Real.log_nonneg (by linarith only [hx])
  have hA : 0 <= A := (abs_nonneg (f 0)).trans (hf 0)
  have htail : 0 <= A * (2 : Real) ^ b :=
    mul_nonneg hA (Real.rpow_pos_of_pos (by norm_num) b).le
  exact abs_le.mpr (And.intro (by linarith only [hlow])
    (by linarith only [hupp, hlog, htail]))

end PrimeFactorOscillations.PrimeClassDeletion

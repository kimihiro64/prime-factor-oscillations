/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.DampedWaveEnvelope

/-! # The literal positive-supremum formula and sup norm of a bounded wave -/

set_option autoImplicit false
set_option Elab.async false

namespace PrimeFactorOscillations.PrimeClassDeletion

noncomputable def waveSupNorm (f : Real -> Real) : Real :=
  sSup (Set.range (fun v : Real => abs (f v)))

theorem waveSupNorm_bounds (A : Real) (f : Real -> Real)
    (hf : forall v : Real, abs (f v) <= A) :
    And (0 <= waveSupNorm f)
      (And (forall v : Real, abs (f v) <= waveSupNorm f) (waveSupNorm f <= A)) := by
  have hne : (Set.range (fun v : Real => abs (f v))).Nonempty :=
    Exists.intro (abs (f 0)) (Set.mem_range_self 0)
  have hu : forall y : Real, Membership.mem (Set.range (fun v : Real => abs (f v))) y -> y <= A := by
    intro y hy
    choose v hv using hy
    rw [<- hv]
    exact hf v
  have hb : BddAbove (Set.range (fun v : Real => abs (f v))) := Exists.intro A hu
  have hbound : forall v : Real, abs (f v) <= waveSupNorm f :=
    fun v => le_csSup hb (Set.mem_range_self v)
  exact And.intro ((abs_nonneg (f 0)).trans (hbound 0))
    (And.intro hbound (csSup_le hne hu))

theorem dampedWaveEnvelope_le_supNorm (b A : Real) (f : Real -> Real)
    (hb : 0 <= b) (hf : forall v : Real, abs (f v) <= A) (v : Real) :
    dampedWaveEnvelope b f v <= waveSupNorm f :=
  dampedWaveEnvelope_le b (waveSupNorm f) f hb (waveSupNorm_bounds A f hf).2.1 v

theorem dampedWaveEnvelope_eq_positive_sup (b A : Real) (f : Real -> Real)
    (hb : 0 <= b) (hf : forall v : Real, abs (f v) <= A) (v : Real) :
    dampedWaveEnvelope b f v =
      max 0 (sSup ((fun u : Real => Real.exp (-(b * u)) * f (v - u)) '' Set.Ici 0)) := by
  let S : Set Real := (fun u : Real => Real.exp (-(b * u)) * f (v - u)) '' Set.Ici 0
  have hne : S.Nonempty :=
    Exists.intro (Real.exp (-(b * 0)) * f (v - 0))
      (Exists.intro 0 (And.intro (Set.mem_Ici.mpr (le_refl (0 : Real))) rfl))
  have hbd : BddAbove S := Exists.intro A (by
    intro y hy
    exact dampedWaveValues_upperBound b A f hb hf v y (Set.mem_insert_iff.mpr (Or.inr hy)))
  apply le_antisymm
  case a =>
    apply csSup_le (dampedWaveValues_nonempty b f v)
    intro y hy
    cases Set.mem_insert_iff.mp hy with
    | inl hz => rw [hz]; exact le_max_left _ _
    | inr hi => exact (le_csSup hbd hi).trans (le_max_right _ _)
  case a =>
    apply max_le (dampedWaveEnvelope_nonneg b A f hb hf v)
    apply csSup_le hne
    intro y hy
    exact le_csSup (dampedWaveValues_bddAbove b A f hb hf v)
      (Set.mem_insert_iff.mpr (Or.inr hy))

end PrimeFactorOscillations.PrimeClassDeletion

/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.DampedWaveRecurrence

/-!
# The strict supremum convention for uniformly almost-periodic waves

The pointwise non-strict epsilon convention is equivalent to the paper's
strict full-line supremum convention. The bounding domain is all reals.
-/

set_option autoImplicit false
set_option Elab.async false

namespace PrimeFactorOscillations.PrimeClassDeletion

theorem uniformWave_difference_range_bddAbove (A : Real) (f : Real -> Real)
    (hf : forall v : Real, abs (f v) <= A) (t : Real) :
    BddAbove (Set.range (fun v : Real => abs (f (v + t) - f v))) := by
  refine Exists.intro (2 * A) ?_
  intro y hy
  choose v hv using hy
  rw [<- hv]
  exact (abs_sub _ _).trans (by linarith only [hf (v + t), hf v])

theorem uniformWave_iff_strict_sup (A : Real) (f : Real -> Real)
    (hf : forall v : Real, abs (f v) <= A) :
    Iff (IsUniformAlmostPeriodicWave f)
      (forall e : Real, 0 < e -> exists L : Real, And (0 < L)
        (forall a : Real, exists t : Real, And (a <= t) (And (t <= a + L)
          (sSup (Set.range (fun v : Real => abs (f (v + t) - f v))) < e)))) := by
  constructor
  case mp =>
    intro hp e he
    choose L hL using hp (e / 2) (by linarith only [he])
    refine Exists.intro L (And.intro hL.1 ?_)
    intro a
    choose t ht using hL.2 a
    refine Exists.intro t (And.intro ht.1 (And.intro ht.2.1 ?_))
    have hsup : sSup (Set.range (fun v : Real => abs (f (v + t) - f v))) <= e / 2 := by
      apply csSup_le (Set.range_nonempty _)
      intro y hy
      choose v hv using hy
      rw [<- hv]
      exact ht.2.2 v
    exact lt_of_le_of_lt hsup (by linarith only [he])
  case mpr =>
    intro hp e he
    choose L hL using hp e he
    refine Exists.intro L (And.intro hL.1 ?_)
    intro a
    choose t ht using hL.2 a
    refine Exists.intro t (And.intro ht.1 (And.intro ht.2.1 ?_))
    intro v
    have hle := le_csSup (uniformWave_difference_range_bddAbove A f hf t)
      (Set.mem_range_self v)
    exact (lt_of_le_of_lt hle ht.2.2).le

end PrimeFactorOscillations.PrimeClassDeletion

/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Mathlib.Analysis.Complex.AnchoredScalarMultiplicity

/-!
# Decoding an integer pair from a bounded one-sided real defect

A coarse rounding step finds the integer level; a finer step then finds the
second integer. No bound on either integer is assumed.
-/

set_option autoImplicit false
set_option Elab.async false

noncomputable section
namespace Real

/-- Center the known one-sided defect interval before rounding. -/
def scalarBudgetInteger (c y : Real) : Int := Int.floor (y + (1 + c) / 2)

/-- After finding the integer level, round the divided defect. -/
def scalarBudgetReference (c delta y : Real) : Int :=
  Int.floor (((scalarBudgetInteger c y : Real) - y) / delta + 1 / 2)

/-- Recover the original pair from one real observation. -/
def scalarBudgetDecode (d : Nat) (c delta y : Real) : Prod Int Int :=
  let b := scalarBudgetReference c delta y
  Prod.mk ((d : Int) * b - scalarBudgetInteger c y) b

theorem scalarBudgetInteger_eq (d : Nat) (a b : Int) (c delta y : Real)
    (hMass : And (0 <= delta * (b : Real)) (delta * (b : Real) <= c))
    (hNoise : abs ((d : Real) * (b : Real) - (a : Real) -
      delta * (b : Real) - y) < (1 - c) / 2) :
    scalarBudgetInteger c y = (d : Int) * b - a := by
  have hn := abs_lt.mp hNoise
  unfold scalarBudgetInteger
  apply Int.floor_eq_iff.mpr
  push_cast
  constructor <;> linarith only [hn.1, hn.2, hMass.1, hMass.2]

theorem scalarBudgetReference_eq (d : Nat) (a b : Int) (c delta y : Real)
    (hDelta : 0 < delta)
    (hMass : And (0 <= delta * (b : Real)) (delta * (b : Real) <= c))
    (hNoise : abs ((d : Real) * (b : Real) - (a : Real) -
      delta * (b : Real) - y) < (1 - c) / 2)
    (hFine : abs ((d : Real) * (b : Real) - (a : Real) -
      delta * (b : Real) - y) < delta / 2) :
    scalarBudgetReference c delta y = b := by
  have hInteger := scalarBudgetInteger_eq d a b c delta y hMass hNoise
  have hn := abs_lt.mp hFine
  unfold scalarBudgetReference
  rw [hInteger]
  push_cast
  let q : Real := ((d : Real) * (b : Real) - (a : Real) - y) / delta
  have hDiv : q * delta = (d : Real) * (b : Real) - (a : Real) - y := by
    dsimp only [q]
    field_simp
  apply Int.floor_eq_iff.mpr
  change And ((b : Real) <= q + 1 / 2) (q + 1 / 2 < (b : Real) + 1)
  constructor
  . by_contra h
    have hh : q + 1 / 2 < (b : Real) := lt_of_not_ge h
    have hm := mul_pos (sub_pos.mpr hh) hDelta
    nlinarith only [hn.1, hDiv, hm]
  . by_contra h
    have hh : (b : Real) + 1 <= q + 1 / 2 := le_of_not_gt h
    have hm := mul_nonneg (sub_nonneg.mpr hh) hDelta.le
    nlinarith only [hn.2, hDiv, hm]

theorem scalarBudgetDecode_eq (d : Nat) (a b : Int) (c delta y : Real)
    (hDelta : 0 < delta)
    (hMass : And (0 <= delta * (b : Real)) (delta * (b : Real) <= c))
    (hNoise : abs ((d : Real) * (b : Real) - (a : Real) -
      delta * (b : Real) - y) < (1 - c) / 2)
    (hFine : abs ((d : Real) * (b : Real) - (a : Real) -
      delta * (b : Real) - y) < delta / 2) :
    scalarBudgetDecode d c delta y = Prod.mk a b := by
  rw [scalarBudgetDecode,
    scalarBudgetReference_eq d a b c delta y hDelta hMass hNoise hFine,
    scalarBudgetInteger_eq d a b c delta y hMass hNoise]
  congr 1
  ring

end Real

/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Assembly.CarmichaelTwoTailSharpness
import PrimeFactorOscillations.Assembly.CarmichaelZetaMinimalCarrier

/-!
# The exact smallest sharp fifth-tail carrier

Seventeen is the minimum support size, and the imported classification lists
every smallest configuration, including both possible central orders.
-/

set_option autoImplicit false
set_option Elab.async false

noncomputable section

namespace PrimeFactorOscillations.CarmichaelDyadicSharpness

def FifthEqualitySupportSize (n : Nat) : Prop :=
  exists S : ReflectedSpectrum (Fin n) (7 / 8),
    S.carrierMass =
      39 * S.weakUnitMass + S.weakRepeatedUnitMass + 4 * S.weakFifthUnitMass /\
    0 < S.weakFifthUnitMass

theorem fifthEqualitySupportSize_isLeast :
    IsLeast {n : Nat | FifthEqualitySupportSize n} 17 := by
  constructor
  . let S := seventeenRootSpectrum 1 (by norm_num) 5 (Or.inl rfl)
    exact Exists.intro S (And.intro
      (seventeenRootSpectrum_fifth_equality 1 (by norm_num) 5 (Or.inl rfl))
      (seventeenRootSpectrum_weakFifthUnitMass_pos 1 (by norm_num) 5 (Or.inl rfl)))
  . intro n hn
    choose S hEq hPos using hn
    have h := S.fifth_equality_card_minimum hEq hPos
    simpa using h

end PrimeFactorOscillations.CarmichaelDyadicSharpness


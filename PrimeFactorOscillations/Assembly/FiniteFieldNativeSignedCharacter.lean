/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Assembly.FiniteFieldNativeSquareCharacter

/-! # Signed integer principal characters and their physical prime-band means

The negative numerator phase is retained. Every integer numerator is fixed
before the independent field-prime scale, and zero is explicitly excluded.
-/

set_option autoImplicit false
set_option Elab.async false

noncomputable section
namespace PrimeFactorOscillations.FiniteFieldIntegerSignature
open Filter IntegerQuadraticCharacter
open FiniteFieldIntegerWindowTransfer

theorem numerator_principal_indicator_int_eq_square (D : Int) (hD : Not (D = 0)) :
    numeratorPrincipalIndicator D = if IsSquare D then (1 : Real) else 0 := by
  classical
  cases D with
  | ofNat n =>
    have hn0 : Not (n = 0) := by
      intro hz
      apply hD
      rw [hz]
      rfl
    have hn : 0 < n := Nat.pos_of_ne_zero hn0
    have hcast : IsSquare (n : Int) <-> IsSquare n := by
      constructor
      . intro h
        cases h with
        | intro k hk =>
          refine Exists.intro k.natAbs ?_
          have hh := congrArg Int.natAbs hk
          simpa only [Int.natAbs_natCast, Int.natAbs_mul] using hh
      . intro h
        cases h with
        | intro k hk =>
          refine Exists.intro (k : Int) ?_
          exact_mod_cast hk
    change numeratorPrincipalIndicator (n : Int) = if IsSquare (n : Int) then (1 : Real) else 0
    simpa only [hcast] using numerator_principal_indicator_nat_eq_square n hn
  | negSucc n =>
    have he : Int.negSucc n = -((n + 1 : Nat) : Int) := by omega
    rw [he] at hD
    rw [he]
    have hchi : Not (numeratorCharacter (-((n + 1 : Nat) : Int)) hD = 1) :=
      negative_numerator_character_ne_one (n + 1) (by omega) hD
    have hnot : Not (IsSquare (-((n + 1 : Nat) : Int))) := by
      intro h
      cases h with
      | intro k hk =>
        have hnon := mul_self_nonneg k
        rw [<- hk] at hnon
        omega
    simp only [numeratorPrincipalIndicator, dite_eq_right hD,
      ite_eq_right hchi, ite_eq_right hnot]

theorem prime_correlation_centered_int_square_tendsto_zero
    (D : Int) (hD : Not (D = 0)) :
    Tendsto (fun U : Nat =>
      primeCorrelation D (preciseCore U + 1) (preciseCore U * preciseCore U + 1) -
        (if IsSquare D then (1 : Real) else 0) *
          reciprocalBand (preciseCore U + 1) (preciseCore U * preciseCore U + 1))
      atTop (nhds 0) := by
  classical
  simpa only [numerator_principal_indicator_int_eq_square D hD] using
    prime_correlation_principal_centered_tendsto_zero D hD

end PrimeFactorOscillations.FiniteFieldIntegerSignature

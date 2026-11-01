/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Assembly.FiniteFieldNativeSignedMoments
import PrimeFactorOscillations.Helpers.NativePrimeUniversalCycles

/-! # General signed native moments before square-mask exclusion

Only the full integer numerator is required to be nonzero. The graph and
all masks stay fixed before the independently varying field-prime scale.
-/

set_option autoImplicit false
set_option Elab.async false

noncomputable section
namespace PrimeFactorOscillations.FiniteFieldIntegerSignature
open Filter IntegerQuadraticCharacter
open FiniteFieldIntegerWindowTransfer

theorem native_signed_row_moment_centered_general (A B : Finset (Prod Nat Nat))
    (hD : Not (nativeSignedRowProduct A B = 0)) :
    Tendsto (fun U : Nat =>
      nativeSignedRowMoment A B (preciseCore U + 1) (preciseCore U * preciseCore U + 1) -
        numeratorPrincipalIndicator (nativeSignedRowProduct A B) *
          reciprocalBand (preciseCore U + 1) (preciseCore U * preciseCore U + 1))
      atTop (nhds 0) := by
  have hlim := prime_correlation_principal_centered_tendsto_zero
    (nativeSignedRowProduct A B) hD
  have htail := precise_core_tendsto_atTop.eventually_ge_atTop 3
  apply hlim.congr'
  filter_upwards [htail] with U hU
  rw [native_signed_row_moment_eq_correlation A B _ _ (by omega)]

theorem native_signed_row_moment_general_ratio_tendsto (A B : Finset (Prod Nat Nat))
    (hD : Not (nativeSignedRowProduct A B = 0)) :
    Tendsto (fun U : Nat =>
      nativeSignedRowMoment A B (preciseCore U + 1) (preciseCore U * preciseCore U + 1) /
        reciprocalBand (preciseCore U + 1) (preciseCore U * preciseCore U + 1))
      atTop (nhds (numeratorPrincipalIndicator (nativeSignedRowProduct A B))) :=
  native_prime_band_ratio_tendsto_of_centered _ _
    (native_signed_row_moment_centered_general A B hD)

end PrimeFactorOscillations.FiniteFieldIntegerSignature

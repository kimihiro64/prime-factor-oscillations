/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.PrimePowerIntrinsicBridge
import PrimeFactorOscillations.Helpers.PrimeSquareConductorShell

/-!
# Complete prime-square classification for the original intrinsic observable

The native signed calculation is transported to the existing rational
residue coefficients. Every frequency and the exceptional prime two are
included; this is not a replacement observable.
-/

set_option autoImplicit false
set_option Elab.async false

noncomputable section

namespace PrimeFactorOscillations.PrimePowerReturnSpectrum

open CarmichaelCarrierReadout ModularReturnFourier

theorem intrinsic_prime_square_formula (p h : Nat) [NeZero p] (hp : Nat.Prime p) :
    residueFourier (p ^ 2) (centeredPower (p ^ 2) p) h =
      if Dvd.dvd (p ^ 2) h then 0
      else if Dvd.dvd p h then
        (p : Complex) ^ 2 *
          (((p - 1 : Nat) : Complex) * ZMod.stdAddChar (h : ZMod (p ^ 2)) + 1)
      else 0 := by
  rw [intrinsic_eq_native]
  exact prime_square_centered_formula p h hp

theorem prime_square_conductor_shell (p h : Nat) [NeZero p] (hp : Nat.Prime p) :
    Not (residueFourier (p ^ 2) (centeredPower (p ^ 2) p) h = 0) <->
      And (Not (p = 2)) (And (Dvd.dvd p h) (Not (Dvd.dvd (p ^ 2) h))) := by
  rw [intrinsic_eq_native]
  exact prime_square_centered_all_primes p h hp

theorem prime_square_odd_conductor_shell (p h : Nat) [NeZero p]
    (hp : Nat.Prime p) (hp2 : Not (p = 2)) :
    Not (residueFourier (p ^ 2) (centeredPower (p ^ 2) p) h = 0) <->
      And (Dvd.dvd p h) (Not (Dvd.dvd (p ^ 2) h)) := by
  rw [intrinsic_eq_native]
  exact prime_square_centered_nonzero_iff p h hp hp2

theorem prime_square_intrinsic_zero_iff (p h : Nat) [NeZero p] (hp : Nat.Prime p) :
    residueFourier (p ^ 2) (centeredPower (p ^ 2) p) h = 0 <->
      Or (p = 2) (Or (Not (Dvd.dvd p h)) (Dvd.dvd (p ^ 2) h)) := by
  classical
  simpa only [not_not, not_and_or] using
    (not_congr (prime_square_conductor_shell p h hp))

end PrimeFactorOscillations.PrimePowerReturnSpectrum

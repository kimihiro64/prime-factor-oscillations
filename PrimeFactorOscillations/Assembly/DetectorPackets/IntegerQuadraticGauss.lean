/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/

import Mathlib.NumberTheory.GaussSum
import PrimeFactorOscillations.Assembly.DetectorPackets.IntegerQuadraticCharacter

/-!
# IntegerQuadraticGauss

Maintained extraction of completed detector/packet proof components.
All original theorem hypotheses and retained proof bodies are preserved.
This module alone asserts no improved zero-free boundary.
-/

set_option autoImplicit false
set_option Elab.async false

/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/

/-!
# Prime local Fourier transforms of the actual integer Jacobi character

The zero frequency is retained. The Gauss sum has its raw square-root
normalization; no conductor saving or global large sieve is assumed.
-/


noncomputable section
open scoped BigOperators
namespace PrimeFactorOscillations.IntegerQuadraticGauss

open QuadraticCarrierPacket IntegerQuadraticCharacter

theorem character_quadratic (n : Nat) (hn : 1 < n) :
    (character n hn).IsQuadratic := by
  intro x
  rcases jacobiSym.trichotomy (x.val : Int) n with h | h | h
  . exact Or.inl (by simp [character_apply, kernel, h])
  . exact Or.inr (Or.inl (by simp [character_apply, kernel, h]))
  . exact Or.inr (Or.inr (by simp [character_apply, kernel, h]))

theorem prime_fourier_factor (p : Nat) [hp : Fact (Nat.Prime p)]
    (hp2 : Not (p = 2)) (psi : AddChar (ZMod p) Complex) (k : ZMod p) :
    gaussSum (character p hp.out.one_lt) (psi.mulShift k) =
      character p hp.out.one_lt k * gaussSum (character p hp.out.one_lt) psi := by
  have hchi := prime_character_ne_one p hp.out hp2
  have hinv := (character_quadratic p hp.out.one_lt).inv
  by_cases hk : k = 0
  . subst k
    have hshift : psi.mulShift 0 = 1 := by
      ext x
      simp [AddChar.mulShift_apply]
    rw [hshift, gaussSum_one_right hchi]
    have hz : character p hp.out.one_lt 0 = 0 := by
      rw [character_apply]
      simp only [ZMod.val_zero, kernel, Nat.cast_zero,
        jacobiSym.zero_left hp.out.one_lt, Int.cast_zero]
    rw [hz, zero_mul]
  . let u : Units (ZMod p) := Units.mk0 k hk
    have h := gaussSum_mulShift_eq (character p hp.out.one_lt) psi u
    rw [hinv] at h
    simpa only [u, Units.val_mk0] using h

theorem prime_gauss_norm_sq (p : Nat) [hp : Fact (Nat.Prime p)]
    (hp2 : Not (p = 2)) (psi : AddChar (ZMod p) Complex)
    (hpsi : psi.IsPrimitive) :
    norm (gaussSum (character p hp.out.one_lt) psi) ^ 2 = (p : Real) := by
  have hprod := gaussSum_mul_gaussSum_eq_card
    (prime_character_ne_one p hp.out hp2) hpsi
  rw [<- star_gaussSum_eq] at hprod
  have hre := congrArg Complex.re hprod
  simpa [Complex.mul_conj, Complex.normSq_eq_norm_sq, pow_two,
    Complex.mul_re] using hre

theorem prime_gauss_norm (p : Nat) [hp : Fact (Nat.Prime p)]
    (hp2 : Not (p = 2)) (psi : AddChar (ZMod p) Complex)
    (hpsi : psi.IsPrimitive) :
    norm (gaussSum (character p hp.out.one_lt) psi) = Real.sqrt p := by
  have h := prime_gauss_norm_sq p hp2 psi hpsi
  have hs := Real.sq_sqrt (show (0 : Real) <= (p : Real) from Nat.cast_nonneg p)
  have hn := norm_nonneg (gaussSum (character p hp.out.one_lt) psi)
  have hr := Real.sqrt_nonneg (p : Real)
  nlinarith

end PrimeFactorOscillations.IntegerQuadraticGauss

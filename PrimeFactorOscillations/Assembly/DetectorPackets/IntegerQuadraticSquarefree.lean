/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/

import Mathlib.Data.Nat.Squarefree
import PrimeFactorOscillations.Assembly.DetectorPackets.IntegerQuadraticCRT

/-!
# IntegerQuadraticSquarefree

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
# All-frequency Jacobi transforms at every odd squarefree modulus

Strong induction assembles the proved prime transforms by CRT. No
large-sieve or zero-free-region hypothesis occurs in these statements.
-/


noncomputable section
namespace PrimeFactorOscillations.IntegerQuadraticSquarefree

open IntegerQuadraticCharacter IntegerQuadraticGauss IntegerQuadraticCRT

def FourierData (n : Nat) : Prop :=
  forall (hn : 1 < n),
    letI : NeZero n := NeZero.mk (by omega);
    (forall (psi : AddChar (ZMod n) Complex) (k : ZMod n),
      gaussSum (character n hn) (psi.mulShift k) =
        character n hn k * gaussSum (character n hn) psi) /\
    (forall psi : AddChar (ZMod n) Complex, psi.IsPrimitive ->
      norm (gaussSum (character n hn) psi) ^ 2 = (n : Real))

theorem squarefree_data :
    forall n : Nat, Odd n -> Squarefree n -> FourierData n := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro hodd hsf hn
    letI : NeZero n := NeZero.mk (by omega)
    choose p hp using Nat.exists_prime_and_dvd (by omega : Not (n = 1))
    choose m hm using hp.2
    have hpm : Squarefree (p * m) := by
      rw [<- hm]
      exact hsf
    have hsfparts := Nat.squarefree_mul_iff.mp hpm
    have hoddpm : Odd (p * m) := by
      rw [<- hm]
      exact hodd
    have hoddparts := Nat.odd_mul.mp hoddpm
    have hp2 : Not (p = 2) := by
      intro hz
      have hodd2 : Odd (2 : Nat) := by simpa only [hz] using hoddparts.1
      have hmod := Nat.odd_iff.mp hodd2
      norm_num at hmod
    letI : Fact (Nat.Prime p) := Fact.mk hp.1
    by_cases hm1 : m = 1
    . subst m
      simp only [Nat.mul_one] at hm
      subst n
      exact And.intro
        (fun psi k => prime_fourier_factor p hp2 psi k)
        (fun psi hpsi => prime_gauss_norm_sq p hp2 psi hpsi)
    . have hm0 : Not (m = 0) := by
        intro hz
        rw [hz, Nat.mul_zero] at hm
        omega
      have hmgt : 1 < m := by omega
      have hmlt : m < n := by
        have hmul := Nat.mul_le_mul_right m hp.1.two_le
        nlinarith
      letI : NeZero m := NeZero.mk hm0
      have hdm := ih m hmlt hoddparts.2 hsfparts.2.2 hmgt
      subst n
      exact And.intro
        (fourier_factor_mul hp.1.one_lt hmgt hsfparts.1
          (fun psi k => prime_fourier_factor p hp2 psi k) hdm.1)
        (gauss_norm_sq_mul hp.1.one_lt hmgt hsfparts.1
          (fun psi hpsi => prime_gauss_norm_sq p hp2 psi hpsi) hdm.2)

theorem squarefree_fourier_factor (n : Nat) [NeZero n]
    (hn : 1 < n) (hodd : Odd n) (hsf : Squarefree n)
    (psi : AddChar (ZMod n) Complex) (k : ZMod n) :
    gaussSum (character n hn) (psi.mulShift k) =
      character n hn k * gaussSum (character n hn) psi :=
  (squarefree_data n hodd hsf hn).1 psi k

theorem squarefree_gauss_norm_sq (n : Nat) [NeZero n]
    (hn : 1 < n) (hodd : Odd n) (hsf : Squarefree n)
    (psi : AddChar (ZMod n) Complex) (hpsi : psi.IsPrimitive) :
    norm (gaussSum (character n hn) psi) ^ 2 = (n : Real) :=
  (squarefree_data n hodd hsf hn).2 psi hpsi

theorem squarefree_gauss_norm (n : Nat) [NeZero n]
    (hn : 1 < n) (hodd : Odd n) (hsf : Squarefree n)
    (psi : AddChar (ZMod n) Complex) (hpsi : psi.IsPrimitive) :
    norm (gaussSum (character n hn) psi) = Real.sqrt n := by
  have h := squarefree_gauss_norm_sq n hn hodd hsf psi hpsi
  have hs := Real.sq_sqrt (show (0 : Real) <= (n : Real) from Nat.cast_nonneg n)
  have hg := norm_nonneg (gaussSum (character n hn) psi)
  have hr := Real.sqrt_nonneg (n : Real)
  nlinarith

end PrimeFactorOscillations.IntegerQuadraticSquarefree
